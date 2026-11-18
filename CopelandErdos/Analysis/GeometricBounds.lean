module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Sums of exponentially growing terms with a quadratic denominator

For `b > 1`, the partial sum of `b^n / n²` is bounded by a constant multiple of its
last term. After dividing by that last term and reversing the index, the summands
are bounded by `(j + 1)² * (b⁻¹)^j`, a summable polynomial times a geometric sequence.
-/

public section

open Filter
open scoped BigOperators

namespace CopelandErdos.Analysis

private theorem summable_add_one_sq_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ 2 * r ^ n) := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_lt_one hr0 hr1
  convert (h2.add (h1.mul_left 2)).add h0 using 1
  funext n
  ring

private theorem geometric_div_sq_term_le {b : ℝ} (hb : 1 < b) {n L : ℕ}
    (hn : 1 ≤ n) (hnL : n ≤ L) :
    b ^ n / (n : ℝ) ^ 2 ≤
      (b ^ L / (L : ℝ) ^ 2) * (((L - n : ℕ) : ℝ) + 1) ^ 2 *
        (b⁻¹) ^ (L - n) := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le hn0 (by exact_mod_cast hnL)
  have hcast : (L : ℝ) = (n : ℝ) + ((L - n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_sub_of_le hnL).symm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ (L - n : ℕ) := Nat.cast_nonneg _
  have hscale : (L : ℝ) ≤ (n : ℝ) * (((L - n : ℕ) : ℝ) + 1) := by
    nlinarith
  have hsq : (L : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * (((L - n : ℕ) : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) * (((L - n : ℕ) : ℝ) + 1) - L)]
  have hpow : b ^ L * (b⁻¹) ^ (L - n) = b ^ n := by
    rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hb0.ne')]
    rw [← pow_add, Nat.add_sub_of_le hnL]
  calc
    b ^ n / (n : ℝ) ^ 2 ≤
        b ^ n * (((L - n : ℕ) : ℝ) + 1) ^ 2 / (L : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hn0) (sq_pos_of_pos hL0)).2
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hsq (pow_nonneg hb0.le n)
    _ = (b ^ L / (L : ℝ) ^ 2) * (((L - n : ℕ) : ℝ) + 1) ^ 2 *
        (b⁻¹) ^ (L - n) := by rw [← hpow]; ring

/-- The sum of `b^n / n²` up to `L` is bounded by a constant multiple of its final term. -/
theorem exists_pos_sum_geometric_div_sq_le (b : ℝ) (hb : 1 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L →
      (∑ n ∈ Finset.Icc 1 L, b ^ n / (n : ℝ) ^ 2) ≤ C * b ^ L / (L : ℝ) ^ 2 := by
  let f : ℕ → ℝ := fun j ↦ ((j : ℝ) + 1) ^ 2 * (b⁻¹) ^ j
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hf0 : ∀ j, 0 ≤ f j := by intro j; dsimp [f]; positivity
  have hfs : Summable f := summable_add_one_sq_mul_pow (inv_nonneg.mpr hb0.le)
    (inv_lt_one_of_one_lt₀ hb)
  have hsum0 : 0 ≤ ∑' j, f j := tsum_nonneg hf0
  refine ⟨(∑' j, f j) + 1, by linarith, ?_⟩
  intro L hL
  have hratio :
      (∑ n ∈ Finset.Icc 1 L, f (L - n)) ≤ ∑' j, f j := by
    have hinj : Set.InjOn (fun n : ℕ ↦ L - n) (Finset.Icc 1 L) := by
      intro n hn m hm heq
      simp only [Finset.mem_coe, Finset.mem_Icc] at hn hm
      change L - n = L - m at heq
      omega
    rw [← Finset.sum_image hinj]
    exact hfs.sum_le_tsum _ (fun j _ ↦ hf0 j)
  calc
    (∑ n ∈ Finset.Icc 1 L, b ^ n / (n : ℝ) ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 L, (b ^ L / (L : ℝ) ^ 2) * f (L - n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      simpa [f, mul_assoc] using geometric_div_sq_term_le hb hn'.1 hn'.2
    _ = (b ^ L / (L : ℝ) ^ 2) * (∑ n ∈ Finset.Icc 1 L, f (L - n)) := by
      rw [Finset.mul_sum]
    _ ≤ (b ^ L / (L : ℝ) ^ 2) * (∑' j, f j) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ ((∑' j, f j) + 1) * b ^ L / (L : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ b ^ L / (L : ℝ) ^ 2 := by positivity
      calc
        _ = (∑' j, f j) * (b ^ L / (L : ℝ) ^ 2) := by ring
        _ ≤ ((∑' j, f j) + 1) * (b ^ L / (L : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hnonneg
        _ = _ := by ring

/-- Transfer the quadratic-denominator geometric bound to any pointwise dominated sequence. -/
theorem exists_pos_sum_le_geometric_div_sq {a : ℕ → ℝ} {b K : ℝ} (hb : 1 < b)
    (hK : 0 ≤ K) (ha : ∀ n : ℕ, 1 ≤ n → a n ≤ K * b ^ n / (n : ℝ) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L →
      (∑ n ∈ Finset.Icc 1 L, a n) ≤ C * b ^ L / (L : ℝ) ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := exists_pos_sum_geometric_div_sq_le b hb
  refine ⟨K * D + 1, by positivity, ?_⟩
  intro L hL
  calc
    (∑ n ∈ Finset.Icc 1 L, a n) ≤
        ∑ n ∈ Finset.Icc 1 L, K * (b ^ n / (n : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa [mul_div_assoc] using ha n (Finset.mem_Icc.mp hn).1
    _ = K * (∑ n ∈ Finset.Icc 1 L, b ^ n / (n : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ K * (D * b ^ L / (L : ℝ) ^ 2) := mul_le_mul_of_nonneg_left (hbound L hL) hK
    _ ≤ (K * D + 1) * b ^ L / (L : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ b ^ L / (L : ℝ) ^ 2 := by positivity
      calc
        _ = (K * D) * (b ^ L / (L : ℝ) ^ 2) := by ring
        _ ≤ (K * D + 1) * (b ^ L / (L : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hnonneg
        _ = _ := by ring

/-- An eventual form convenient for asymptotic applications. -/
theorem exists_pos_eventually_sum_le_geometric_div_sq {a : ℕ → ℝ} {b K : ℝ}
    (hb : 1 < b) (hK : 0 ≤ K)
    (ha : ∀ n : ℕ, 1 ≤ n → a n ≤ K * b ^ n / (n : ℝ) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℕ in atTop,
      (∑ n ∈ Finset.Icc 1 L, a n) ≤ C * b ^ L / (L : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_sum_le_geometric_div_sq hb hK ha
  exact ⟨C, hC, (eventually_ge_atTop 1).mono fun L hL ↦ hbound L hL⟩

end CopelandErdos.Analysis
