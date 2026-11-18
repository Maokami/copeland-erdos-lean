module

public import CopelandErdos.Words.BlockCounts
public import CopelandErdos.Words.BadWordArithmetic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# A quadratic bound for exceptional finite words

The exceptional set uses the overlapping occurrence count and the full word length as
denominator. Its bound is obtained from residue groups in the actual uniform word space.
-/

@[expose] public section

open scoped BigOperators
open Finset
open CopelandErdos.Probability

namespace CopelandErdos.Words

variable {b k ℓ : ℕ}

/-- Words whose frequency of the fixed pattern differs from its uniform frequency by
more than `ε`. All words, including words with leading zeroes, are included. -/
noncomputable def badWords (w : Fin k → Fin b) (ε : ℝ) (ℓ : ℕ) :
    Finset (Fin ℓ → Fin b) :=
  Finset.univ.filter (fun u ↦
    ε < |(occurrenceCount (List.ofFn w) (List.ofFn u) : ℝ) / (ℓ : ℝ) -
      1 / (b : ℝ) ^ k|)

/-- The exceptional event for a single residue group, measured on the full word space. -/
noncomputable def residueBadWords (hk : 0 < k) (w : Fin k → Fin b) (τ : ℝ)
    (r : Fin k) (ℓ : ℕ) : Finset (Fin ℓ → Fin b) :=
  Finset.univ.filter (fun u ↦ τ < |residueDeviation hk w u r|)

theorem card_fin_words_cast (b n : ℕ) :
    (Fintype.card (Fin n → Fin b) : ℝ) = (b : ℝ) ^ n := by
  simp

theorem sum_residueDeviation_fin (hk : 0 < k) (hℓ : k ≤ ℓ)
    (w : Fin k → Fin b) (u : Fin ℓ → Fin b) :
    ∑ r, residueDeviation hk w u r =
      (occurrenceCount (List.ofFn w) (List.ofFn u) : ℝ) -
        (1 / (b : ℝ) ^ k) * ((ℓ : ℝ) - ((k : ℝ) - 1)) := by
  have hcount : (∑ r, (residueCount hk w u r : ℝ)) =
      (occurrenceCount (List.ofFn w) (List.ofFn u) : ℝ) := by
    exact_mod_cast (occurrenceCount_eq_sum_residueCount hk hℓ w u).symm
  have hmult : (∑ r : Fin k, (blockMultiplicity ℓ k r : ℝ)) =
      (ℓ : ℝ) - ((k : ℝ) - 1) := by
    rw [← Nat.cast_sum, sum_blockMultiplicity hk hℓ]
    rw [Nat.cast_add, Nat.cast_sub hℓ, Nat.cast_one]
    ring
  simp only [residueDeviation, Finset.sum_sub_distrib, ← Finset.sum_div,
    hcount, hmult, card_fin_words_cast]
  ring

/-- Large total frequency error forces a large error in one residue group. -/
theorem badWords_subset_residue_union (hb : 2 ≤ b) (hk : 0 < k)
    (hℓ : k ≤ ℓ) (hℓpos : 0 < ℓ) (w : Fin k → Fin b) (ε : ℝ)
    (hmargin : 2 * ((k : ℝ) - 1) ≤ ε * (ℓ : ℝ)) :
    badWords w ε ℓ ⊆ Finset.univ.biUnion
      (fun r : Fin k ↦ residueBadWords hk w (ε * (ℓ : ℝ) / (2 * (k : ℝ))) r ℓ) := by
  classical
  intro u hu
  simp only [badWords, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    residueBadWords, Finset.mem_filter]
  by_contra h
  have hbound (r : Fin k) :
      |residueDeviation hk w u r| ≤ ε * (ℓ : ℝ) / (2 * (k : ℝ)) := by
    have hn : ¬ ε * (ℓ : ℝ) / (2 * (k : ℝ)) < |residueDeviation hk w u r| := by
      intro hr
      exact h ⟨r, hr⟩
    exact le_of_not_gt hn
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hℓR : 0 < (ℓ : ℝ) := by exact_mod_cast hℓpos
  have hbR : (1 : ℝ) ≤ (b : ℝ) ^ k := by
    exact one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ b))
  have hp1 : (1 : ℝ) / (b : ℝ) ^ k ≤ 1 := (div_le_one (by positivity)).2 hbR
  have hq : 0 ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have he := abs_frequency_sub_le_of_residue_bounds
    (occurrenceCount (List.ofFn w) (List.ofFn u)) (1 / (b : ℝ) ^ k)
    (ℓ : ℝ) ((k : ℝ) - 1) (ε * (ℓ : ℝ) / (2 * (k : ℝ)))
    (fun r ↦ residueDeviation hk w u r) hℓR (by positivity) hp1 hq
    (sum_residueDeviation_fin hk hℓ w u) hbound
  have ht := residue_threshold_error_le (k : ℝ) (ℓ : ℝ) ε ((k : ℝ) - 1)
    hkR hℓR hmargin
  exact (not_lt_of_ge (he.trans ht)) hu

/-- Finite Markov bound for one group, with the moment taken on all length-`ℓ` words. -/
theorem residueBadWords_ratio_le (hb : 0 < b) (hk : 0 < k) (w : Fin k → Fin b)
    (τ : ℝ) (hτ : 0 < τ) (r : Fin k) :
    ((residueBadWords hk w τ r ℓ).card : ℝ) / (b : ℝ) ^ ℓ ≤
      3 * (ℓ : ℝ) ^ 2 / τ ^ 4 := by
  classical
  let : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  have ht : 0 < τ ^ 4 := by positivity
  have hmoment : uniformMean (fun u : Fin ℓ → Fin b ↦ residueDeviation hk w u r ^ 4) ≤
      3 * (ℓ : ℝ) ^ 2 := by
    apply (mean_residueDeviation_fourth_le hk w r).trans
    have hm : (blockMultiplicity ℓ k r : ℝ) ≤ (ℓ : ℝ) := by
      exact_mod_cast (blockMultiplicity_le (ℓ := ℓ) r)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm 2) (by positivity)
  rw [← card_fin_words_cast]
  calc
    _ ≤ uniformMean (fun u : Fin ℓ → Fin b ↦ residueDeviation hk w u r ^ 4) / τ ^ 4 := by
      apply uniformMean_card_le (fun u ↦ residueDeviation hk w u r ^ 4)
        (fun _ ↦ by positivity) _ _ ht
      intro u hu
      have hu' := (Finset.mem_filter.1 hu).2.le
      have hp := pow_le_pow_left₀ hτ.le hu' 4
      simpa only [(by decide : Even 4).pow_abs] using hp
    _ ≤ 3 * (ℓ : ℝ) ^ 2 / τ ^ 4 := div_le_div_of_nonneg_right hmoment ht.le

/-- The explicit coarse bound after the word is long enough to absorb the boundary error. -/
theorem badWords_card_le_of_large (hb : 2 ≤ b) (hk : 0 < k) (w : Fin k → Fin b)
    (ε : ℝ) (hε : 0 < ε) (hℓ : k ≤ ℓ)
    (hmargin : 2 * ((k : ℝ) - 1) ≤ ε * (ℓ : ℝ)) :
    ((badWords w ε ℓ).card : ℝ) ≤
      (48 * (k : ℝ) ^ 5 / ε ^ 4) * (b : ℝ) ^ ℓ / (ℓ : ℝ) ^ 2 := by
  classical
  have hℓpos : 0 < ℓ := hk.trans_le hℓ
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hℓR : 0 < (ℓ : ℝ) := by exact_mod_cast hℓpos
  have hbpos : 0 < b := by omega
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hbpos
  let τ : ℝ := ε * (ℓ : ℝ) / (2 * (k : ℝ))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let s : Fin k → Finset (Fin ℓ → Fin b) := fun r ↦ residueBadWords hk w τ r ℓ
  have hcard : (badWords w ε ℓ).card ≤ ∑ r, (s r).card := by
    apply (Finset.card_le_card (badWords_subset_residue_union hb hk hℓ hℓpos w ε
      hmargin)).trans
    exact Finset.card_biUnion_le
  have hratio : ((badWords w ε ℓ).card : ℝ) / (b : ℝ) ^ ℓ ≤
      48 * (k : ℝ) ^ 5 / (ε ^ 4 * (ℓ : ℝ) ^ 2) := by
    calc
      _ ≤ (∑ r, ((s r).card : ℝ)) / (b : ℝ) ^ ℓ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
      _ = ∑ r, ((s r).card : ℝ) / (b : ℝ) ^ ℓ := Finset.sum_div _ _ _
      _ ≤ ∑ _r : Fin k, 3 * (ℓ : ℝ) ^ 2 / τ ^ 4 := by
        apply Finset.sum_le_sum
        intro r _
        exact residueBadWords_ratio_le hbpos hk w τ hτ r
      _ = (k : ℝ) * (3 * (ℓ : ℝ) ^ 2 / τ ^ 4) := by simp
      _ = 48 * (k : ℝ) ^ 5 / (ε ^ 4 * (ℓ : ℝ) ^ 2) :=
        residue_tail_factor (k : ℝ) (ℓ : ℝ) ε hkR.ne' hℓR.ne' hε.ne'
  calc
    _ ≤ (48 * (k : ℝ) ^ 5 / (ε ^ 4 * (ℓ : ℝ) ^ 2)) * (b : ℝ) ^ ℓ :=
      (div_le_iff₀ (by positivity)).1 hratio
    _ = _ := by ring

/-- For every fixed nonempty pattern and every positive tolerance, the number of bad
length-`ℓ` words is at most `K b^ℓ / ℓ²`, for every positive `ℓ`. -/
theorem exists_badWords_card_le (hb : 2 ≤ b) (hk : 1 ≤ k) (w : Fin k → Fin b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
      ((badWords w ε ℓ).card : ℝ) ≤ K * (b : ℝ) ^ ℓ / (ℓ : ℝ) ^ 2 := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_ge (2 * ((k : ℝ) - 1) / ε)
  let N : ℕ := max k n
  let A : ℝ := 48 * (k : ℝ) ^ 5 / ε ^ 4
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hNk : k ≤ N := le_max_left _ _
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_max_right k n)
  have hNmargin : 2 * ((k : ℝ) - 1) ≤ ε * (N : ℝ) := by
    have h := (div_le_iff₀ hε).1 (hn.trans hnN)
    nlinarith
  refine ⟨A + (N : ℝ) ^ 2 + 1, by positivity, ?_⟩
  intro ℓ hℓ
  have hℓR : 0 < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hbR : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  by_cases hlarge : N ≤ ℓ
  · have hmargin : 2 * ((k : ℝ) - 1) ≤ ε * (ℓ : ℝ) := by
      apply hNmargin.trans
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlarge) hε.le
    apply (badWords_card_le_of_large hb (by omega) w ε hε (hNk.trans hlarge) hmargin).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp [A]
    nlinarith [sq_nonneg (N : ℝ)]
  · have hsmall : (ℓ : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (le_of_lt (lt_of_not_ge hlarge))
    have hsq : (ℓ : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
      pow_le_pow_left₀ hℓR.le hsmall 2
    have hcard : ((badWords w ε ℓ).card : ℝ) ≤ (b : ℝ) ^ ℓ := by
      rw [← card_fin_words_cast]
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _))
    apply hcard.trans
    apply (le_div_iff₀ (by positivity : 0 < (ℓ : ℝ) ^ 2)).2
    have hcoef : (ℓ : ℝ) ^ 2 ≤ A + (N : ℝ) ^ 2 + 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (b : ℝ) ^ ℓ)]

end CopelandErdos.Words
