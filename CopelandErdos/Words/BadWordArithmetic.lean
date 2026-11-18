module

public import CopelandErdos.Probability.FiniteMoments
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! Scalar estimates for combining residue-group deviations. -/

@[expose] public section

open scoped BigOperators
open Finset

namespace CopelandErdos.Words

variable {k : ℕ}

/-- The deterministic scalar estimate used to combine residue-group errors. -/
theorem abs_frequency_sub_le_of_residue_bounds
    (c p L q τ : ℝ) (x : Fin k → ℝ) (hL : 0 < L) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hsum : ∑ r, x r = c - p * (L - q))
    (hbound : ∀ r, |x r| ≤ τ) :
    |c / L - p| ≤ ((k : ℝ) * τ + q) / L := by
  have hsumabs : |∑ r, x r| ≤ (k : ℝ) * τ := by
    calc
      _ ≤ ∑ r, |x r| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin k, τ := Finset.sum_le_sum (fun r _ ↦ hbound r)
      _ = (k : ℝ) * τ := by simp
  have htriangle : |c - p * L| ≤ (k : ℝ) * τ + q := by
    calc
      _ = |(∑ r, x r) - p * q| := by rw [hsum]; congr 1; ring
      _ ≤ |∑ r, x r| + |p * q| := abs_sub _ _
      _ = |∑ r, x r| + p * q := by rw [abs_of_nonneg (mul_nonneg hp hq)]
      _ ≤ (k : ℝ) * τ + q := by nlinarith
  calc
    _ = |c - p * L| / L := by
      rw [show c / L - p = (c - p * L) / L by field_simp, abs_div, abs_of_pos hL]
    _ ≤ ((k : ℝ) * τ + q) / L := div_le_div_of_nonneg_right htriangle hL.le

theorem residue_threshold_error_le (K L ε q : ℝ) (hK : 0 < K) (hL : 0 < L)
    (hmargin : 2 * q ≤ ε * L) :
    (K * (ε * L / (2 * K)) + q) / L ≤ ε := by
  have hcancel : K * (ε * L / (2 * K)) = ε * L / 2 := by
    field_simp [hK.ne']
  rw [hcancel]
  apply (div_le_iff₀ hL).2
  linarith

theorem residue_tail_factor (K L ε : ℝ) (hK : K ≠ 0) (hL : L ≠ 0) (hε : ε ≠ 0) :
    K * (3 * L ^ 2 / (ε * L / (2 * K)) ^ 4) =
      48 * K ^ 5 / (ε ^ 4 * L ^ 2) := by
  field_simp [hK, hL, hε]
  ring

end CopelandErdos.Words
