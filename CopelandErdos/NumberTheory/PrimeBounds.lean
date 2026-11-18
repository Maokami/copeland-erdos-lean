module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Elementary bounds for the prime stream

Chebyshev's explicit lower bound yields a positive constant multiple of `n / log n`
eventually. Bertrand's postulate bounds consecutive primes, including the concrete sequence
`Nat.nth Nat.Prime` used to enumerate the prime digit blocks.
-/

public section

open Filter

namespace CopelandErdos.NumberTheory

/-- The positive constant retained from Chebyshev's explicit prime-counting lower bound. -/
noncomputable def primeCountingLowerConstant : ℝ := Real.log 2 / 2

theorem primeCountingLowerConstant_pos : 0 < primeCountingLowerConstant := by
  unfold primeCountingLowerConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- The logarithmic correction in Chebyshev's bound is eventually at most half its main term. -/
theorem eventually_log_add_one_le_half_log_two_mul :
    ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) + 1) ≤ (Real.log 2 / 2) * n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hsmall := hshift.eventually
    (Real.isLittleO_log_id_atTop.def (show 0 < Real.log 2 / 4 by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity), id_eq] at hn
  nlinarith

/-- An unconditional Chebyshev lower bound with the explicit positive constant `log 2 / 2`.
The proof restricts to `n > 1`, so the denominator is positive. -/
theorem eventually_primeCounting_ge :
    ∀ᶠ n : ℕ in atTop,
      (Real.log 2 / 2) * (n : ℝ) / Real.log n ≤ (Nat.primeCounting n : ℝ) := by
  filter_upwards [eventually_log_add_one_le_half_log_two_mul, eventually_gt_atTop 1]
    with n hcorrection hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn'
  refine le_trans (div_le_div_of_nonneg_right ?_ hlog.le) (Chebyshev.pi_ge n)
  nlinarith

/-- A constant-form interface for later estimates on the total prime digit mass. -/
theorem exists_pos_eventually_primeCounting_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) / Real.log n ≤ (Nat.primeCounting n : ℝ) := by
  exact ⟨primeCountingLowerConstant, primeCountingLowerConstant_pos,
    eventually_primeCounting_ge⟩

/-- Bertrand's bound for two primes with no prime strictly between them. -/
theorem consecutive_prime_le_two_mul {p q : ℕ} (hp : Nat.Prime p) (_hq : Nat.Prime q)
    (_hpq : p < q) (hgap : ∀ r : ℕ, p < r → r < q → ¬ Nat.Prime r) : q ≤ 2 * p := by
  obtain ⟨r, hr, hpr, hrp⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  have hqr : q ≤ r := le_of_not_gt (fun hrq ↦ hgap r hpr hrq hr)
  exact hqr.trans hrp

/-- Successive entries of the increasing enumeration of primes satisfy Bertrand's bound. -/
theorem nth_prime_succ_le_two_mul (n : ℕ) :
    Nat.nth Nat.Prime (n + 1) ≤ 2 * Nat.nth Nat.Prime n := by
  apply consecutive_prime_le_two_mul (Nat.prime_nth_prime n) (Nat.prime_nth_prime (n + 1))
    ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.lt_succ_self n))
  intro r hnr hrn hr
  exact (not_le_of_gt hnr) (Nat.le_nth_of_lt_nth_succ hrn hr)

end CopelandErdos.NumberTheory
