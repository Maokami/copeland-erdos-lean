module

public import CopelandErdos.Digits.NatWord
public import CopelandErdos.NumberTheory.PrimeBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp

/-!
# Total digit mass of the primes

The sum of the base-`b` digit lengths of the primes up to `X` grows at least linearly
in `X`. The proof compares the digit mass with Chebyshev's `theta` function and uses
its elementary lower bound. Chebyshev's upper bound for prime counting then shows
that the number of prime blocks divided by their digit mass tends to zero.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace CopelandErdos.NumberTheory

/-- Total base-`b` digit length of all primes at most `X`, with an inclusive cutoff. -/
noncomputable def primeDigitMass (b : ℕ) (hb : 1 < b) (X : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE X, (Digits.natWord b hb p).length

/-- The logarithm of a positive integer is at most its digit length times `log b`. -/
theorem log_le_length_natWord_mul_log (b : ℕ) (hb : 1 < b) (p : ℕ) (hp : 0 < p) :
    Real.log (p : ℝ) ≤ ((Digits.natWord b hb p).length : ℝ) * Real.log b := by
  have hpow : p < b ^ (Digits.natWord b hb p).length := by
    rw [Digits.length_natWord_eq_log_add_one b hb p hp.ne']
    exact Nat.lt_pow_succ_log_self hb p
  have hpow' : (p : ℝ) ≤ (b : ℝ) ^ (Digits.natWord b hb p).length := by
    exact_mod_cast hpow.le
  calc
    Real.log (p : ℝ) ≤ Real.log ((b : ℝ) ^ (Digits.natWord b hb p).length) :=
      Real.log_le_log (by exact_mod_cast hp) hpow'
    _ = _ := Real.log_pow _ _

/-- Chebyshev's `theta` function is bounded above by the prime digit mass times `log b`. -/
theorem theta_le_primeDigitMass_mul_log (b : ℕ) (hb : 1 < b) (X : ℕ) :
    Chebyshev.theta X ≤ (primeDigitMass b hb X : ℝ) * Real.log b := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, primeDigitMass, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  exact log_le_length_natWord_mul_log b hb p (Nat.prime_of_mem_primesLE hp).pos

/-- Chebyshev's explicit error terms are eventually at most half of the linear main term. -/
theorem eventually_theta_ge_half_log_two_mul :
    ∀ᶠ X : ℕ in atTop, (Real.log 2 / 2) * (X : ℝ) ≤ Chebyshev.theta X := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hshift : Tendsto (fun X : ℕ ↦ (X : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hsmall := hshift.eventually
    (Real.isLittleO_log_id_atTop.def (show 0 < Real.log 2 / 8 by positivity))
  have hsqrt := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).def
      (show 0 < Real.log 2 / 8 by positivity))
  filter_upwards [hsmall, hsqrt, eventually_ge_atTop 1] with X hsmall hsqrt hX
  have hX' : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX'
  have hlogadd : 0 ≤ Real.log ((X : ℝ) + 1) := Real.log_nonneg (by linarith)
  simp only [Real.norm_eq_abs, abs_of_nonneg hlogadd,
    abs_of_nonneg (show 0 ≤ (X : ℝ) + 1 by positivity), id_eq] at hsmall
  rw [← Real.sqrt_eq_rpow] at hsqrt
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg (Real.sqrt_nonneg _)] at hsqrt
  have herror : 2 * Real.sqrt X * Real.log X ≤ (Real.log 2 / 4) * (X : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg (X : ℝ))
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ X by positivity)]
  have hshiftError : Real.log ((X : ℝ) + 1) ≤ (Real.log 2 / 4) * (X : ℝ) := by
    nlinarith
  nlinarith [Chebyshev.theta_ge X]

/-- An explicit unconditional linear lower bound for the total prime digit mass. -/
theorem eventually_primeDigitMass_ge (b : ℕ) (hb : 1 < b) :
    ∀ᶠ X : ℕ in atTop,
      (Real.log 2 / (2 * Real.log b)) * (X : ℝ) ≤ (primeDigitMass b hb X : ℝ) := by
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  filter_upwards [eventually_theta_ge_half_log_two_mul] with X htheta
  have hmass := theta_le_primeDigitMass_mul_log b hb X
  apply (le_of_mul_le_mul_right ?_ hlogb)
  calc
    (Real.log 2 / (2 * Real.log b) * (X : ℝ)) * Real.log b =
        (Real.log 2 / 2) * (X : ℝ) := by field_simp
    _ ≤ _ := htheta.trans hmass

/-- A positive-constant interface for the linear growth of the total prime digit mass. -/
theorem exists_pos_eventually_primeDigitMass_ge (b : ℕ) (hb : 1 < b) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c * (X : ℝ) ≤ (primeDigitMass b hb X : ℝ) := by
  refine ⟨Real.log 2 / (2 * Real.log b), ?_, eventually_primeDigitMass_ge b hb⟩
  exact div_pos (Real.log_pos (by norm_num))
    (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hb)))

/-- The number of prime blocks is negligible compared with their total digit length. -/
theorem tendsto_primeCounting_div_primeDigitMass (b : ℕ) (hb : 1 < b) :
    Tendsto (fun X : ℕ ↦ (Nat.primeCounting X : ℝ) / (primeDigitMass b hb X : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hmass⟩ := exists_pos_eventually_primeDigitMass_ge b hb
  have hpi := tendsto_natCast_atTop_atTop.eventually
    (Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num))
  have hupper : ∀ᶠ X : ℕ in atTop,
      (Nat.primeCounting X : ℝ) / (primeDigitMass b hb X : ℝ) ≤
        ((Real.log 4 + 1) / c) / Real.log X := by
    filter_upwards [hmass, hpi, eventually_gt_atTop 1] with X hmass hpi hX
    have hX' : (1 : ℝ) < X := by exact_mod_cast hX
    have hX0 : (0 : ℝ) < X := lt_trans zero_lt_one hX'
    have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hX'
    have hcx : 0 < c * (X : ℝ) := mul_pos hc hX0
    simp only [Nat.floor_natCast] at hpi
    calc
      (Nat.primeCounting X : ℝ) / (primeDigitMass b hb X : ℝ) ≤
          (Nat.primeCounting X : ℝ) / (c * (X : ℝ)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hcx hmass
      _ ≤ ((Real.log 4 + 1) * (X : ℝ) / Real.log X) / (c * (X : ℝ)) :=
        div_le_div_of_nonneg_right hpi hcx.le
      _ = ((Real.log 4 + 1) / c) / Real.log X := by
        field_simp
  apply squeeze_zero' (Eventually.of_forall fun X ↦ by positivity) hupper
  exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop _

end CopelandErdos.NumberTheory
