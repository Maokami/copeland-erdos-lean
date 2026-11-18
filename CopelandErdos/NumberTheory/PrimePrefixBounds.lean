module

public import CopelandErdos.Digits.PrimeStream
public import CopelandErdos.NumberTheory.PrimeDigitMass
public import Mathlib.Tactic.Ring

/-!
# Prime prefixes and negligible block boundaries

The first `n + 1` primes are exactly the primes up to the `n`th prime. This identifies
their cumulative digit length with `primeDigitMass`. Chebyshev's bounds then make the
number of blocks negligible relative to their total length. Bertrand's postulate and
the logarithmic digit-length bound also make the next individual block negligible.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace CopelandErdos.NumberTheory

/-- The first `n + 1` primes, as a finset, are the primes up to the `n`th prime. -/
theorem image_range_nth_prime_eq_primesLE (n : ℕ) :
    (Finset.range (n + 1)).image (Nat.nth Nat.Prime) =
      Nat.primesLE (Nat.nth Nat.Prime n) := by
  classical
  ext p
  simp only [Finset.mem_image, Finset.mem_range, Nat.mem_primesLE]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 (Nat.le_of_lt_succ hi),
      Nat.prime_nth_prime i⟩
  · rintro ⟨hle, hp⟩
    refine ⟨Nat.primeCounting' p, ?_, Nat.nth_count hp⟩
    apply Nat.lt_succ_of_le
    apply (Nat.nth_le_nth Nat.infinite_setOfPred_prime).1
    simpa only [Nat.primeCounting', Nat.nth_count hp] using hle

/-- Prime counting includes the endpoint, so the `n`th prime has count `n + 1`. -/
theorem primeCounting_nth_prime (n : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  exact Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime n

/-- The increasing enumeration of primes tends to infinity. -/
theorem tendsto_nth_prime_atTop : Tendsto (Nat.nth Nat.Prime) atTop atTop :=
  (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop

/-- Cumulative prime digit length is the sum of the individual block lengths. -/
theorem cumulativeLength_eq_sum_prime_lengths (b : ℕ) (hb : 1 < b) (n : ℕ) :
    Digits.cumulativeLength b hb n =
      ∑ i ∈ Finset.range n, (Digits.primeBlock b hb i).length := by
  induction n with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, ih]

/-- The cumulative length through the `n`th prime equals the inclusive prime digit mass. -/
theorem cumulativeLength_succ_eq_primeDigitMass (b : ℕ) (hb : 1 < b) (n : ℕ) :
    Digits.cumulativeLength b hb (n + 1) = primeDigitMass b hb (Nat.nth Nat.Prime n) := by
  classical
  rw [primeDigitMass, ← image_range_nth_prime_eq_primesLE,
    Finset.sum_image (fun i _ j _ hij ↦
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij),
    cumulativeLength_eq_sum_prime_lengths]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Digits.length_primeBlock, Digits.length_natWord]

/-- The number of prime blocks divided by their cumulative length tends to zero. -/
theorem tendsto_index_div_cumulativeLength (b : ℕ) (hb : 1 < b) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / (Digits.cumulativeLength b hb n : ℝ)) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  have h := (tendsto_primeCounting_div_primeDigitMass b hb).comp tendsto_nth_prime_atTop
  simpa only [Function.comp_def, primeCounting_nth_prime,
    ← cumulativeLength_succ_eq_primeDigitMass] using h

/-- A positive integer's digit length is at most `log p / log b + 1`. -/
theorem length_natWord_le_log_div_log_add_one (b : ℕ) (hb : 1 < b) (p : ℕ) (hp : 0 < p) :
    ((Digits.natWord b hb p).length : ℝ) ≤ Real.log p / Real.log b + 1 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (lt_trans Nat.zero_lt_one hb)
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hpow : (b : ℝ) ^ Nat.log b p ≤ (p : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self b hp.ne'
  have hlog := Real.log_le_log (pow_pos hb0 _) hpow
  rw [Real.log_pow] at hlog
  rw [Digits.length_natWord_eq_log_add_one b hb p hp.ne', Nat.cast_add, Nat.cast_one]
  linarith [(le_div_iff₀ hlogb).2 hlog]

/-- Each next prime block is negligible compared with the length already written. -/
theorem tendsto_primeBlock_length_div_cumulativeLength (b : ℕ) (hb : 1 < b) :
    Tendsto (fun n : ℕ ↦ ((Digits.primeBlock b hb n).length : ℝ) /
      (Digits.cumulativeLength b hb n : ℝ)) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  obtain ⟨c, hc, hmass⟩ := exists_pos_eventually_primeDigitMass_ge b hb
  have hpr : Tendsto (fun n : ℕ ↦ (Nat.nth Nat.Prime n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nth_prime_atTop
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hlogratio : Tendsto
      (fun n : ℕ ↦ Real.log (Nat.nth Nat.Prime n : ℝ) / (Nat.nth Nat.Prime n : ℝ))
      atTop (𝓝 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hpr
  have hupper : ∀ᶠ n : ℕ in atTop,
      ((Digits.primeBlock b hb (n + 1)).length : ℝ) /
          (Digits.cumulativeLength b hb (n + 1) : ℝ) ≤
        (Real.log (Nat.nth Nat.Prime n : ℝ) / (Nat.nth Nat.Prime n : ℝ)) /
            (c * Real.log b) +
          ((Real.log 2 / Real.log b + 1) / c) / (Nat.nth Nat.Prime n : ℝ) := by
    filter_upwards [tendsto_nth_prime_atTop.eventually hmass] with n hmass
    have hp0 : (0 : ℝ) < Nat.nth Nat.Prime n := by
      exact_mod_cast (Nat.prime_nth_prime n).pos
    have hq0 : (0 : ℝ) < Nat.nth Nat.Prime (n + 1) := by
      exact_mod_cast (Nat.prime_nth_prime (n + 1)).pos
    have hcx : 0 < c * (Nat.nth Nat.Prime n : ℝ) := mul_pos hc hp0
    have hgap : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ 2 * Nat.nth Nat.Prime n := by
      exact_mod_cast nth_prime_succ_le_two_mul n
    have hloggap := Real.log_le_log hq0 hgap
    rw [Real.log_mul (by norm_num) hp0.ne'] at hloggap
    have hlength : ((Digits.primeBlock b hb (n + 1)).length : ℝ) ≤
        (Real.log 2 + Real.log (Nat.nth Nat.Prime n : ℝ)) / Real.log b + 1 := by
      calc
        _ ≤ Real.log (Nat.nth Nat.Prime (n + 1) : ℝ) / Real.log b + 1 := by
          simpa only [Digits.length_natWord, Digits.length_primeBlock] using
            length_natWord_le_log_div_log_add_one b hb (Nat.nth Nat.Prime (n + 1))
              (Nat.prime_nth_prime (n + 1)).pos
        _ ≤ _ := by linarith [div_le_div_of_nonneg_right hloggap hlogb.le]
    rw [cumulativeLength_succ_eq_primeDigitMass]
    calc
      _ ≤ ((Digits.primeBlock b hb (n + 1)).length : ℝ) /
          (c * (Nat.nth Nat.Prime n : ℝ)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hcx hmass
      _ ≤ ((Real.log 2 + Real.log (Nat.nth Nat.Prime n : ℝ)) / Real.log b + 1) /
          (c * (Nat.nth Nat.Prime n : ℝ)) :=
        div_le_div_of_nonneg_right hlength hcx.le
      _ = _ := by field_simp; ring
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) hupper
  simpa using (hlogratio.div_const (c * Real.log b)).add
    (hpr.const_div_atTop ((Real.log 2 / Real.log b + 1) / c))

end CopelandErdos.NumberTheory
