module

public import CopelandErdos.Normality.BoundaryCriterion
public import CopelandErdos.Normality.NormalDigits
public import CopelandErdos.NumberTheory.BadPrimeMass
public import CopelandErdos.NumberTheory.PrimePrefixBounds
public import Mathlib.Order.Interval.Finset.Nat

import all CopelandErdos.Words.Concatenation

/-!
# Normality of the concatenated prime digit stream

The exceptional length in the actual first prime blocks agrees exactly with the weighted
exceptional-prime mass. Its negligible ratio, together with the proved negligible boundary
count and next-block length, gives every-prefix frequency convergence for the prime stream.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace CopelandErdos.Normality

open CopelandErdos.Digits CopelandErdos.NumberTheory CopelandErdos.Words

private theorem badLength_eq_sum_range {α : Type*} [DecidableEq α]
    (blocks : ℕ → List α) (w : List α) (p ε : ℝ) (n : ℕ) :
    badLength blocks w p ε n = ∑ i ∈ Finset.range n,
      if ε * ((blocks i).length : ℝ) <
          |(occurrenceCount w (blocks i) : ℝ) - p * ((blocks i).length : ℝ)|
        then (blocks i).length else 0 := by
  classical
  unfold badLength badSubwords
  rw [List.filter_map, List.map_map]
  rw [← List.sum_toFinset _
    (List.Nodup.filter _ (show (List.range n).Nodup from List.nodup_range))]
  simp [Function.comp_def, List.toFinset_filter, List.toFinset_range, Finset.sum_filter]

/-- The bad length through the `n`th prime is exactly the weighted mass of the bad primes
up to that prime. The conversion of the list sum retains every prime once. -/
theorem badLength_primeBlock_succ_eq_badPrimeMass (b : ℕ) (hb : 1 < b) {k : ℕ}
    (w : Fin k → Fin b) (ε : ℝ) (n : ℕ) :
    badLength (primeBlock b hb) (List.ofFn w) (1 / (b : ℝ) ^ k) ε (n + 1) =
      badPrimeMass b hb w ε (Nat.nth Nat.Prime n) := by
  classical
  rw [badLength_eq_sum_range, badPrimeMass, badPrimesLE, Finset.sum_filter,
    ← image_range_nth_prime_eq_primesLE,
    Finset.sum_image (fun i _ j _ hij ↦
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij)]
  apply Finset.sum_congr rfl
  intro i _
  rw [natWord_nth_prime_eq_primeBlock]
  have hL : (0 : ℝ) < (primeBlock b hb i).length := by
    exact_mod_cast length_primeBlock_pos b hb i
  simp only [normalized_bad_iff_mul _ _ _ _ hL]

/-- For every positive tolerance, the actual bad-block length divided by the cumulative
prime digit length tends to zero. -/
theorem tendsto_badLength_div_cumulativeLength (b : ℕ) (hb : 1 < b) {k : ℕ}
    (hk : 0 < k) (w : Fin k → Fin b) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦
      (badLength (primeBlock b hb) (List.ofFn w) (1 / (b : ℝ) ^ k) ε n : ℝ) /
        (cumulativeLength b hb n : ℝ)) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  have h := (tendsto_badPrimeMass_div_primeDigitMass (by omega : 2 ≤ b)
    (by omega : 1 ≤ k) w ε hε).comp tendsto_nth_prime_atTop
  simpa only [Function.comp_def, ← badLength_primeBlock_succ_eq_badPrimeMass,
    ← cumulativeLength_succ_eq_primeDigitMass] using h

/-- Every nonempty digit pattern has its uniform limiting frequency along all actual
prefixes of the concatenation of consecutive primes. -/
theorem tendsto_primeDigits_patternFrequency (b : ℕ) (hb : 1 < b) (k : ℕ)
    (hk : 0 < k) (w : Fin k → Fin b) :
    Tendsto (fun M : ℕ ↦
      (occurrenceCount (List.ofFn w)
        (List.ofFn (fun i : Fin M ↦ primeDigits b hb i)) : ℝ) / (M : ℝ))
      atTop (𝓝 (1 / (b : ℝ) ^ k)) := by
  have hw : List.ofFn w ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hlen
    omega
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hpow : (1 : ℝ) ≤ (b : ℝ) ^ k := one_le_pow₀ hbR
  have hp1 : (1 : ℝ) / (b : ℝ) ^ k ≤ 1 :=
    (div_le_one (lt_of_lt_of_le zero_lt_one hpow)).2 hpow
  simpa only [primeDigits] using
    tendsto_prefixFrequency_of_badLength (primeBlock b hb) (length_primeBlock_pos b hb)
      (List.ofFn w) (1 / (b : ℝ) ^ k) hw (by positivity) hp1
      (by simpa only [cumulativeLength] using tendsto_index_div_cumulativeLength b hb)
      (fun ε hε ↦ by simpa only [cumulativeLength] using
        tendsto_badLength_div_cumulativeLength b hb hk w ε hε)
      (by simpa only [cumulativeLength] using
        tendsto_primeBlock_length_div_cumulativeLength b hb)

/-- The stream obtained by writing consecutive primes in base `b` is unconditionally
normal: every nonempty pattern has its uniform frequency along all finite prefixes. -/
theorem normalDigits_primeDigits (b : ℕ) (hb : 1 < b) : NormalDigits (primeDigits b hb) := by
  intro k hk w
  exact tendsto_primeDigits_patternFrequency b hb k hk w

end CopelandErdos.Normality
