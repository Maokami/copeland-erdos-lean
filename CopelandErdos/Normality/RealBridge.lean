module

public import CopelandErdos.Digits.RealExpansion
public import CopelandErdos.Normality.NormalDigits
public import CopelandErdos.Normality.PrimeConcatenation

/-!
# The normal Copeland–Erdős real number

`NormalInBase b x` states normality of the standard base-`b` digits of a real number
in `[0, 1)`. Normal digit sequences have a nonmaximal digit and a positive digit in
every tail, so their represented reals lie in `(0, 1)` and recover the original digits.
Applying these facts to the prime digit stream gives the unconditional normality of
the Copeland–Erdős constant `0.2357111317…`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace CopelandErdos.Normality

/-- A real in `[0, 1)` is normal in base `b` when its standard digits are normal. -/
def NormalInBase (b : ℕ) [NeZero b] (x : ℝ) : Prop :=
  0 ≤ x ∧ x < 1 ∧ NormalDigits (Real.digits x b)

/-- A normal digit sequence represents a strictly positive real number. -/
theorem ofDigits_pos_of_normalDigits {b : ℕ} (hb : 1 < b) (d : ℕ → Fin b)
    (hd : NormalDigits d) : 0 < Real.ofDigits d := by
  obtain ⟨j, _, hj⟩ := normalDigits_exists_pos hb hd 0
  exact Digits.ofDigits_pos_of_exists_pos d ⟨j, hj⟩

/-- A normal digit sequence represents a real number strictly below one. -/
theorem ofDigits_lt_one_of_normalDigits {b : ℕ} (hb : 1 < b) (d : ℕ → Fin b)
    (hd : NormalDigits d) : Real.ofDigits d < 1 :=
  Digits.ofDigits_lt_one_of_canonical hb d (normalDigits_exists_lt_last hb hd)

/-- The standard digits of the real represented by a normal sequence recover that sequence. -/
theorem digits_ofDigits_of_normalDigits {b : ℕ} [NeZero b] (hb : 1 < b) (d : ℕ → Fin b)
    (hd : NormalDigits d) : Real.digits (Real.ofDigits d) b = d :=
  Digits.digits_ofDigits_of_canonical hb d (normalDigits_exists_lt_last hb hd)

/-- Normality of a digit sequence gives normality of the represented real in the same base. -/
theorem normalInBase_of_normalDigits {b : ℕ} [NeZero b] (hb : 1 < b) (d : ℕ → Fin b)
    (hd : NormalDigits d) : NormalInBase b (Real.ofDigits d) := by
  refine ⟨Real.ofDigits_nonneg d, ofDigits_lt_one_of_normalDigits hb d hd, ?_⟩
  rwa [digits_ofDigits_of_normalDigits hb d hd]

/-- The Copeland–Erdős constant: the real number `0.2357111317…` formed from the decimal primes. -/
noncomputable def copelandErdos : ℝ := Real.ofDigits (Digits.primeDigits 10 (by decide))

theorem copelandErdos_pos : 0 < copelandErdos :=
  ofDigits_pos_of_normalDigits (by decide) _ (normalDigits_primeDigits 10 (by decide))

theorem copelandErdos_lt_one : copelandErdos < 1 :=
  ofDigits_lt_one_of_normalDigits (by decide) _ (normalDigits_primeDigits 10 (by decide))

/-- The standard decimal expansion is exactly the concatenation of the primes. -/
theorem digits_copelandErdos :
    Real.digits copelandErdos 10 = Digits.primeDigits 10 (by decide) :=
  digits_ofDigits_of_normalDigits (by decide) _ (normalDigits_primeDigits 10 (by decide))

/-- The Copeland–Erdős constant is unconditionally normal in base ten. -/
theorem copelandErdos_normal : NormalInBase 10 copelandErdos :=
  normalInBase_of_normalDigits (by decide) _ (normalDigits_primeDigits 10 (by decide))

/-- Every nonempty finite decimal pattern has its expected frequency in the standard digits. -/
theorem tendsto_copelandErdos_patternFrequency :
    ∀ k : ℕ, 0 < k → ∀ w : Fin k → Fin 10,
      Tendsto (fun M : ℕ ↦
        (Words.occurrenceCount (List.ofFn w)
          (List.ofFn (fun i : Fin M ↦ Real.digits copelandErdos 10 i)) : ℝ) / (M : ℝ))
        atTop (𝓝 (1 / (10 : ℝ) ^ k)) :=
  copelandErdos_normal.2.2

end CopelandErdos.Normality
