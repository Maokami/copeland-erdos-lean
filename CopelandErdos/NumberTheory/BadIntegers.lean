module

public import CopelandErdos.Digits.NatWord
public import CopelandErdos.Digits.PrimeStream
public import CopelandErdos.Words.BadWords

/-!
# Exceptional integers of a fixed digit length

The cutoff in `badIntegersOfLength ... ℓ X` is exclusive: its members satisfy `a < X`.
The frequency uses every overlapping occurrence and the full digit length as denominator,
exactly as in `Words.badWords`. Injectivity of standard digit words transfers the proved
finite-word estimate to these integers, uniformly in the cutoff.
-/

@[expose] public section

namespace CopelandErdos.Digits

/-- The standard integer word of the `n`th prime agrees with the existing stream block. -/
theorem natWord_nth_prime_eq_primeBlock (b : ℕ) (hb : 1 < b) (n : ℕ) :
    natWord b hb (Nat.nth Nat.Prime n) = primeBlock b hb n := by
  rfl

end CopelandErdos.Digits

namespace CopelandErdos.NumberTheory

open CopelandErdos.Digits CopelandErdos.Words

variable {b k ℓ X : ℕ}

/-- Positive integers `a < X` of exactly `ℓ` digits whose full-length frequency error
exceeds `ε`. The cutoff is exclusive, and all overlapping pattern matches are counted. -/
noncomputable def badIntegersOfLength (b : ℕ) (hb : 1 < b) (w : Fin k → Fin b)
    (ε : ℝ) (ℓ X : ℕ) : Finset ℕ :=
  (Finset.range X).filter (fun a ↦ 0 < a ∧ (natWord b hb a).length = ℓ ∧
    ε < |(occurrenceCount (List.ofFn w) (natWord b hb a) : ℝ) / (ℓ : ℝ) -
      1 / (b : ℝ) ^ k|)

@[simp] theorem mem_badIntegersOfLength (hb : 1 < b) (w : Fin k → Fin b) (ε : ℝ)
    (ℓ X a : ℕ) :
    a ∈ badIntegersOfLength b hb w ε ℓ X ↔ a < X ∧ 0 < a ∧
      (natWord b hb a).length = ℓ ∧
      ε < |(occurrenceCount (List.ofFn w) (natWord b hb a) : ℝ) / (ℓ : ℝ) -
        1 / (b : ℝ) ^ k| := by
  classical
  simp [badIntegersOfLength]

/-- The exact-length encoding sends every exceptional integer to an exceptional word. -/
theorem natWordOfLength_mem_badWords (hb : 1 < b) (w : Fin k → Fin b) (ε : ℝ)
    {a : ℕ} (ha : a ∈ badIntegersOfLength b hb w ε ℓ X) :
    natWordOfLength b hb a ((mem_badIntegersOfLength hb w ε ℓ X a).1 ha).2.2.1 ∈
      badWords w ε ℓ := by
  classical
  have hbad := ((mem_badIntegersOfLength hb w ε ℓ X a).1 ha).2.2.2
  simpa [badWords] using hbad

/-- Standard digit words embed the bad positive integers of exact length `ℓ` below `X`
into all bad length-`ℓ` words, which may also have leading zeroes. -/
theorem card_badIntegersOfLength_le_badWords (hb : 1 < b) (w : Fin k → Fin b) (ε : ℝ)
    (ℓ X : ℕ) :
    (badIntegersOfLength b hb w ε ℓ X).card ≤ (badWords w ε ℓ).card := by
  classical
  let f : {a // a ∈ badIntegersOfLength b hb w ε ℓ X} → {u // u ∈ badWords w ε ℓ} :=
    fun a ↦ ⟨natWordOfLength b hb a.val
      ((mem_badIntegersOfLength hb w ε ℓ X a.val).1 a.property).2.2.1,
      natWordOfLength_mem_badWords hb w ε a.property⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro a c h
  apply Subtype.ext
  exact natWordOfLength_injective b hb
    ((mem_badIntegersOfLength hb w ε ℓ X a.val).1 a.property).2.2.1
    ((mem_badIntegersOfLength hb w ε ℓ X c.val).1 c.property).2.2.1
    (congrArg Subtype.val h)

/-- The proved word estimate gives one positive constant for all positive digit lengths
and every exclusive cutoff `X`; no additional combinatorial bound is assumed. -/
theorem exists_badIntegersOfLength_card_le (hb : 2 ≤ b) (hk : 1 ≤ k)
    (w : Fin k → Fin b) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ X : ℕ,
      ((badIntegersOfLength b (by omega) w ε ℓ X).card : ℝ) ≤
        K * (b : ℝ) ^ ℓ / (ℓ : ℝ) ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := exists_badWords_card_le hb hk w ε hε
  refine ⟨K, hK, ?_⟩
  intro ℓ hℓ X
  apply le_trans _ (hbound ℓ hℓ)
  exact_mod_cast card_badIntegersOfLength_le_badWords (by omega : 1 < b) w ε ℓ X

end CopelandErdos.NumberTheory
