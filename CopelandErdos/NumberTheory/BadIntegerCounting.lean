module

public import CopelandErdos.Analysis.GeometricBounds
public import CopelandErdos.NumberTheory.BadIntegers

/-!
# Counting exceptional integers below a cutoff

`badIntegersBelow ... X` contains positive integers strictly below `X`, with the
overlapping occurrence count normalized by each integer's own standard digit length.
Decomposition by exact digit length transfers the uniform word estimate and the geometric
summation estimate to a bound with a constant independent of the cutoff and length bound.
-/

@[expose] public section

open scoped BigOperators

namespace CopelandErdos.NumberTheory

open CopelandErdos.Analysis CopelandErdos.Digits CopelandErdos.Words

variable {b k X L : ℕ}

/-- Bad positive integers `a < X`, normalized by their actual digit lengths.
The cutoff is exclusive, and every overlapping pattern occurrence is counted. -/
noncomputable def badIntegersBelow (b : ℕ) (hb : 1 < b) (w : Fin k → Fin b)
    (ε : ℝ) (X : ℕ) : Finset ℕ :=
  (Finset.range X).filter (fun a ↦ 0 < a ∧
    ε < |(occurrenceCount (List.ofFn w) (natWord b hb a) : ℝ) /
      ((natWord b hb a).length : ℝ) - 1 / (b : ℝ) ^ k|)

@[simp] theorem mem_badIntegersBelow (hb : 1 < b) (w : Fin k → Fin b) (ε : ℝ)
    (X a : ℕ) :
    a ∈ badIntegersBelow b hb w ε X ↔ a < X ∧ 0 < a ∧
      ε < |(occurrenceCount (List.ofFn w) (natWord b hb a) : ℝ) /
        ((natWord b hb a).length : ℝ) - 1 / (b : ℝ) ^ k| := by
  classical
  simp [badIntegersBelow]

theorem badIntegersOfLength_subset_badIntegersBelow (hb : 1 < b)
    (w : Fin k → Fin b) (ε : ℝ) (ℓ X : ℕ) :
    badIntegersOfLength b hb w ε ℓ X ⊆ badIntegersBelow b hb w ε X := by
  intro a ha
  rcases (mem_badIntegersOfLength hb w ε ℓ X a).1 ha with ⟨haX, ha, hlen, hbad⟩
  apply (mem_badIntegersBelow hb w ε X a).2
  exact ⟨haX, ha, by simpa only [hlen] using hbad⟩

/-- If `L` bounds all positive digit lengths below the cutoff, the bad integers are
exactly the union of their exact-length fibers with lengths from `1` through `L`. -/
theorem badIntegersBelow_eq_biUnion (hb : 1 < b) (w : Fin k → Fin b) (ε : ℝ)
    (hL : ∀ a : ℕ, 0 < a → a < X → (natWord b hb a).length ≤ L) :
    badIntegersBelow b hb w ε X = (Finset.Icc 1 L).biUnion
      (fun ℓ ↦ badIntegersOfLength b hb w ε ℓ X) := by
  classical
  ext a
  constructor
  · intro ha
    rcases (mem_badIntegersBelow hb w ε X a).1 ha with ⟨haX, ha, hbad⟩
    apply Finset.mem_biUnion.2
    refine ⟨(natWord b hb a).length, Finset.mem_Icc.2 ⟨?_, hL a ha haX⟩, ?_⟩
    · exact length_natWord_pos b hb a ha
    · exact (mem_badIntegersOfLength hb w ε _ X a).2 ⟨haX, ha, rfl, hbad⟩
  · intro ha
    obtain ⟨ℓ, _, haℓ⟩ := Finset.mem_biUnion.1 ha
    exact badIntegersOfLength_subset_badIntegersBelow hb w ε ℓ X haℓ

/-- Summing over exact lengths bounds the number of bad integers by bad-word counts. -/
theorem card_badIntegersBelow_le_sum_badWords (hb : 1 < b) (w : Fin k → Fin b)
    (ε : ℝ) (hL : ∀ a : ℕ, 0 < a → a < X → (natWord b hb a).length ≤ L) :
    (badIntegersBelow b hb w ε X).card ≤
      ∑ ℓ ∈ Finset.Icc 1 L, (badWords w ε ℓ).card := by
  classical
  rw [badIntegersBelow_eq_biUnion hb w ε hL]
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro ℓ _
  exact card_badIntegersOfLength_le_badWords hb w ε ℓ X

/-- One positive constant bounds every cutoff and every positive digit-length bound.
The summation estimate is applied once to `card (badWords w ε ℓ)`, independently of `X`. -/
theorem exists_badIntegersBelow_card_le (hb : 2 ≤ b) (hk : 1 ≤ k)
    (w : Fin k → Fin b) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X L : ℕ, 1 ≤ L →
      (∀ a : ℕ, 0 < a → a < X → (natWord b (by omega) a).length ≤ L) →
      ((badIntegersBelow b (by omega) w ε X).card : ℝ) ≤
        C * (b : ℝ) ^ L / (L : ℝ) ^ 2 := by
  obtain ⟨K, hK, hwords⟩ := exists_badWords_card_le hb hk w ε hε
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  obtain ⟨C, hC, hsum⟩ := exists_pos_sum_le_geometric_div_sq
    (a := fun ℓ ↦ ((badWords w ε ℓ).card : ℝ)) hbR hK.le hwords
  refine ⟨C, hC, ?_⟩
  intro X L hL hlength
  apply le_trans _ (hsum L hL)
  exact_mod_cast card_badIntegersBelow_le_sum_badWords (by omega : 1 < b) w ε hlength

/-- The standard digit length below an exclusive cutoff is at most `log_b X + 1`. -/
theorem length_natWord_le_log_cutoff (hb : 1 < b) {a : ℕ} (ha : 0 < a) (haX : a < X) :
    (natWord b hb a).length ≤ Nat.log b X + 1 := by
  rw [length_natWord_eq_log_add_one b hb a (Nat.ne_of_gt ha)]
  exact Nat.add_le_add_right (Nat.log_mono_right haX.le) 1

/-- Specialize the uniform counting bound to the logarithmic digit-length cutoff. -/
theorem exists_badIntegersBelow_card_le_log_length (hb : 2 ≤ b) (hk : 1 ≤ k)
    (w : Fin k → Fin b) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 0 < X →
      ((badIntegersBelow b (by omega) w ε X).card : ℝ) ≤
        C * (b : ℝ) ^ (Nat.log b X + 1) / ((Nat.log b X + 1 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_badIntegersBelow_card_le hb hk w ε hε
  refine ⟨C, hC, ?_⟩
  intro X _
  apply hbound X (Nat.log b X + 1) (by omega)
  intro a ha haX
  exact length_natWord_le_log_cutoff (by omega : 1 < b) ha haX

/-- Replace the exponential cutoff term by `b X`, retaining the positive digit-length
denominator. This form is convenient when subsequently weighting bad integers by length. -/
theorem exists_badIntegersBelow_card_le_log_length_linear (hb : 2 ≤ b) (hk : 1 ≤ k)
    (w : Fin k → Fin b) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 0 < X →
      ((badIntegersBelow b (by omega) w ε X).card : ℝ) ≤
        C * (X : ℝ) / ((Nat.log b X + 1 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_badIntegersBelow_card_le_log_length hb hk w ε hε
  refine ⟨C * (b : ℝ), by positivity, ?_⟩
  intro X hX
  have hpow : (b : ℝ) ^ (Nat.log b X + 1) ≤ (b : ℝ) * (X : ℝ) := by
    have hn : b ^ (Nat.log b X + 1) ≤ b * X := by
      rw [pow_succ']
      exact Nat.mul_le_mul_left b (Nat.pow_log_le_self b (Nat.ne_of_gt hX))
    exact_mod_cast hn
  calc
    _ ≤ C * (b : ℝ) ^ (Nat.log b X + 1) / ((Nat.log b X + 1 : ℕ) : ℝ) ^ 2 :=
      hbound X hX
    _ ≤ C * ((b : ℝ) * (X : ℝ)) / ((Nat.log b X + 1 : ℕ) : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) (by positivity)
    _ = _ := by ring

/-- For `X ≥ b`, the count is at most `C X / (log_b X)²` with the integer logarithm.
This range ensures that the logarithmic denominator is positive. -/
theorem exists_badIntegersBelow_card_le_nat_log_sq (hb : 2 ≤ b) (hk : 1 ≤ k)
    (w : Fin k → Fin b) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, b ≤ X →
      ((badIntegersBelow b (by omega) w ε X).card : ℝ) ≤
        C * (X : ℝ) / (Nat.log b X : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_badIntegersBelow_card_le_log_length_linear hb hk w ε hε
  refine ⟨C, hC, ?_⟩
  intro X hbX
  have hX : 0 < X := lt_of_lt_of_le (by omega : 0 < b) hbX
  have hlog : 0 < (Nat.log b X : ℝ) := by
    exact_mod_cast Nat.log_pos (by omega : 1 < b) hbX
  have hden : (Nat.log b X : ℝ) ^ 2 ≤ ((Nat.log b X + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith
  calc
    _ ≤ C * (X : ℝ) / ((Nat.log b X + 1 : ℕ) : ℝ) ^ 2 :=
      hbound X hX
    _ ≤ C * (X : ℝ) / (Nat.log b X : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden

end CopelandErdos.NumberTheory
