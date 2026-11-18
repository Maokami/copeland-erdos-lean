module

public import Mathlib.Analysis.Real.OfDigits
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Recovering canonical positional expansions

A digit sequence whose every tail has a digit smaller than the maximal digit has
all tail values strictly below one. Scaling its real value by a power of the base
therefore separates an integral prefix value from a tail in `[0, 1)`. The natural
floor recovers that prefix, and reduction modulo the base recovers each digit.
-/

@[expose] public section

open scoped BigOperators

namespace CopelandErdos.Digits

/-- One digit smaller than the maximal digit makes the represented value strictly below one. -/
theorem ofDigits_lt_one_of_exists_lt_last {b : ℕ} (hb : 1 < b) (d : ℕ → Fin b)
    (h : ∃ j, (d j).val < b - 1) : Real.ofDigits d < 1 := by
  let last : ℕ → Fin b := fun _ ↦ ⟨b - 1, Nat.sub_one_lt_of_lt hb⟩
  obtain ⟨j, hj⟩ := h
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (lt_trans Nat.zero_lt_one hb)
  have hle : ∀ i, Real.ofDigitsTerm d i ≤ Real.ofDigitsTerm last i := by
    intro i
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.le_sub_one_of_lt (d i).isLt
  have hlt : Real.ofDigitsTerm d j < Real.ofDigitsTerm last j := by
    apply mul_lt_mul_of_pos_right _ (by positivity)
    exact_mod_cast hj
  have ht : Real.ofDigits d < Real.ofDigits last :=
    Summable.tsum_lt_tsum hle hlt Real.summable_ofDigitsTerm Real.summable_ofDigitsTerm
  dsimp only [last] at ht
  rwa [Real.ofDigits_const_last_eq_one' hb] at ht

/-- The canonical-tail condition makes the value of every tail strictly below one. -/
theorem ofDigits_tail_lt_one {b : ℕ} (hb : 1 < b) (d : ℕ → Fin b)
    (hcanonical : ∀ N, ∃ j, N ≤ j ∧ (d j).val < b - 1) (N : ℕ) :
    Real.ofDigits (fun i ↦ d (i + N)) < 1 := by
  obtain ⟨j, hjN, hj⟩ := hcanonical N
  apply ofDigits_lt_one_of_exists_lt_last hb
  refine ⟨j - N, ?_⟩
  simpa only [Nat.sub_add_cancel hjN] using hj

/-- A sequence with no tail consisting solely of maximal digits represents a value below one. -/
theorem ofDigits_lt_one_of_canonical {b : ℕ} (hb : 1 < b) (d : ℕ → Fin b)
    (hcanonical : ∀ N, ∃ j, N ≤ j ∧ (d j).val < b - 1) : Real.ofDigits d < 1 := by
  simpa only [Nat.add_zero] using ofDigits_tail_lt_one hb d hcanonical 0

/-- Any positive digit makes the represented real value strictly positive. -/
theorem ofDigits_pos_of_exists_pos {b : ℕ} (d : ℕ → Fin b)
    (hpositive : ∃ j, 0 < (d j).val) : 0 < Real.ofDigits d := by
  obtain ⟨j, hj⟩ := hpositive
  have hb0 : (0 : ℝ) < b := by exact_mod_cast Fin.pos (d j)
  have hterm : 0 < Real.ofDigitsTerm d j := by
    apply mul_pos
    · exact_mod_cast hj
    · positivity
  apply hterm.trans_le
  simpa only [Finset.sum_singleton, Real.ofDigits] using
    (Real.summable_ofDigitsTerm (digits := d)).sum_le_tsum {j}
      (fun _ _ ↦ Real.ofDigitsTerm_nonneg)

/-- If every tail contains a positive digit, every represented tail value is positive. -/
theorem ofDigits_tail_pos {b : ℕ} (d : ℕ → Fin b)
    (hpositive : ∀ N, ∃ j, N ≤ j ∧ 0 < (d j).val) (N : ℕ) :
    0 < Real.ofDigits (fun i ↦ d (i + N)) := by
  obtain ⟨j, hjN, hj⟩ := hpositive N
  apply ofDigits_pos_of_exists_pos
  refine ⟨j - N, ?_⟩
  simpa only [Nat.sub_add_cancel hjN] using hj

/-- The natural number written by the first `n` digits, in most-significant-first order. -/
def digitPrefixValue {b : ℕ} (d : ℕ → Fin b) : ℕ → ℕ
  | 0 => 0
  | n + 1 => b * digitPrefixValue d n + (d n).val

@[simp] theorem digitPrefixValue_zero {b : ℕ} (d : ℕ → Fin b) : digitPrefixValue d 0 = 0 := rfl

@[simp] theorem digitPrefixValue_succ {b : ℕ} (d : ℕ → Fin b) (n : ℕ) :
    digitPrefixValue d (n + 1) = b * digitPrefixValue d n + (d n).val := rfl

private theorem ofDigits_tail_step {b : ℕ} (hb : 1 < b) (d : ℕ → Fin b) (n : ℕ) :
    (b : ℝ) * Real.ofDigits (fun i ↦ d (i + n)) =
      (d n).val + Real.ofDigits (fun i ↦ d (i + (n + 1))) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hb)
  have h := Real.ofDigits_eq_sum_add_ofDigits (fun i ↦ d (i + n)) 1
  simp only [Finset.sum_range_one, Real.ofDigitsTerm, zero_add, pow_one] at h
  simp only [Nat.add_assoc, Nat.add_comm 1 n] at h
  rw [h]
  field_simp

/-- Scaling by `b^n` separates the integral prefix value from the remaining digit tail. -/
theorem pow_mul_ofDigits_eq_prefix_add_tail {b : ℕ} (hb : 1 < b) (d : ℕ → Fin b) (n : ℕ) :
    (b : ℝ) ^ n * Real.ofDigits d =
      (digitPrefixValue d n : ℝ) + Real.ofDigits (fun i ↦ d (i + n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, mul_add, digitPrefixValue_succ]
    push_cast
    linarith [ofDigits_tail_step hb d n]

/-- For a canonical sequence, the floor of the scaled real is exactly its prefix value. -/
theorem floor_pow_mul_ofDigits_eq_prefix {b : ℕ} (hb : 1 < b) (d : ℕ → Fin b)
    (hcanonical : ∀ N, ∃ j, N ≤ j ∧ (d j).val < b - 1) (n : ℕ) :
    ⌊(b : ℝ) ^ n * Real.ofDigits d⌋₊ = digitPrefixValue d n := by
  apply (Nat.floor_eq_iff (mul_nonneg (by positivity) (Real.ofDigits_nonneg d))).2
  rw [pow_mul_ofDigits_eq_prefix_add_tail hb d n]
  constructor
  · linarith [Real.ofDigits_nonneg (fun i ↦ d (i + n))]
  · linarith [ofDigits_tail_lt_one hb d hcanonical n]

/-- Canonical digit sequences are recovered from their represented real by `Real.digits`. -/
theorem digits_ofDigits_of_canonical {b : ℕ} [NeZero b] (hb : 1 < b) (d : ℕ → Fin b)
    (hcanonical : ∀ N, ∃ j, N ≤ j ∧ (d j).val < b - 1) :
    Real.digits (Real.ofDigits d) b = d := by
  funext n
  apply Fin.ext
  change ⌊Real.ofDigits d * (b : ℝ) ^ (n + 1)⌋₊ % b = (d n).val
  rw [mul_comm, floor_pow_mul_ofDigits_eq_prefix hb d hcanonical, digitPrefixValue_succ]
  simp [Nat.add_mod, Nat.mod_eq_of_lt (d n).isLt]

end CopelandErdos.Digits
