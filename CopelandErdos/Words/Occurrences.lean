module

public import Mathlib.Data.List.TakeDrop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega

/-!
# Overlapping occurrences in finite words

An occurrence must be fully contained in the host. Every valid starting index is counted,
including overlapping occurrences. The empty pattern has count zero by convention; normality
will quantify only over nonempty patterns.
-/

public section

namespace CopelandErdos.Words

variable {α : Type*} [DecidableEq α]

/-- The pattern `w` occurs at starting index `i`, fully inside the host `u`. -/
def OccursAt (w u : List α) (i : ℕ) : Prop :=
  i + w.length ≤ u.length ∧ (u.drop i).take w.length = w

instance (w u : List α) (i : ℕ) : Decidable (OccursAt w u i) :=
  inferInstanceAs (Decidable
    (i + w.length ≤ u.length ∧ (u.drop i).take w.length = w))

/-- Indicator of a fully contained occurrence, before the empty-pattern convention. -/
def occurrenceIndicator (w u : List α) (i : ℕ) : ℕ :=
  if OccursAt w u i then 1 else 0

/-- Count all overlapping occurrences. The empty pattern has count zero by convention. -/
def occurrenceCount (w u : List α) : ℕ :=
  if w = [] then 0 else ∑ i ∈ Finset.range u.length, occurrenceIndicator w u i

@[simp] theorem occurrenceCount_nil_pattern (u : List α) : occurrenceCount [] u = 0 := by
  simp [occurrenceCount]

@[simp] theorem occurrenceCount_nil_host (w : List α) : occurrenceCount w [] = 0 := by
  simp [occurrenceCount]

/-- Direct semantic bridge: the count is the cardinality of the valid matching start indices. -/
theorem occurrenceCount_eq_card (w u : List α) (hw : w ≠ []) :
    occurrenceCount w u = ((Finset.range u.length).filter (OccursAt w u)).card := by
  simp [occurrenceCount, hw, Finset.card_filter, occurrenceIndicator]

omit [DecidableEq α] in
/-- For a nonempty pattern, the host range includes every fully contained occurrence. -/
theorem occursAt_start_lt {w u : List α} {i : ℕ} (hw : w ≠ [])
    (h : OccursAt w u i) : i < u.length := by
  have hk : 0 < w.length := List.length_pos_iff.mpr hw
  have := h.1
  omega

theorem occurrenceIndicator_le_one (w u : List α) (i : ℕ) :
    occurrenceIndicator w u i ≤ 1 := by
  unfold occurrenceIndicator
  split <;> omega

private theorem sum_range_le {f : ℕ → ℕ} (n : ℕ) (hf : ∀ i, f i ≤ 1) :
    ∑ i ∈ Finset.range n, f i ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hf n
      omega

/-- There are at most as many nonempty-pattern occurrences as host symbols. -/
theorem occurrenceCount_le_length (w u : List α) : occurrenceCount w u ≤ u.length := by
  unfold occurrenceCount
  split
  · omega
  · exact sum_range_le _ (occurrenceIndicator_le_one w u)

theorem occurrenceCount_eq_zero_of_length_lt {w u : List α} (h : u.length < w.length) :
    occurrenceCount w u = 0 := by
  unfold occurrenceCount
  split
  · rfl
  · apply Finset.sum_eq_zero
    intro i hi
    simp only [occurrenceIndicator, OccursAt]
    have : ¬ i + w.length ≤ u.length := by omega
    simp [this]

private theorem indicator_append_shift (w u v : List α) (i : ℕ) :
    occurrenceIndicator w (u ++ v) (u.length + i) = occurrenceIndicator w v i := by
  have hd : (u ++ v).drop (u.length + i) = v.drop i := by
    rw [List.drop_append]
    simp
  have hlen : u.length + i + w.length ≤ u.length + v.length ↔
      i + w.length ≤ v.length := by omega
  simp only [occurrenceIndicator, OccursAt, List.length_append, hd, hlen]
  rfl

private theorem indicator_append_of_fits {w u : List α} (v : List α) {i : ℕ}
    (hi : i + w.length ≤ u.length) :
    occurrenceIndicator w (u ++ v) i = occurrenceIndicator w u i := by
  have hiu : i ≤ u.length := by omega
  have hk : w.length ≤ (u.drop i).length := by simp only [List.length_drop]; omega
  rw [occurrenceIndicator, occurrenceIndicator]
  simp only [OccursAt, List.length_append, List.drop_append_of_le_length hiu,
    List.take_append_of_le_length hk]
  have hiuv : i + w.length ≤ u.length + v.length := by omega
  simp [hi, hiuv]

private theorem indicator_zero_of_not_fits {w u : List α} {i : ℕ}
    (hi : ¬ i + w.length ≤ u.length) : occurrenceIndicator w u i = 0 := by
  simp [occurrenceIndicator, OccursAt, hi]

private theorem indicator_le_append (w u v : List α) (i : ℕ) :
    occurrenceIndicator w u i ≤ occurrenceIndicator w (u ++ v) i := by
  by_cases hi : i + w.length ≤ u.length
  · rw [indicator_append_of_fits v hi]
  · rw [indicator_zero_of_not_fits hi]
    exact Nat.zero_le _

/-- Existing occurrences in either component survive concatenation. -/
theorem occurrenceCount_add_le_append (w u v : List α) :
    occurrenceCount w u + occurrenceCount w v ≤ occurrenceCount w (u ++ v) := by
  by_cases hw : w = []
  · simp [hw]
  simp only [occurrenceCount, hw, ite_false, List.length_append, Finset.sum_range_add]
  simp_rw [indicator_append_shift]
  exact Nat.add_le_add_right (Finset.sum_le_sum fun i _ ↦ indicator_le_append w u v i) _

/-- Appending a word never removes an occurrence. -/
theorem occurrenceCount_le_append (w u v : List α) :
    occurrenceCount w u ≤ occurrenceCount w (u ++ v) := by
  have := occurrenceCount_add_le_append w u v
  omega

/-- Sum over precisely the possible starting indices of a nonempty pattern. -/
theorem occurrenceCount_eq_sum_valid (w u : List α) (hw : w ≠ []) :
    occurrenceCount w u =
      ∑ i ∈ Finset.range (u.length + 1 - w.length), occurrenceIndicator w u i := by
  have hk : 0 < w.length := List.length_pos_iff.mpr hw
  have hs : u.length + 1 - w.length ≤ u.length := by omega
  have hsplit : u.length = (u.length + 1 - w.length) +
      (u.length - (u.length + 1 - w.length)) := by omega
  simp only [occurrenceCount, hw, ite_false]
  conv_lhs => rw [hsplit, Finset.sum_range_add]
  have hz : ∑ i ∈ Finset.range (u.length - (u.length + 1 - w.length)),
      occurrenceIndicator w u (u.length + 1 - w.length + i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply indicator_zero_of_not_fits
    omega
  rw [hz, Nat.add_zero]

/-- At most `w.length - 1` occurrences cross the join, including empty/short hosts. -/
theorem occurrenceCount_append_le (w u v : List α) (hw : w ≠ []) :
    occurrenceCount w (u ++ v) ≤
      occurrenceCount w u + occurrenceCount w v + (w.length - 1) := by
  let n := u.length + 1 - w.length
  have hk : 0 < w.length := List.length_pos_iff.mpr hw
  have hn : n ≤ u.length := by dsimp [n]; omega
  have hsplit : u.length = n + (u.length - n) := by omega
  have hleft : ∑ i ∈ Finset.range n, occurrenceIndicator w (u ++ v) i =
      occurrenceCount w u := by
    rw [occurrenceCount_eq_sum_valid w u hw]
    apply Finset.sum_congr rfl
    intro i hi
    apply indicator_append_of_fits
    have := Finset.mem_range.mp hi
    dsimp [n] at this
    omega
  have hcross : (∑ i ∈ Finset.range (u.length - n),
      occurrenceIndicator w (u ++ v) (n + i)) ≤ w.length - 1 := by
    apply (sum_range_le (u.length - n)
      (fun i ↦ occurrenceIndicator_le_one w (u ++ v) (n + i))).trans
    dsimp [n]
    omega
  have hv : ∑ i ∈ Finset.range v.length, occurrenceIndicator w v i =
      occurrenceCount w v := by simp [occurrenceCount, hw]
  have hdecomp : occurrenceCount w (u ++ v) = occurrenceCount w u +
      (∑ i ∈ Finset.range (u.length - n), occurrenceIndicator w (u ++ v) (n + i)) +
      occurrenceCount w v := by
    rw [occurrenceCount, ite_eq_right hw, List.length_append, Finset.sum_range_add]
    simp_rw [indicator_append_shift]
    conv_lhs => lhs; rw [hsplit, Finset.sum_range_add]
    rw [hleft, hv]
  omega

/-- The boundary gap is nonnegative and at most `w.length - 1`. -/
theorem occurrenceCount_append_gap (w u v : List α) (hw : w ≠ []) :
    occurrenceCount w u + occurrenceCount w v ≤ occurrenceCount w (u ++ v) ∧
      occurrenceCount w (u ++ v) - (occurrenceCount w u + occurrenceCount w v) ≤
        w.length - 1 := by
  constructor
  · exact occurrenceCount_add_le_append w u v
  · have := occurrenceCount_append_le w u v hw
    omega

/-- Appending `v` creates at most `v.length` new fully contained occurrences. -/
theorem occurrenceCount_append_le_add_length (w u v : List α) :
    occurrenceCount w (u ++ v) ≤ occurrenceCount w u + v.length := by
  by_cases hw : w = []
  · simp [hw]
  let n := u.length + 1 - w.length
  let m := (u ++ v).length + 1 - w.length
  have hnm : n ≤ m := by dsimp [n, m]; simp only [List.length_append]; omega
  have hdiff : m - n ≤ v.length := by
    dsimp [n, m]
    simp only [List.length_append]
    omega
  have hsplit : m = n + (m - n) := by omega
  rw [occurrenceCount_eq_sum_valid w (u ++ v) hw]
  change (∑ i ∈ Finset.range m, occurrenceIndicator w (u ++ v) i) ≤ _
  rw [hsplit, Finset.sum_range_add]
  have hleft : ∑ i ∈ Finset.range n, occurrenceIndicator w (u ++ v) i =
      occurrenceCount w u := by
    rw [occurrenceCount_eq_sum_valid w u hw]
    apply Finset.sum_congr rfl
    intro i hi
    apply indicator_append_of_fits
    have := Finset.mem_range.mp hi
    dsimp [n] at this
    omega
  rw [hleft]
  have hb := sum_range_le (m - n)
    (fun i ↦ occurrenceIndicator_le_one w (u ++ v) (n + i))
  omega

example : occurrenceCount ([1, 1] : List ℕ) [1, 1, 1] = 2 := by decide
example : occurrenceCount ([1, 1, 1] : List ℕ) [1, 1] = 0 := by decide
example : occurrenceCount ([1] : List ℕ) [] = 0 := by decide
example : occurrenceCount ([] : List ℕ) [1, 1] = 0 := by decide
example : occurrenceCount ([1, 1] : List ℕ) ([1] ++ [1]) = 1 := by decide

end CopelandErdos.Words
