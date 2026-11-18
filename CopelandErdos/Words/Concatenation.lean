module

public import CopelandErdos.Words.Occurrences
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite concatenation error

The error of a concatenation is bounded by the tolerance on its good constituent words,
the total length of its bad constituent words, and the possible boundary occurrences.
All statements concern finite lists and allow empty constituent words.
-/

public section

namespace CopelandErdos.Words

variable {α : Type*} [DecidableEq α]

/-- Occurrences contained in the constituent words survive flattening. -/
theorem sum_occurrenceCount_le_flatten (w : List α) (us : List (List α)) :
    (us.map (occurrenceCount w)).sum ≤ occurrenceCount w us.flatten := by
  induction us with
  | nil => simp
  | cons u us ih =>
      simp only [List.map_cons, List.sum_cons, List.flatten_cons]
      exact (Nat.add_le_add_left ih _).trans (occurrenceCount_add_le_append w u us.flatten)

/-- Each join contributes at most `w.length - 1` new occurrences. The coarse bound counts
one join per constituent word, so it also covers the empty list without subtraction. -/
theorem occurrenceCount_flatten_le (w : List α) (us : List (List α)) (hw : w ≠ []) :
    occurrenceCount w us.flatten ≤
      (us.map (occurrenceCount w)).sum + (w.length - 1) * us.length := by
  induction us with
  | nil => simp
  | cons u us ih =>
      have h := occurrenceCount_append_le w u us.flatten hw
      simp only [List.flatten_cons, List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- For a target frequency in `[0, 1]`, the absolute count error never exceeds the length. -/
theorem abs_occurrenceCount_sub_le_length (w u : List α) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    |(occurrenceCount w u : ℝ) - p * (u.length : ℝ)| ≤ (u.length : ℝ) := by
  have hc : (occurrenceCount w u : ℝ) ≤ (u.length : ℝ) := by
    exact_mod_cast occurrenceCount_le_length w u
  have hc0 : (0 : ℝ) ≤ occurrenceCount w u := by positivity
  have hL : (0 : ℝ) ≤ u.length := by positivity
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Bad constituent words, with multiplicity retained. The unnormalized predicate also
handles empty words: their count and error are both zero. -/
noncomputable def badSubwords (w : List α) (p ε : ℝ) (us : List (List α)) :
    List (List α) := by
  classical
  exact us.filter (fun u ↦
    ε * (u.length : ℝ) < |(occurrenceCount w u : ℝ) - p * (u.length : ℝ)|)

@[simp] theorem mem_badSubwords (w u : List α) (p ε : ℝ) (us : List (List α)) :
    u ∈ badSubwords w p ε us ↔
      u ∈ us ∧ ε * (u.length : ℝ) <
        |(occurrenceCount w u : ℝ) - p * (u.length : ℝ)| := by
  classical
  simp [badSubwords]

/-- Absolute count error is subadditive up to the boundary contribution. -/
theorem abs_occurrenceCount_append_sub_le (w u v : List α) (p : ℝ) (hw : w ≠ []) :
    |(occurrenceCount w (u ++ v) : ℝ) - p * ((u ++ v).length : ℝ)| ≤
      |(occurrenceCount w u : ℝ) - p * (u.length : ℝ)| +
        |(occurrenceCount w v : ℝ) - p * (v.length : ℝ)| + (w.length - 1 : ℕ) := by
  have hlo : (occurrenceCount w u : ℝ) + occurrenceCount w v ≤
      occurrenceCount w (u ++ v) := by
    exact_mod_cast occurrenceCount_add_le_append w u v
  have hhi : (occurrenceCount w (u ++ v) : ℝ) ≤
      occurrenceCount w u + occurrenceCount w v + (w.length - 1 : ℕ) := by
    exact_mod_cast occurrenceCount_append_le w u v hw
  have hu := abs_le.mp (le_refl |(occurrenceCount w u : ℝ) - p * (u.length : ℝ)|)
  have hv := abs_le.mp (le_refl |(occurrenceCount w v : ℝ) - p * (v.length : ℝ)|)
  have hb : (0 : ℝ) ≤ (w.length - 1 : ℕ) := by positivity
  simp only [List.length_append, Nat.cast_add]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Finite concatenation error: good-word tolerance, bad-word length, and boundaries. -/
theorem abs_occurrenceCount_flatten_sub_le (w : List α) (us : List (List α))
    (p ε : ℝ) (hw : w ≠ []) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) :
    |(occurrenceCount w us.flatten : ℝ) - p * (us.flatten.length : ℝ)| ≤
      ε * (us.flatten.length : ℝ) +
        (((badSubwords w p ε us).map List.length).sum : ℝ) +
        ((w.length - 1) * us.length : ℕ) := by
  classical
  induction us with
  | nil => simp [badSubwords]
  | cons u us ih =>
      have ha := abs_occurrenceCount_append_sub_le w u us.flatten p hw
      have hL : 0 ≤ ε * (u.length : ℝ) := mul_nonneg hε (by positivity)
      by_cases hu : ε * (u.length : ℝ) <
          |(occurrenceCount w u : ℝ) - p * (u.length : ℝ)|
      · have he := abs_occurrenceCount_sub_le_length w u p hp hp1
        have hbad : badSubwords w p ε (u :: us) = u :: badSubwords w p ε us := by
          simp [badSubwords, hu]
        rw [hbad]
        simp only [List.flatten_cons, List.length_append, List.map_cons, List.sum_cons,
          List.length_cons, Nat.cast_add, Nat.mul_add, Nat.mul_one]
        simp only [List.length_append, Nat.cast_add] at ha
        nlinarith
      · have he := le_of_not_gt hu
        have hbad : badSubwords w p ε (u :: us) = badSubwords w p ε us := by
          simp [badSubwords, hu]
        rw [hbad]
        simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.cast_add,
          Nat.mul_add, Nat.mul_one]
        simp only [List.length_append, Nat.cast_add] at ha
        nlinarith

/-- Extending a positive-length prefix by `v` changes any pattern frequency by at most
twice the added length divided by the original length. -/
theorem abs_occurrenceFrequency_append_sub_le (w u v : List α) (hu : 0 < u.length) :
    |(occurrenceCount w (u ++ v) : ℝ) / ((u ++ v).length : ℝ) -
        (occurrenceCount w u : ℝ) / (u.length : ℝ)| ≤
      2 * (v.length : ℝ) / (u.length : ℝ) := by
  let L : ℝ := u.length
  let V : ℝ := v.length
  let a : ℝ := occurrenceCount w (u ++ v)
  let c : ℝ := occurrenceCount w u
  have hL : 0 < L := by dsimp [L]; exact_mod_cast hu
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc : c ≤ L := by
    dsimp [c, L]
    exact_mod_cast occurrenceCount_le_length w u
  have hlo : c ≤ a := by
    dsimp [c, a]
    exact_mod_cast occurrenceCount_le_append w u v
  have hhi : a ≤ c + V := by
    dsimp [c, a, V]
    exact_mod_cast occurrenceCount_append_le_add_length w u v
  have hsum : 0 < L + V := by linarith
  have hnum : |(a - c) * L - c * V| ≤ 2 * V * (L + V) := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hlo) hL.le,
        mul_le_mul_of_nonneg_right hc hV, sq_nonneg V]
    · nlinarith [mul_le_mul_of_nonneg_right (by linarith : a - c ≤ V) hL.le,
        mul_nonneg hc0 hV, sq_nonneg V]
  simp only [List.length_append, Nat.cast_add]
  change |a / (L + V) - c / L| ≤ 2 * V / L
  rw [show a / (L + V) - c / L =
      ((a - c) * L - c * V) / ((L + V) * L) by
    field_simp; ring]
  rw [abs_div, abs_of_pos (mul_pos hsum hL)]
  calc
    _ ≤ (2 * V * (L + V)) / ((L + V) * L) :=
      div_le_div_of_nonneg_right hnum (mul_pos hsum hL).le
    _ = 2 * V / L := by field_simp

end CopelandErdos.Words
