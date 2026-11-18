module

public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Monotone.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Infinite concatenation of nonempty finite blocks

Positions are located by the cumulative block lengths. Positivity of every block supplies an
explicit unboundedness bound, so this construction has no assumption about an existing stream.
-/

@[expose] public section

namespace CopelandErdos.Digits.BlockStream

variable {α : Type*}

/-- The length of the concatenation of the first `n` blocks. -/
def cumulativeLength (blocks : ℕ → List α) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cumulativeLength blocks n + (blocks n).length

@[simp] theorem cumulativeLength_zero (blocks : ℕ → List α) :
    cumulativeLength blocks 0 = 0 := rfl

@[simp] theorem cumulativeLength_succ (blocks : ℕ → List α) (n : ℕ) :
    cumulativeLength blocks (n + 1) = cumulativeLength blocks n + (blocks n).length := rfl

variable (blocks : ℕ → List α) (hblocks : ∀ n, 0 < (blocks n).length)

include hblocks in
theorem cumulativeLength_strictMono : StrictMono (cumulativeLength blocks) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [cumulativeLength_succ]
  have := hblocks n
  omega

include hblocks in
theorem le_cumulativeLength (n : ℕ) : n ≤ cumulativeLength blocks n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cumulativeLength_succ]
    have := hblocks n
    omega

include hblocks in
/-- Every position occurs before some block boundary. -/
theorem exists_lt_cumulativeLength (i : ℕ) : ∃ n, i < cumulativeLength blocks (n + 1) :=
  ⟨i, Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (le_cumulativeLength blocks hblocks (i + 1))⟩

/-- The unique block containing a zero-indexed position. -/
def blockIndex (i : ℕ) : ℕ := Nat.find (exists_lt_cumulativeLength blocks hblocks i)

theorem lt_cumulativeLength_blockIndex_succ (i : ℕ) :
    i < cumulativeLength blocks (blockIndex blocks hblocks i + 1) :=
  Nat.find_spec (exists_lt_cumulativeLength blocks hblocks i)

theorem cumulativeLength_blockIndex_le (i : ℕ) :
    cumulativeLength blocks (blockIndex blocks hblocks i) ≤ i := by
  generalize hn : blockIndex blocks hblocks i = n
  cases n with
  | zero => simp
  | succ n =>
    apply Nat.le_of_not_lt
    intro hi
    have hmin := Nat.find_min (exists_lt_cumulativeLength blocks hblocks i)
      (show n < blockIndex blocks hblocks i by omega)
    exact hmin hi

theorem blockIndex_eq_of_bounds {i n : ℕ}
    (hlo : cumulativeLength blocks n ≤ i)
    (hhi : i < cumulativeLength blocks (n + 1)) : blockIndex blocks hblocks i = n := by
  have hmono := cumulativeLength_strictMono blocks hblocks
  have hl := cumulativeLength_blockIndex_le blocks hblocks i
  have hu := lt_cumulativeLength_blockIndex_succ blocks hblocks i
  apply Nat.le_antisymm
  · by_contra! h
    have hh : cumulativeLength blocks (n + 1) ≤
        cumulativeLength blocks (blockIndex blocks hblocks i) :=
      hmono.monotone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hh.trans hl)) hhi
  · by_contra! h
    have hh : cumulativeLength blocks (blockIndex blocks hblocks i + 1) ≤
        cumulativeLength blocks n := hmono.monotone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hh.trans hlo)) hu

include hblocks in
/-- Every index belongs to exactly one half-open block interval. -/
theorem existsUnique_block (i : ℕ) :
    ∃! n, cumulativeLength blocks n ≤ i ∧ i < cumulativeLength blocks (n + 1) := by
  refine ⟨blockIndex blocks hblocks i,
    ⟨cumulativeLength_blockIndex_le blocks hblocks i,
      lt_cumulativeLength_blockIndex_succ blocks hblocks i⟩, ?_⟩
  intro n hn
  exact (blockIndex_eq_of_bounds blocks hblocks hn.1 hn.2).symm

/-- The infinite digit stream obtained by writing each block in its list order. -/
def stream (i : ℕ) : α :=
  (blocks (blockIndex blocks hblocks i))[i - cumulativeLength blocks
    (blockIndex blocks hblocks i)]'(by
      have hl := cumulativeLength_blockIndex_le blocks hblocks i
      have hu := lt_cumulativeLength_blockIndex_succ blocks hblocks i
      rw [cumulativeLength_succ] at hu
      omega)

/-- Indexed lookup inside a block agrees exactly with the concatenated stream. -/
theorem stream_at_block (n j : ℕ) (hj : j < (blocks n).length) :
    stream blocks hblocks (cumulativeLength blocks n + j) = (blocks n)[j] := by
  have hi : blockIndex blocks hblocks (cumulativeLength blocks n + j) = n := by
    apply blockIndex_eq_of_bounds blocks hblocks
    · omega
    · rw [cumulativeLength_succ]
      omega
  simp [stream, hi]

/-- The finite concatenation of the first `n` blocks, using `flatten` in chronological order. -/
def finitePrefix (n : ℕ) : List α := ((List.range n).map blocks).flatten

@[simp] theorem finitePrefix_zero : finitePrefix blocks 0 = [] := rfl

@[simp] theorem finitePrefix_succ (n : ℕ) :
    finitePrefix blocks (n + 1) = finitePrefix blocks n ++ blocks n := by
  simp [finitePrefix, List.range_succ]

@[simp] theorem length_finitePrefix (n : ℕ) :
    (finitePrefix blocks n).length = cumulativeLength blocks n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/-- At every block boundary, the stream prefix is the actual finite concatenation. -/
theorem ofFn_stream_cumulativeLength (n : ℕ) :
    List.ofFn (fun i : Fin (cumulativeLength blocks n) ↦ stream blocks hblocks i) =
      finitePrefix blocks n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cumulativeLength_succ, List.ofFn_add, finitePrefix_succ]
    apply congrArg₂ (fun u v : List α ↦ u ++ v)
    · exact ih
    · trans List.ofFn (fun j : Fin (blocks n).length ↦ (blocks n)[j])
      · congr 1
        funext j
        exact stream_at_block blocks hblocks n j j.isLt
      · exact List.ofFn_getElem

end CopelandErdos.Digits.BlockStream
