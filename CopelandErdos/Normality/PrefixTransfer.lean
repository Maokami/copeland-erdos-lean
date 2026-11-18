module

public import CopelandErdos.Digits.BlockStream
public import CopelandErdos.Words.Concatenation
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Transfer from block boundaries to arbitrary prefixes

This generic interpolation theorem is conditional on boundary-frequency convergence and on
the next block being negligible relative to the preceding blocks. Its conclusion concerns the
actual stream constructed by `BlockStream.stream`, including prefixes ending inside a block.
-/

public section

open Filter
open scoped Topology
open CopelandErdos.Digits.BlockStream

namespace CopelandErdos.Normality

variable {α : Type*}

/-- The block containing position `M` eventually lies beyond every fixed block. -/
theorem blockIndex_tendsto_atTop (blocks : ℕ → List α)
    (hblocks : ∀ n, 0 < (blocks n).length) :
    Tendsto (blockIndex blocks hblocks) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro n
  refine ⟨cumulativeLength blocks n, ?_⟩
  intro M hM
  have hhi := lt_cumulativeLength_blockIndex_succ blocks hblocks M
  have hmono := (cumulativeLength_strictMono blocks hblocks).monotone
  by_contra hn
  have hle : blockIndex blocks hblocks M + 1 ≤ n := by omega
  have := hmono hle
  omega

/-- An actual stream prefix is the complete preceding blocks followed by an initial segment
of the block containing its endpoint. -/
theorem ofFn_stream_eq_finitePrefix_append_take (blocks : ℕ → List α)
    (hblocks : ∀ n, 0 < (blocks n).length) (M : ℕ) :
    List.ofFn (fun i : Fin M ↦ stream blocks hblocks i) =
      finitePrefix blocks (blockIndex blocks hblocks M) ++
        (blocks (blockIndex blocks hblocks M)).take
          (M - cumulativeLength blocks (blockIndex blocks hblocks M)) := by
  let n := blockIndex blocks hblocks M
  have hlo := cumulativeLength_blockIndex_le blocks hblocks M
  have hhi := lt_cumulativeLength_blockIndex_succ blocks hblocks M
  change cumulativeLength blocks n ≤ M at hlo
  change M < cumulativeLength blocks (n + 1) at hhi
  rw [cumulativeLength_succ] at hhi
  have hrem : M - cumulativeLength blocks n < (blocks n).length := by omega
  have hsum : cumulativeLength blocks n + (M - cumulativeLength blocks n) = M := by omega
  have hsplit := List.ofFn_congr hsum
    (fun i : Fin (cumulativeLength blocks n + (M - cumulativeLength blocks n)) ↦
      stream blocks hblocks i)
  have htail :
      List.ofFn (fun j : Fin (M - cumulativeLength blocks n) ↦
        stream blocks hblocks (cumulativeLength blocks n + j)) =
      (blocks n).take (M - cumulativeLength blocks n) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_take]
      omega
    · intro j hj hj'
      simp only [List.length_ofFn] at hj
      simp only [List.getElem_ofFn, List.getElem_take]
      exact stream_at_block blocks hblocks n j (by omega)
  have hs : List.ofFn (fun i : Fin M ↦ stream blocks hblocks i) =
      List.ofFn (fun i : Fin (cumulativeLength blocks n) ↦ stream blocks hblocks i) ++
        List.ofFn (fun j : Fin (M - cumulativeLength blocks n) ↦
          stream blocks hblocks (cumulativeLength blocks n + j)) := by
    simpa only [List.ofFn_add, Fin.val_cast, Fin.val_castLE, Fin.val_natAdd] using hsplit.symm
  rw [hs, ofFn_stream_cumulativeLength, htail]

variable [DecidableEq α]

/-- The interpolation error is bounded by twice the next block's relative length. -/
theorem abs_prefixFrequency_sub_boundary_le (blocks : ℕ → List α)
    (hblocks : ∀ n, 0 < (blocks n).length) (w : List α) (M : ℕ)
    (hn : 0 < blockIndex blocks hblocks M) :
    |(Words.occurrenceCount w (List.ofFn (fun i : Fin M ↦ stream blocks hblocks i)) : ℝ) /
        (M : ℝ) -
      (Words.occurrenceCount w (finitePrefix blocks (blockIndex blocks hblocks M)) : ℝ) /
        (cumulativeLength blocks (blockIndex blocks hblocks M) : ℝ)| ≤
      2 * ((blocks (blockIndex blocks hblocks M)).length : ℝ) /
        (cumulativeLength blocks (blockIndex blocks hblocks M) : ℝ) := by
  let n := blockIndex blocks hblocks M
  let v := (blocks n).take (M - cumulativeLength blocks n)
  have hT : 0 < cumulativeLength blocks n :=
    hn.trans_le (le_cumulativeLength blocks hblocks n)
  have hpref : 0 < (finitePrefix blocks n).length := by
    simpa only [length_finitePrefix] using hT
  have he := Words.abs_occurrenceFrequency_append_sub_le w (finitePrefix blocks n) v hpref
  have hsplit : List.ofFn (fun i : Fin M ↦ stream blocks hblocks i) =
      finitePrefix blocks n ++ v := ofFn_stream_eq_finitePrefix_append_take blocks hblocks M
  rw [← hsplit] at he
  simp only [List.length_ofFn, length_finitePrefix] at he
  apply he.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hv : v.length ≤ (blocks n).length := by
    dsimp [v]
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  exact_mod_cast hv

/-- Boundary convergence transfers to every actual stream prefix when the next block's
length divided by the preceding cumulative length tends to zero. -/
theorem tendsto_prefixFrequency_of_boundary (blocks : ℕ → List α)
    (hblocks : ∀ n, 0 < (blocks n).length) (w : List α) (p : ℝ)
    (hboundary : Tendsto
      (fun n ↦ (Words.occurrenceCount w (finitePrefix blocks n) : ℝ) /
        (cumulativeLength blocks n : ℝ)) atTop (𝓝 p))
    (hsmall : Tendsto
      (fun n ↦ ((blocks n).length : ℝ) / (cumulativeLength blocks n : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun M ↦ (Words.occurrenceCount w
        (List.ofFn (fun i : Fin M ↦ stream blocks hblocks i)) : ℝ) / (M : ℝ))
      atTop (𝓝 p) := by
  let f : ℕ → ℝ := fun M ↦ (Words.occurrenceCount w
    (List.ofFn (fun i : Fin M ↦ stream blocks hblocks i)) : ℝ) / (M : ℝ)
  let g : ℕ → ℝ := fun M ↦
    (Words.occurrenceCount w (finitePrefix blocks (blockIndex blocks hblocks M)) : ℝ) /
      (cumulativeLength blocks (blockIndex blocks hblocks M) : ℝ)
  have hindex := blockIndex_tendsto_atTop blocks hblocks
  have hg : Tendsto g atTop (𝓝 p) := hboundary.comp hindex
  have hq : Tendsto
      (fun M ↦ 2 * ((blocks (blockIndex blocks hblocks M)).length : ℝ) /
        (cumulativeLength blocks (blockIndex blocks hblocks M) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, mul_div_assoc] using
      (hsmall.comp hindex).const_mul 2
  have habs : Tendsto (fun M ↦ |f M - g M|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun M ↦ abs_nonneg (f M - g M))) _ hq
    filter_upwards [hindex.eventually (eventually_ge_atTop 1)] with M hM
    exact abs_prefixFrequency_sub_boundary_le blocks hblocks w M (by omega)
  have hdiff : Tendsto (fun M ↦ f M - g M) atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq, sub_zero] using habs
  simpa only [sub_add_cancel, zero_add] using hdiff.add hg

end CopelandErdos.Normality
