module

public import CopelandErdos.Normality.PrefixTransfer

/-!
# A generic criterion for boundary-frequency convergence

The criterion separates the finite concatenation estimate from the arithmetic needed to
control exceptional blocks. Its hypotheses are explicit: the number of boundaries and the
total length of bad blocks must be negligible relative to the cumulative length.
-/

public section

open Filter
open scoped Topology
open CopelandErdos.Digits.BlockStream

namespace CopelandErdos.Normality

variable {α : Type*} [DecidableEq α]

/-- The total length of bad blocks among the first `n` blocks, retaining multiplicity. -/
@[expose] noncomputable def badLength
    (blocks : ℕ → List α) (w : List α) (p ε : ℝ) (n : ℕ) : ℕ :=
  ((Words.badSubwords w p ε ((List.range n).map blocks)).map List.length).sum

/-- The normalized finite concatenation estimate at a positive block boundary. -/
theorem abs_boundaryFrequency_sub_le (blocks : ℕ → List α)
    (hblocks : ∀ n, 0 < (blocks n).length) (w : List α) (p ε : ℝ)
    (hw : w ≠ []) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) (n : ℕ) (hn : 0 < n) :
    |(Words.occurrenceCount w (finitePrefix blocks n) : ℝ) /
        (cumulativeLength blocks n : ℝ) - p| ≤
      ε + (badLength blocks w p ε n : ℝ) / (cumulativeLength blocks n : ℝ) +
        (w.length - 1 : ℕ) * ((n : ℝ) / (cumulativeLength blocks n : ℝ)) := by
  have hT : (0 : ℝ) < cumulativeLength blocks n := by
    exact_mod_cast hn.trans_le (le_cumulativeLength blocks hblocks n)
  have he := Words.abs_occurrenceCount_flatten_sub_le w ((List.range n).map blocks)
    p ε hw hp hp1 hε
  change |(Words.occurrenceCount w (finitePrefix blocks n) : ℝ) -
      p * ((finitePrefix blocks n).length : ℝ)| ≤
    ε * ((finitePrefix blocks n).length : ℝ) + (badLength blocks w p ε n : ℝ) +
      ((w.length - 1) * ((List.range n).map blocks).length : ℕ) at he
  simp only [length_finitePrefix, List.length_map, List.length_range, Nat.cast_mul] at he
  calc
    _ = |(Words.occurrenceCount w (finitePrefix blocks n) : ℝ) -
        p * (cumulativeLength blocks n : ℝ)| / (cumulativeLength blocks n : ℝ) := by
      rw [show (Words.occurrenceCount w (finitePrefix blocks n) : ℝ) /
          (cumulativeLength blocks n : ℝ) - p =
          ((Words.occurrenceCount w (finitePrefix blocks n) : ℝ) -
            p * (cumulativeLength blocks n : ℝ)) /
              (cumulativeLength blocks n : ℝ) by field_simp]
      rw [abs_div, abs_of_pos hT]
    _ ≤ (ε * (cumulativeLength blocks n : ℝ) + (badLength blocks w p ε n : ℝ) +
        (w.length - 1 : ℕ) * (n : ℝ)) / (cumulativeLength blocks n : ℝ) :=
      div_le_div_of_nonneg_right he hT.le
    _ = _ := by field_simp

/-- Boundary frequencies converge when both the boundary count and, at every positive
tolerance, the total bad-block length are negligible relative to cumulative length. -/
theorem tendsto_boundaryFrequency_of_badLength (blocks : ℕ → List α)
    (hblocks : ∀ n, 0 < (blocks n).length) (w : List α) (p : ℝ)
    (hw : w ≠ []) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hboundaryCount : Tendsto
      (fun n : ℕ ↦ (n : ℝ) / (cumulativeLength blocks n : ℝ)) atTop (𝓝 0))
    (hbad : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n ↦ (badLength blocks w p ε n : ℝ) / (cumulativeLength blocks n : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun n ↦ (Words.occurrenceCount w (finitePrefix blocks n) : ℝ) /
        (cumulativeLength blocks n : ℝ)) atTop (𝓝 p) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hhalf : 0 < δ / 2 := by positivity
  have hb : Tendsto
      (fun n : ℕ ↦ (w.length - 1 : ℕ) * ((n : ℝ) / (cumulativeLength blocks n : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hboundaryCount.const_mul ((w.length - 1 : ℕ) : ℝ)
  have htail := (hbad (δ / 2) hhalf).add hb
  have htailEvent := Metric.tendsto_nhds.mp htail (δ / 2) hhalf
  filter_upwards [htailEvent, eventually_ge_atTop 1] with n ht hn
  simp only [Real.dist_eq, zero_add, sub_zero] at ht ⊢
  have hbound := abs_boundaryFrequency_sub_le blocks hblocks w p (δ / 2)
    hw hp hp1 hhalf.le n (by omega)
  have htailLt := (le_abs_self _).trans_lt ht
  linarith

/-- The bad-length criterion and negligible next blocks imply convergence at every actual
stream prefix, including prefixes that end inside a block. -/
theorem tendsto_prefixFrequency_of_badLength (blocks : ℕ → List α)
    (hblocks : ∀ n, 0 < (blocks n).length) (w : List α) (p : ℝ)
    (hw : w ≠ []) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hboundaryCount : Tendsto
      (fun n : ℕ ↦ (n : ℝ) / (cumulativeLength blocks n : ℝ)) atTop (𝓝 0))
    (hbad : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n ↦ (badLength blocks w p ε n : ℝ) / (cumulativeLength blocks n : ℝ))
      atTop (𝓝 0))
    (hsmall : Tendsto
      (fun n ↦ ((blocks n).length : ℝ) / (cumulativeLength blocks n : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun M ↦ (Words.occurrenceCount w
        (List.ofFn (fun i : Fin M ↦ stream blocks hblocks i)) : ℝ) / (M : ℝ))
      atTop (𝓝 p) :=
  tendsto_prefixFrequency_of_boundary blocks hblocks w p
    (tendsto_boundaryFrequency_of_badLength blocks hblocks w p hw hp hp1 hboundaryCount hbad)
    hsmall

end CopelandErdos.Normality
