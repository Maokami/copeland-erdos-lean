module

public import CopelandErdos.Words.Occurrences
public import Mathlib.Data.List.OfFn
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

import all CopelandErdos.Words.Occurrences

/-!
# Normal digit streams

Normality uses every overlapping occurrence of every nonempty pattern in the actual first
`M` digits, with the full prefix length as denominator. Each digit of a normal stream recurs
arbitrarily far out; consequently every tail contains a positive and a nonmaximal digit.
-/

public section

open Filter
open scoped Topology

namespace CopelandErdos.Normality

/-- Every nonempty digit pattern has its uniform overlapping frequency in the full stream. -/
@[expose] def NormalDigits {b : ℕ} (d : ℕ → Fin b) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ w : Fin k → Fin b,
    Tendsto (fun M ↦ (Words.occurrenceCount (List.ofFn w)
      (List.ofFn (fun i : Fin M ↦ d i)) : ℝ) / (M : ℝ))
      atTop (𝓝 (1 / (b : ℝ) ^ k))

/-- If `c` never appears at or after `N`, at most `N` singleton occurrences appear in any
finite prefix. No eventual-frequency assumption is used in this finite estimate. -/
theorem occurrenceCount_singleton_prefix_le_of_eventually_ne
    {α : Type*} [DecidableEq α] (d : ℕ → α) (c : α) (N : ℕ)
    (h : ∀ j, N ≤ j → d j ≠ c) (M : ℕ) :
    Words.occurrenceCount [c] (List.ofFn (fun i : Fin M ↦ d i)) ≤ N := by
  rw [Words.occurrenceCount_eq_card _ _ (by simp)]
  calc
    _ ≤ (Finset.range N).card := by
      apply Finset.card_le_card
      intro i hi
      obtain ⟨hiM, hocc⟩ := Finset.mem_filter.mp hi
      have hiM' : i < M := by simpa only [Finset.mem_range, List.length_ofFn] using hiM
      have heq := congrArg (fun xs : List α ↦ xs[0]?) hocc.2
      have hd : d i = c := by
        simpa [List.getElem?_take_of_lt, List.getElem?_drop, List.getElem?_ofFn, hiM']
          using heq
      apply Finset.mem_range.mpr
      by_contra hiN
      exact h i (by omega) hd
    _ = N := Finset.card_range N

/-- A digit that disappears from some tail has limiting singleton frequency zero. -/
theorem tendsto_singleton_frequency_zero_of_eventually_ne
    {α : Type*} [DecidableEq α] (d : ℕ → α) (c : α) (N : ℕ)
    (h : ∀ j, N ≤ j → d j ≠ c) :
    Tendsto (fun M ↦ (Words.occurrenceCount [c]
      (List.ofFn (fun i : Fin M ↦ d i)) : ℝ) / (M : ℝ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun M : ℕ ↦ (N : ℝ) / (M : ℝ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ ↦ (M : ℝ)) atTop atTop).const_div_atTop _
  refine squeeze_zero (fun M ↦ div_nonneg (by positivity) (by positivity)) (fun M ↦ ?_) hN
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast occurrenceCount_singleton_prefix_le_of_eventually_ne d c N h M

/-- Every digit of a normal stream recurs beyond every prescribed index. -/
theorem normalDigits_recurs {b : ℕ} (hb : 1 < b) {d : ℕ → Fin b}
    (hd : NormalDigits d) (c : Fin b) (N : ℕ) : ∃ j, N ≤ j ∧ d j = c := by
  by_contra hnone
  have hne : ∀ j, N ≤ j → d j ≠ c := by
    intro j hj heq
    exact hnone ⟨j, hj, heq⟩
  have hz := tendsto_singleton_frequency_zero_of_eventually_ne d c N hne
  have hn : Tendsto (fun M ↦ (Words.occurrenceCount [c]
      (List.ofFn (fun i : Fin M ↦ d i)) : ℝ) / (M : ℝ)) atTop (𝓝 (1 / (b : ℝ))) := by
    simpa using hd 1 (by decide) (fun _ ↦ c)
  have heq := tendsto_nhds_unique hn hz
  have hpos : (0 : ℝ) < 1 / (b : ℝ) := by
    apply one_div_pos.mpr
    exact_mod_cast (by omega : 0 < b)
  rw [heq] at hpos
  exact (lt_irrefl 0) hpos

/-- A normal stream has a nonmaximal digit in every tail, witnessed by digit zero. -/
theorem normalDigits_exists_lt_last {b : ℕ} (hb : 1 < b) {d : ℕ → Fin b}
    (hd : NormalDigits d) : ∀ N, ∃ j, N ≤ j ∧ (d j).val < b - 1 := by
  intro N
  obtain ⟨j, hj, hdj⟩ := normalDigits_recurs hb hd ⟨0, by omega⟩ N
  refine ⟨j, hj, ?_⟩
  rw [hdj]
  change 0 < b - 1
  omega

/-- A normal stream has a positive digit in every tail, witnessed by digit one. -/
theorem normalDigits_exists_pos {b : ℕ} (hb : 1 < b) {d : ℕ → Fin b}
    (hd : NormalDigits d) : ∀ N, ∃ j, N ≤ j ∧ 0 < (d j).val := by
  intro N
  obtain ⟨j, hj, hdj⟩ := normalDigits_recurs hb hd ⟨1, hb⟩ N
  refine ⟨j, hj, ?_⟩
  rw [hdj]
  exact Nat.zero_lt_one

end CopelandErdos.Normality
