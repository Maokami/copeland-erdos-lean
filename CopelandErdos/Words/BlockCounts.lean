module

public import CopelandErdos.Words.Occurrences
public import CopelandErdos.Words.UniformBlocks
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fintype.BigOperators

import all CopelandErdos.Words.Occurrences
import all CopelandErdos.Probability.FiniteMoments

/-!
# Residue groups of overlapping word occurrences

Starts of windows of length `k` are separated by their residue modulo `k`. Within one
group the selected coordinates are distinct. Summing the group counts recovers the existing
overlapping `occurrenceCount` exactly.
-/

@[expose] public section

open scoped BigOperators
open Finset
open CopelandErdos.Probability

namespace CopelandErdos.Words

variable {α : Type*} {k ℓ : ℕ}

/-- The number of complete length-`k` blocks starting in residue class `r`. -/
def blockMultiplicity (ℓ k r : ℕ) : ℕ := (ℓ - r) / k

theorem block_end_le (hk : 0 < k) (r : Fin k)
    (j : Fin (blockMultiplicity ℓ k r)) : r.val + j.val * k + k ≤ ℓ := by
  have h := (Nat.le_div_iff_mul_le hk).1 (Nat.succ_le_iff.2 j.isLt)
  change (j.val + 1) * k ≤ ℓ - r.val at h
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

/-- The coordinates of block `j` in residue group `r`. -/
def blockPosition (hk : 0 < k) (r : Fin k)
    (p : Fin (blockMultiplicity ℓ k r) × Fin k) : Fin ℓ :=
  ⟨r.val + p.1.val * k + p.2.val, by
    have := block_end_le hk r p.1
    omega⟩

theorem blockPosition_injective (hk : 0 < k) (r : Fin k) :
    Function.Injective (blockPosition (ℓ := ℓ) hk r) := by
  intro p q h
  have hv := congrArg Fin.val h
  change r.val + p.1.val * k + p.2.val = r.val + q.1.val * k + q.2.val at hv
  have hcancel : p.1.val * k + p.2.val = q.1.val * k + q.2.val := by omega
  have ht := congrArg (fun n ↦ n % k) hcancel
  simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
    Nat.mod_eq_of_lt p.2.isLt, Nat.mod_eq_of_lt q.2.isLt] at ht
  have hj : p.1.val = q.1.val := by
    have hm : p.1.val * k = q.1.val * k := by omega
    exact Nat.eq_of_mul_eq_mul_right hk hm
  exact Prod.ext (Fin.ext hj) (Fin.ext ht)

/-- Extract the disjoint blocks of a fixed residue group from the full word. -/
def residueBlocks (hk : 0 < k) (r : Fin k) (u : Fin ℓ → α) :
    Fin (blockMultiplicity ℓ k r) → (Fin k → α) :=
  fun j t ↦ u (blockPosition hk r (j, t))

/-- The number of matching blocks in one residue group. -/
noncomputable def residueCount [DecidableEq α] (hk : 0 < k) (w : Fin k → α)
    (u : Fin ℓ → α) (r : Fin k) : ℕ :=
  ∑ j, if residueBlocks hk r u j = w then 1 else 0

/-- Reassemble valid starts from their residue and quotient. -/
def residueStartEquiv (hk : 0 < k) (hℓ : k ≤ ℓ) :
    (Σ r : Fin k, Fin (blockMultiplicity ℓ k r)) ≃ Fin (ℓ - k + 1) where
  toFun p := ⟨p.1.val + p.2.val * k, by
    have := block_end_le hk p.1 p.2
    omega⟩
  invFun i := ⟨⟨i.val % k, Nat.mod_lt _ hk⟩,
    ⟨i.val / k, by
      change i.val / k < (ℓ - i.val % k) / k
      apply Nat.lt_of_succ_le
      apply (Nat.le_div_iff_mul_le hk).2
      have hm := Nat.mod_add_div i.val k
      have hi := i.isLt
      rw [Nat.succ_mul]
      rw [Nat.mul_comm k] at hm
      omega⟩⟩
  left_inv p := by
    obtain ⟨r, j⟩ := p
    have hr : (r.val + j.val * k) % k = r.val := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt r.isLt]
    have hj : (r.val + j.val * k) / k = j.val := by
      rw [Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt r.isLt, Nat.zero_add]
    apply Sigma.ext (Fin.ext hr)
    exact (Fin.heq_ext_iff (by simp only [hr])).2 hj
  right_inv i := by
    apply Fin.ext
    simpa [Nat.mul_comm] using Nat.mod_add_div i.val k

theorem sum_blockMultiplicity (hk : 0 < k) (hℓ : k ≤ ℓ) :
    ∑ r : Fin k, blockMultiplicity ℓ k r = ℓ - k + 1 := by
  have h := Fintype.card_congr (residueStartEquiv hk hℓ)
  simpa [Fintype.card_sigma] using h

theorem blockMultiplicity_le (r : Fin k) : blockMultiplicity ℓ k r ≤ ℓ :=
  (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem ofFn_window (u : Fin ℓ → α) (i : ℕ) (hi : i + k ≤ ℓ) :
    ((List.ofFn u).drop i).take k =
      List.ofFn (fun t : Fin k ↦ u ⟨i + t.val, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro t ht ht'
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem occursAt_ofFn_iff [DecidableEq α] (hk : 0 < k) (w : Fin k → α)
    (u : Fin ℓ → α) (r : Fin k) (j : Fin (blockMultiplicity ℓ k r)) :
    OccursAt (List.ofFn w) (List.ofFn u) (r.val + j.val * k) ↔
      residueBlocks hk r u j = w := by
  have he := block_end_le (ℓ := ℓ) hk r j
  simp only [OccursAt, List.length_ofFn, he, true_and]
  rw [ofFn_window u _ he, List.ofFn_inj]
  rfl

/-- Every overlapping occurrence is in exactly one residue group. -/
theorem occurrenceCount_eq_sum_residueCount [DecidableEq α] (hk : 0 < k)
    (hℓ : k ≤ ℓ) (w : Fin k → α) (u : Fin ℓ → α) :
    occurrenceCount (List.ofFn w) (List.ofFn u) = ∑ r, residueCount hk w u r := by
  have hw : List.ofFn w ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at this
    omega
  let f : ℕ → ℕ := occurrenceIndicator (List.ofFn w) (List.ofFn u)
  have hzero (i : ℕ) (hi : i ∈ Finset.range ℓ)
      (hi' : i ∉ Finset.range (ℓ - k + 1)) : f i = 0 := by
    simp only [Finset.mem_range, not_lt] at hi hi'
    have hn : ¬ OccursAt (List.ofFn w) (List.ofFn u) i := by
      simp only [OccursAt, List.length_ofFn]
      omega
    simp [f, occurrenceIndicator, hn]
  calc
    _ = ∑ i ∈ Finset.range ℓ, f i := by simp [occurrenceCount, hw, f]
    _ = ∑ i ∈ Finset.range (ℓ - k + 1), f i := by
      exact (Finset.sum_subset (Finset.range_mono (by omega)) hzero).symm
    _ = ∑ i : Fin (ℓ - k + 1), f i.val := (Fin.sum_univ_eq_sum_range f _).symm
    _ = ∑ p : (Σ r : Fin k, Fin (blockMultiplicity ℓ k r)),
        f ((residueStartEquiv hk hℓ) p).val :=
      (Equiv.sum_comp (residueStartEquiv hk hℓ) (fun i ↦ f i.val)).symm
    _ = ∑ r : Fin k, residueCount hk w u r := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro j _
      change (if OccursAt (List.ofFn w) (List.ofFn u) (r.val + j.val * k) then 1 else 0) =
        (if residueBlocks hk r u j = w then 1 else 0)
      simp only [occursAt_ofFn_iff hk w u r j]

variable [Fintype α] [Nonempty α] [DecidableEq α]

/-- The centered count of a residue group in the full uniform word space. -/
noncomputable def residueDeviation (hk : 0 < k) (w : Fin k → α)
    (u : Fin ℓ → α) (r : Fin k) : ℝ :=
  (residueCount hk w u r : ℝ) -
    (blockMultiplicity ℓ k r : ℝ) / Fintype.card (Fin k → α)

omit [Nonempty α] in
theorem residueDeviation_eq_coordinateSum (hk : 0 < k) (w : Fin k → α)
    (u : Fin ℓ → α) (r : Fin k) :
    residueDeviation hk w u r = coordinateSum (centeredIndicator w)
      (blockMultiplicity ℓ k r) (residueBlocks hk r u) := by
  simp [residueDeviation, residueCount, coordinateSum, centeredIndicator,
    Finset.sum_sub_distrib, div_eq_mul_inv]

omit [DecidableEq α] in
/-- The selected disjoint blocks have the exact uniform product distribution. -/
theorem uniformMean_residueBlocks (hk : 0 < k) (r : Fin k)
    (g : (Fin (blockMultiplicity ℓ k r) → (Fin k → α)) → ℝ) :
    uniformMean (fun u : Fin ℓ → α ↦ g (residueBlocks hk r u)) = uniformMean g := by
  calc
    _ = uniformMean (fun v : (Fin (blockMultiplicity ℓ k r) × Fin k) → α ↦
        g (Function.curry v)) := by
      have hb (u : Fin ℓ → α) :
          residueBlocks hk r u = Function.curry (u ∘ blockPosition hk r) := rfl
      simp_rw [hb]
      exact uniformMean_restrict (blockPosition (ℓ := ℓ) hk r) (blockPosition_injective hk r)
          (fun v ↦ g (Function.curry v))
    _ = uniformMean g := by
      rw [uniformMean_eq_expect, uniformMean_eq_expect]
      exact Fintype.expect_equiv (Equiv.curry _ _ _) _ _ (fun _ ↦ rfl)

/-- Fourth moment of one residue count, proved on the actual full-word sample space.
The statement includes residue groups with no complete blocks. -/
theorem mean_residueDeviation_fourth_le (hk : 0 < k) (w : Fin k → α) (r : Fin k) :
    uniformMean (fun u : Fin ℓ → α ↦ residueDeviation hk w u r ^ 4) ≤
      3 * (blockMultiplicity ℓ k r : ℝ) ^ 2 := by
  simp_rw [residueDeviation_eq_coordinateSum]
  rw [uniformMean_residueBlocks hk r
    (fun x ↦ coordinateSum (centeredIndicator w) (blockMultiplicity ℓ k r) x ^ 4)]
  exact mean_coordinateSum_fourth_le (centeredIndicator w) (uniformMean_centeredIndicator w)
    (abs_centeredIndicator_le_one w) _

end CopelandErdos.Words
