module

public import CopelandErdos.Probability.FiniteMoments
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Fintype.Pi

/-!
# Uniform restriction to distinct coordinates

Restriction of a uniformly chosen finite word to any injective family of positions is
uniform. The proof splits the unused coordinates off as a second finite product, rather
than postulating independence of the selected blocks.
-/

@[expose] public section

open scoped BigOperators
open Finset
open CopelandErdos.Probability

namespace CopelandErdos.Words

theorem uniformMean_eq_expect {β : Type*} [Fintype β] (f : β → ℝ) :
    uniformMean f = 𝔼 x, f x :=
  (uniformMean_eq_sum_div_card f).trans (Fintype.expect_eq_sum_div_card f).symm

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype α] [Nonempty α]

/-- Selecting pairwise distinct coordinates preserves the uniform average. -/
theorem uniformMean_restrict (e : κ → ι) (he : Function.Injective e)
    (g : (κ → α) → ℝ) :
    uniformMean (fun u : ι → α ↦ g (u ∘ e)) = uniformMean g := by
  classical
  let E : (ι → α) ≃ ((κ → α) × ({i : ι // i ∉ Set.range e} → α)) :=
    (Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ Set.range e) (fun _ ↦ α)).trans
      (Equiv.prodCongr
        (Equiv.arrowCongr (Equiv.ofInjective e he).symm (Equiv.refl α)) (Equiv.refl _))
  have hE (u : ι → α) : (E u).1 = u ∘ e := by
    funext j
    simp [E, Equiv.arrowCongr, Equiv.ofInjective]
  rw [uniformMean_eq_expect, uniformMean_eq_expect]
  rw [Fintype.expect_equiv E (fun u ↦ g (u ∘ e)) (fun p ↦ g p.1)
    (fun u ↦ by rw [hE])]
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp

/-- Restriction preserves the proportion of every event, in exact cardinality form. -/
theorem restrict_event_ratio (e : κ → ι) (he : Function.Injective e)
    (P : (κ → α) → Prop) [DecidablePred P] :
    (((Finset.univ.filter (fun u : ι → α ↦ P (u ∘ e))).card : ℝ) /
      Fintype.card (ι → α)) =
    (((Finset.univ.filter P).card : ℝ) / Fintype.card (κ → α)) := by
  classical
  have h := uniformMean_restrict e he (fun x ↦ if P x then (1 : ℝ) else 0)
  simp only [uniformMean_eq_sum_div_card, Finset.sum_boole] at h
  exact h

/-- The centered indicator of one element of a nonempty finite uniform sample space. -/
noncomputable def centeredIndicator [DecidableEq α] (w a : α) : ℝ :=
  (if a = w then 1 else 0) - 1 / Fintype.card α

@[simp] theorem uniformMean_centeredIndicator [DecidableEq α] (w : α) :
    uniformMean (centeredIndicator w) = 0 := by
  rw [uniformMean_eq_sum_div_card]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [centeredIndicator, Finset.sum_sub_distrib, hc]

theorem abs_centeredIndicator_le_one [DecidableEq α] (w a : α) :
    |centeredIndicator w a| ≤ 1 := by
  have hc : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hp0 : (0 : ℝ) ≤ 1 / Fintype.card α := by positivity
  have hp1 : (1 : ℝ) / Fintype.card α ≤ 1 := by
    exact (div_le_one (by positivity)).2 hc
  unfold centeredIndicator
  split <;> rw [abs_le] <;> constructor <;> linarith

end CopelandErdos.Words
