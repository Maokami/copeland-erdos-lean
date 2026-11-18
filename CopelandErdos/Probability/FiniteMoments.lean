module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Moments of a bounded centered coordinate sum

All averages are uniform averages over actual finite sets. In particular, independence is
proved by separating a function on `Fin (m + 1)` into its head and tail, and factoring the
average over the resulting product. No probabilistic independence hypothesis is required.
-/

public section

open scoped BigOperators
open Finset

namespace CopelandErdos.Probability

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The uniform mean of a real-valued function on a finite type. -/
noncomputable def uniformMean (f : α → ℝ) : ℝ := 𝔼 x, f x

/-- The uniform mean is the finite sum divided by the size of the sample space. -/
theorem uniformMean_eq_sum_div_card (f : α → ℝ) :
    uniformMean f = (∑ x, f x) / Fintype.card α :=
  Fintype.expect_eq_sum_div_card f

@[simp] theorem uniformMean_zero : uniformMean (fun _ : α ↦ (0 : ℝ)) = 0 := by
  simp [uniformMean]

@[simp] theorem uniformMean_const [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α ↦ c) = c := Fintype.expect_const c

@[simp] theorem uniformMean_add (f g : α → ℝ) :
    uniformMean (fun x ↦ f x + g x) = uniformMean f + uniformMean g :=
  Finset.expect_add_distrib _ _ _

@[simp] theorem uniformMean_mul_left (c : ℝ) (f : α → ℝ) :
    uniformMean (fun x ↦ c * f x) = c * uniformMean f :=
  (Finset.mul_expect _ _ _).symm

@[simp] theorem uniformMean_mul_right (f : α → ℝ) (c : ℝ) :
    uniformMean (fun x ↦ f x * c) = uniformMean f * c :=
  (Finset.expect_mul _ _ _).symm

/-- Uniform averages factor on a product of two finite sample spaces. -/
theorem uniformMean_product (f : α → ℝ) (g : β → ℝ) :
    uniformMean (fun p : α × β ↦ f p.1 * g p.2) = uniformMean f * uniformMean g := by
  simp only [uniformMean, ← Finset.univ_product_univ, Finset.expect_product]
  exact (Fintype.expect_mul_expect f g).symm

/-- Splitting the head and tail of a finite coordinate sample preserves its uniform mean. -/
theorem uniformMean_succ (m : ℕ) (g : (Fin (m + 1) → α) → ℝ) :
    uniformMean g = uniformMean (fun a : α ↦
      uniformMean (fun x : Fin m → α ↦ g (Fin.cons a x))) := by
  unfold uniformMean
  rw [← Fintype.expect_equiv (Fin.consEquiv fun _ : Fin (m + 1) ↦ α)
    (fun p ↦ g (Fin.cons p.1 p.2)) g (fun _ ↦ rfl)]
  exact Finset.expect_product _ _ _

/-- The sum of the same coordinate observable on a sample of length `m`. -/
noncomputable def coordinateSum (f : α → ℝ) (m : ℕ) (x : Fin m → α) : ℝ :=
  ∑ i, f (x i)

omit [Fintype α] in
@[simp] theorem coordinateSum_zero (f : α → ℝ) (x : Fin 0 → α) :
    coordinateSum f 0 x = 0 := by simp [coordinateSum]

omit [Fintype α] in
@[simp] theorem coordinateSum_cons (f : α → ℝ) (m : ℕ) (a : α) (x : Fin m → α) :
    coordinateSum f (m + 1) (Fin.cons a x) = f a + coordinateSum f m x := by
  simp [coordinateSum, Fin.sum_univ_succ]

variable [Nonempty α]

/-- A centered observable has a centered sum on the finite uniform product space. -/
theorem mean_coordinateSum (f : α → ℝ) (hcenter : uniformMean f = 0) (m : ℕ) :
    uniformMean (coordinateSum f m) = 0 := by
  induction m with
  | zero => simp [uniformMean, coordinateSum]
  | succ m ih =>
    rw [uniformMean_succ]
    simp [ih, hcenter]

/-- Second moment on the finite uniform product space. -/
theorem mean_coordinateSum_sq (f : α → ℝ) (hcenter : uniformMean f = 0) (m : ℕ) :
    uniformMean (fun x ↦ coordinateSum f m x ^ 2) =
      (m : ℝ) * uniformMean (fun a ↦ f a ^ 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [uniformMean_succ]
    simp_rw [coordinateSum_cons]
    simp_rw [show ∀ a b : ℝ, (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 by
      intros; ring]
    simp [ih, mean_coordinateSum f hcenter, Nat.cast_add, Nat.cast_one]
    ring

/-- Exact fourth moment. The subtraction in `m - 1` takes place in `ℝ`, so the formula
also holds when `m = 0`. -/
theorem mean_coordinateSum_fourth (f : α → ℝ) (hcenter : uniformMean f = 0) (m : ℕ) :
    uniformMean (fun x ↦ coordinateSum f m x ^ 4) =
      (m : ℝ) * uniformMean (fun a ↦ f a ^ 4) +
        3 * (m : ℝ) * ((m : ℝ) - 1) * uniformMean (fun a ↦ f a ^ 2) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [uniformMean_succ]
    simp_rw [coordinateSum_cons]
    simp_rw [show ∀ a b : ℝ, (a + b) ^ 4 =
      a ^ 4 + 4 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 4 * a * b ^ 3 + b ^ 4 by
      intros; ring]
    simp [ih, mean_coordinateSum f hcenter, mean_coordinateSum_sq f hcenter,
      hcenter, Nat.cast_add, Nat.cast_one]
    ring

/-- The second moment of an observable bounded in absolute value by one is at most one. -/
theorem uniformMean_sq_le_one (f : α → ℝ) (hbound : ∀ a, |f a| ≤ 1) :
    uniformMean (fun a ↦ f a ^ 2) ≤ 1 := by
  exact Finset.expect_le Finset.univ_nonempty fun a _ ↦
    (sq_le_one_iff_abs_le_one (f a)).2 (hbound a)

/-- The fourth moment of an observable bounded in absolute value by one is at most one. -/
theorem uniformMean_fourth_le_one (f : α → ℝ) (hbound : ∀ a, |f a| ≤ 1) :
    uniformMean (fun a ↦ f a ^ 4) ≤ 1 := by
  apply Finset.expect_le Finset.univ_nonempty
  intro a _
  have h := pow_le_one₀ (abs_nonneg (f a)) (hbound a) (n := 4)
  simpa only [(by decide : Even 4).pow_abs] using h

/-- A uniform fourth-moment bound, including the empty coordinate sample. -/
theorem mean_coordinateSum_fourth_le (f : α → ℝ) (hcenter : uniformMean f = 0)
    (hbound : ∀ a, |f a| ≤ 1) (m : ℕ) :
    uniformMean (fun x ↦ coordinateSum f m x ^ 4) ≤ 3 * (m : ℝ) ^ 2 := by
  cases m with
  | zero => simp
  | succ m =>
    have hm : 1 ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    have hv0 : 0 ≤ uniformMean (fun a ↦ f a ^ 2) :=
      Finset.expect_nonneg fun _ _ ↦ sq_nonneg _
    have hv1 := uniformMean_sq_le_one f hbound
    have hv2 : uniformMean (fun a ↦ f a ^ 2) ^ 2 ≤ 1 := pow_le_one₀ hv0 hv1
    have hfourth := uniformMean_fourth_le_one f hbound
    have hc : 0 ≤ 3 * ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.2 hm)
    rw [mean_coordinateSum_fourth f hcenter]
    calc
      _ ≤ ((m + 1 : ℕ) : ℝ) * 1 +
          3 * ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hfourth (by positivity))
          (mul_le_mul_of_nonneg_left hv2 hc)
      _ ≤ 3 * (((m + 1 : ℕ) : ℝ)) ^ 2 := by nlinarith

/-- Finite Markov inequality in cardinality form, for an arbitrary event whose members
have observable value at least the positive threshold. -/
theorem uniformMean_card_le (g : α → ℝ) (hnonneg : ∀ a, 0 ≤ g a)
    (s : Finset α) (t : ℝ) (ht : 0 < t) (hlarge : ∀ a ∈ s, t ≤ g a) :
    (s.card : ℝ) / Fintype.card α ≤ uniformMean g / t := by
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : (s.card : ℝ) * t ≤ ∑ a, g a := by
    calc
      _ = ∑ _a ∈ s, t := by simp
      _ ≤ ∑ a ∈ s, g a := Finset.sum_le_sum hlarge
      _ ≤ ∑ a, g a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun a _ _ ↦ hnonneg a)
  apply (le_div_iff₀ ht).2
  rw [uniformMean_eq_sum_div_card, div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hc).2 hs

/-- The fourth-moment tail bound as a ratio of cardinalities in the finite product space. -/
theorem coordinateSum_tail_card_le (f : α → ℝ) (hcenter : uniformMean f = 0)
    (hbound : ∀ a, |f a| ≤ 1) (m : ℕ) (hm : 1 ≤ m) (η : ℝ) (hη : 0 < η) :
    ((Finset.univ.filter (fun x : Fin m → α ↦ η * (m : ℝ) < |coordinateSum f m x|)).card :
      ℝ) / Fintype.card (Fin m → α) ≤ 3 / (η ^ 4 * (m : ℝ) ^ 2) := by
  classical
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have ht : 0 < η ^ 4 * (m : ℝ) ^ 4 := by positivity
  calc
    _ ≤ uniformMean (fun x ↦ coordinateSum f m x ^ 4) / (η ^ 4 * (m : ℝ) ^ 4) := by
      apply uniformMean_card_le (fun x ↦ coordinateSum f m x ^ 4)
        (fun _ ↦ by positivity) _ _ ht
      intro x hx
      have hx' := (Finset.mem_filter.1 hx).2.le
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ η * (m : ℝ)) hx' 4
      simpa only [mul_pow, (by decide : Even 4).pow_abs] using hp
    _ ≤ (3 * (m : ℝ) ^ 2) / (η ^ 4 * (m : ℝ) ^ 4) :=
      div_le_div_of_nonneg_right (mean_coordinateSum_fourth_le f hcenter hbound m) ht.le
    _ = 3 / (η ^ 4 * (m : ℝ) ^ 2) := by
      field_simp

end CopelandErdos.Probability
