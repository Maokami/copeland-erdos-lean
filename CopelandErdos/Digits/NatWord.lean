module

public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Standard digit words of natural numbers

`natWord b hb a` writes `a` in base `b`, most significant digit first and without leading
zeroes. Zero is represented by the empty word, following `Nat.digits`.
-/

@[expose] public section

namespace CopelandErdos.Digits

/-- The standard most-significant-first base-`b` digits. Zero has the empty word. -/
noncomputable def natWord (b : ℕ) (hb : 1 < b) (a : ℕ) : List (Fin b) :=
  ((Nat.digits b a).reverse).pmap
    (fun d hd ↦ ⟨d, hd⟩)
    (fun _ hd ↦ Nat.digits_lt_base hb (List.mem_reverse.mp hd))

@[simp] theorem map_val_natWord (b : ℕ) (hb : 1 < b) (a : ℕ) :
    (natWord b hb a).map Fin.val = (Nat.digits b a).reverse := by
  simp [natWord, List.map_pmap, List.pmap_eq_map]

@[simp] theorem length_natWord (b : ℕ) (hb : 1 < b) (a : ℕ) :
    (natWord b hb a).length = (Nat.digits b a).length := by
  simp [natWord]

@[simp] theorem natWord_zero (b : ℕ) (hb : 1 < b) : natWord b hb 0 = [] := by
  simp [natWord]

/-- Evaluation reverses the written order because `Nat.ofDigits` is little endian. -/
@[simp] theorem ofDigits_reverse_natWord (b : ℕ) (hb : 1 < b) (a : ℕ) :
    Nat.ofDigits b ((natWord b hb a).map Fin.val).reverse = a := by
  simp [Nat.ofDigits_digits]

theorem natWord_injective (b : ℕ) (hb : 1 < b) : Function.Injective (natWord b hb) := by
  intro a c h
  have := congrArg (fun l : List (Fin b) ↦ Nat.ofDigits b (l.map Fin.val).reverse) h
  simpa only [ofDigits_reverse_natWord] using this

theorem length_natWord_eq_log_add_one (b : ℕ) (hb : 1 < b) (a : ℕ) (ha : a ≠ 0) :
    (natWord b hb a).length = Nat.log b a + 1 := by
  rw [length_natWord, Nat.length_digits b a hb ha]

theorem length_natWord_pos (b : ℕ) (hb : 1 < b) (a : ℕ) (ha : 0 < a) :
    0 < (natWord b hb a).length := by
  rw [length_natWord_eq_log_add_one b hb a (Nat.ne_of_gt ha)]
  omega

theorem natWord_ne_nil (b : ℕ) (hb : 1 < b) (a : ℕ) (ha : 0 < a) :
    natWord b hb a ≠ [] := by
  have := length_natWord_pos b hb a ha
  intro h
  simp [h] at this

/-- A positive integer has no leading zero in its written digit word. -/
theorem head_natWord_ne_zero (b : ℕ) (hb : 1 < b) (a : ℕ) (ha : 0 < a) :
    ((natWord b hb a).head (natWord_ne_nil b hb a ha)).val ≠ 0 := by
  simpa [natWord, List.head_pmap, List.head_reverse] using
    Nat.getLast_digit_ne_zero b (Nat.ne_of_gt ha)

/-- Regard an exact-length standard digit word as a point of the full finite word space. -/
noncomputable def natWordOfLength (b : ℕ) (hb : 1 < b) (a : ℕ) {ℓ : ℕ}
    (h : (natWord b hb a).length = ℓ) : Fin ℓ → Fin b :=
  fun i ↦ (natWord b hb a).get (Fin.cast h.symm i)

@[simp] theorem ofFn_natWordOfLength (b : ℕ) (hb : 1 < b) (a : ℕ) {ℓ : ℕ}
    (h : (natWord b hb a).length = ℓ) :
    List.ofFn (natWordOfLength b hb a h) = natWord b hb a := by
  subst ℓ
  change List.ofFn (natWord b hb a).get = _
  exact List.ofFn_get _

/-- Equality of the fixed-length encodings implies equality of the encoded integers. -/
theorem natWordOfLength_injective (b : ℕ) (hb : 1 < b) {ℓ a c : ℕ}
    (ha : (natWord b hb a).length = ℓ) (hc : (natWord b hb c).length = ℓ)
    (h : natWordOfLength b hb a ha = natWordOfLength b hb c hc) : a = c := by
  apply natWord_injective b hb
  have := congrArg List.ofFn h
  simpa using this

end CopelandErdos.Digits
