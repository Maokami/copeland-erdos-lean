module

public import CopelandErdos.Digits.BlockStream
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.NumberTheory.PrimeCounting

/-!
# The stream of digits of consecutive primes

`primeBlock b hb n` writes the zero-indexed `n`th prime in most-significant-first order.
The hypothesis `hb : 1 < b` excludes invalid bases explicitly. `primeDigits` is the actual
infinite concatenation of these blocks; its finite prefixes agree with finite list flattening.
-/

@[expose] public section

namespace CopelandErdos.Digits

/-- The digits of a positive prime, with the most significant digit first and each digit in
`Fin b`. The reversal is essential because `Nat.digits` is little endian. -/
noncomputable def primeBlock (b : ℕ) (hb : 1 < b) (n : ℕ) : List (Fin b) :=
  ((Nat.digits b (Nat.nth Nat.Prime n)).reverse).pmap
    (fun d hd ↦ ⟨d, hd⟩)
    (fun _ hd ↦ Nat.digits_lt_base hb (List.mem_reverse.mp hd))

theorem nth_prime_ne_zero (n : ℕ) : Nat.nth Nat.Prime n ≠ 0 :=
  (Nat.prime_nth_prime n).ne_zero

@[simp] theorem map_val_primeBlock (b : ℕ) (hb : 1 < b) (n : ℕ) :
    (primeBlock b hb n).map Fin.val = (Nat.digits b (Nat.nth Nat.Prime n)).reverse := by
  simp [primeBlock, List.map_pmap, List.pmap_eq_map]

@[simp] theorem length_primeBlock (b : ℕ) (hb : 1 < b) (n : ℕ) :
    (primeBlock b hb n).length = (Nat.digits b (Nat.nth Nat.Prime n)).length := by
  simp [primeBlock]

theorem length_primeBlock_eq_log_add_one (b : ℕ) (hb : 1 < b) (n : ℕ) :
    (primeBlock b hb n).length = Nat.log b (Nat.nth Nat.Prime n) + 1 := by
  rw [length_primeBlock, Nat.length_digits b _ hb (nth_prime_ne_zero n)]

theorem length_primeBlock_pos (b : ℕ) (hb : 1 < b) (n : ℕ) :
    0 < (primeBlock b hb n).length := by
  rw [length_primeBlock_eq_log_add_one]
  omega

theorem primeBlock_ne_nil (b : ℕ) (hb : 1 < b) (n : ℕ) : primeBlock b hb n ≠ [] := by
  have := length_primeBlock_pos b hb n
  intro h
  simp [h] at this

/-- Each prime block has no leading zero in its written order. -/
theorem head_primeBlock_ne_zero (b : ℕ) (hb : 1 < b) (n : ℕ) :
    ((primeBlock b hb n).head (primeBlock_ne_nil b hb n)).val ≠ 0 := by
  simpa [primeBlock, List.head_pmap, List.head_reverse] using
    Nat.getLast_digit_ne_zero b (nth_prime_ne_zero n)

/-- Reading the written digits with `Nat.ofDigits` requires reversing back to little endian. -/
@[simp] theorem ofDigits_reverse_primeBlock (b : ℕ) (hb : 1 < b) (n : ℕ) :
    Nat.ofDigits b ((primeBlock b hb n).map Fin.val).reverse = Nat.nth Nat.Prime n := by
  simp [Nat.ofDigits_digits]

/-- Number of digits contributed by the first `n` consecutive primes, starting with 2. -/
noncomputable def cumulativeLength (b : ℕ) (hb : 1 < b) : ℕ → ℕ :=
  BlockStream.cumulativeLength (primeBlock b hb)

@[simp] theorem cumulativeLength_zero (b : ℕ) (hb : 1 < b) : cumulativeLength b hb 0 = 0 :=
  rfl

@[simp] theorem cumulativeLength_succ (b : ℕ) (hb : 1 < b) (n : ℕ) :
    cumulativeLength b hb (n + 1) = cumulativeLength b hb n + (primeBlock b hb n).length :=
  rfl

theorem cumulativeLength_strictMono (b : ℕ) (hb : 1 < b) :
    StrictMono (cumulativeLength b hb) :=
  BlockStream.cumulativeLength_strictMono _ (length_primeBlock_pos b hb)

theorem le_cumulativeLength (b : ℕ) (hb : 1 < b) (n : ℕ) :
    n ≤ cumulativeLength b hb n :=
  BlockStream.le_cumulativeLength _ (length_primeBlock_pos b hb) n

theorem existsUnique_primeBlock (b : ℕ) (hb : 1 < b) (i : ℕ) :
    ∃! n, cumulativeLength b hb n ≤ i ∧ i < cumulativeLength b hb (n + 1) :=
  BlockStream.existsUnique_block _ (length_primeBlock_pos b hb) i

/-- The actual infinite stream obtained by concatenating consecutive prime digit blocks. -/
noncomputable def primeDigits (b : ℕ) (hb : 1 < b) : ℕ → Fin b :=
  BlockStream.stream (primeBlock b hb) (length_primeBlock_pos b hb)

theorem primeDigits_at_block (b : ℕ) (hb : 1 < b) (n j : ℕ)
    (hj : j < (primeBlock b hb n).length) :
    primeDigits b hb (cumulativeLength b hb n + j) = (primeBlock b hb n)[j] :=
  BlockStream.stream_at_block _ (length_primeBlock_pos b hb) n j hj

/-- The first `n` primes written consecutively, retaining all digits in their written order. -/
noncomputable def primePrefix (b : ℕ) (hb : 1 < b) (n : ℕ) : List (Fin b) :=
  ((List.range n).map (primeBlock b hb)).flatten

@[simp] theorem primePrefix_zero (b : ℕ) (hb : 1 < b) : primePrefix b hb 0 = [] := rfl

@[simp] theorem primePrefix_succ (b : ℕ) (hb : 1 < b) (n : ℕ) :
    primePrefix b hb (n + 1) = primePrefix b hb n ++ primeBlock b hb n :=
  BlockStream.finitePrefix_succ _ n

@[simp] theorem length_primePrefix (b : ℕ) (hb : 1 < b) (n : ℕ) :
    (primePrefix b hb n).length = cumulativeLength b hb n :=
  BlockStream.length_finitePrefix _ n

/-- Exact equality of digit lists at every prime boundary. -/
theorem ofFn_primeDigits_cumulativeLength (b : ℕ) (hb : 1 < b) (n : ℕ) :
    List.ofFn (fun i : Fin (cumulativeLength b hb n) ↦ primeDigits b hb i) =
      primePrefix b hb n :=
  BlockStream.ofFn_stream_cumulativeLength _ (length_primeBlock_pos b hb) n

/-- The first five primes are written as the ordinary decimal word `235711`. -/
theorem map_val_primePrefix_five :
    (primePrefix 10 (by decide) 5).map Fin.val = [2, 3, 5, 7, 1, 1] := by
  simp only [primePrefix_succ, primePrefix_zero, List.map_append, map_val_primeBlock,
    Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
    Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]
  decide

theorem cumulativeLength_ten_five : cumulativeLength 10 (by decide) 5 = 6 := by
  have h := congrArg List.length map_val_primePrefix_five
  simpa only [List.length_map, length_primePrefix, List.length_cons, List.length_nil] using h

/-- The first six digits of the infinite decimal stream are `235711`. -/
theorem ofFn_primeDigits_six :
    List.ofFn (fun i : Fin 6 ↦ (primeDigits 10 (by decide) i).val) =
      [2, 3, 5, 7, 1, 1] := by
  have h := congrArg (List.map Fin.val)
    (ofFn_primeDigits_cumulativeLength 10 (by decide) 5)
  simpa [List.map_ofFn, cumulativeLength_ten_five, map_val_primePrefix_five] using h

end CopelandErdos.Digits
