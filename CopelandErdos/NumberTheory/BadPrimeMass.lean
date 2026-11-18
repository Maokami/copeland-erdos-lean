module

public import CopelandErdos.NumberTheory.BadIntegerCounting
public import CopelandErdos.NumberTheory.PrimeDigitMass

/-!
# Negligible digit mass of exceptional primes

Primes up to the inclusive cutoff `Y` lie among the positive integers below `Y + 1`.
Each such prime has at most `log_b (Y + 1) + 1` digits. The proved exceptional-integer
bound therefore controls their total digit mass by `C (Y + 1) / (log_b (Y + 1) + 1)`.
The unconditional linear lower bound for all prime digits makes the relative mass vanish.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace CopelandErdos.NumberTheory

open CopelandErdos.Digits CopelandErdos.Words

variable {b k : ℕ}

/-- For a positive length, normalized frequency error is equivalent to the corresponding
unnormalized error threshold. No sign restriction on the target or tolerance is needed. -/
theorem normalized_bad_iff_mul (ε c p L : ℝ) (hL : 0 < L) :
    ε < |c / L - p| ↔ ε * L < |c - p * L| := by
  rw [show c / L - p = (c - p * L) / L by field_simp,
    abs_div, abs_of_pos hL]
  exact lt_div_iff₀ hL

/-- Exceptional primes at most `Y`, using actual standard digit lengths and overlapping
occurrences in the normalized frequency error. The prime cutoff is inclusive. -/
noncomputable def badPrimesLE (b : ℕ) (hb : 1 < b) (w : Fin k → Fin b)
    (ε : ℝ) (Y : ℕ) : Finset ℕ :=
  (Nat.primesLE Y).filter (fun p ↦
    ε < |(occurrenceCount (List.ofFn w) (natWord b hb p) : ℝ) /
      ((natWord b hb p).length : ℝ) - 1 / (b : ℝ) ^ k|)

@[simp] theorem mem_badPrimesLE (hb : 1 < b) (w : Fin k → Fin b) (ε : ℝ)
    (Y p : ℕ) :
    p ∈ badPrimesLE b hb w ε Y ↔ p ≤ Y ∧ p.Prime ∧
      ε < |(occurrenceCount (List.ofFn w) (natWord b hb p) : ℝ) /
        ((natWord b hb p).length : ℝ) - 1 / (b : ℝ) ^ k| := by
  classical
  simp [badPrimesLE, Nat.mem_primesLE, and_assoc]

/-- The total digit length of the exceptional primes at the inclusive cutoff `Y`. -/
noncomputable def badPrimeMass (b : ℕ) (hb : 1 < b) (w : Fin k → Fin b)
    (ε : ℝ) (Y : ℕ) : ℕ :=
  ∑ p ∈ badPrimesLE b hb w ε Y, (natWord b hb p).length

theorem badPrimesLE_subset_badIntegersBelow (hb : 1 < b) (w : Fin k → Fin b)
    (ε : ℝ) (Y : ℕ) :
    badPrimesLE b hb w ε Y ⊆ badIntegersBelow b hb w ε (Y + 1) := by
  intro p hp
  rcases (mem_badPrimesLE hb w ε Y p).1 hp with ⟨hpY, hp, hbad⟩
  exact (mem_badIntegersBelow hb w ε (Y + 1) p).2 ⟨by omega, hp.pos, hbad⟩

/-- Bound each exceptional prime length by the common digit-length cutoff and inject
the exceptional prime set into the exceptional integers below `Y + 1`. -/
theorem badPrimeMass_le_length_mul_card (hb : 1 < b) (w : Fin k → Fin b)
    (ε : ℝ) (Y : ℕ) :
    badPrimeMass b hb w ε Y ≤ (Nat.log b (Y + 1) + 1) *
      (badIntegersBelow b hb w ε (Y + 1)).card := by
  classical
  calc
    _ ≤ ∑ _p ∈ badPrimesLE b hb w ε Y, (Nat.log b (Y + 1) + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      rcases (mem_badPrimesLE hb w ε Y p).1 hp with ⟨hpY, hp, _⟩
      exact length_natWord_le_log_cutoff hb hp.pos (by omega)
    _ = (badPrimesLE b hb w ε Y).card * (Nat.log b (Y + 1) + 1) := by simp
    _ ≤ (badIntegersBelow b hb w ε (Y + 1)).card * (Nat.log b (Y + 1) + 1) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card
        (badPrimesLE_subset_badIntegersBelow hb w ε Y))
    _ = _ := Nat.mul_comm _ _

/-- The weighted exceptional mass is bounded by `C (Y + 1)` divided by the digit-length
cutoff, uniformly in `Y`. The coefficient comes from the proved integer counting bound. -/
theorem exists_badPrimeMass_le_div_log_length (hb : 2 ≤ b) (hk : 1 ≤ k)
    (w : Fin k → Fin b) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ,
      (badPrimeMass b (by omega) w ε Y : ℝ) ≤
        C * ((Y + 1 : ℕ) : ℝ) / ((Nat.log b (Y + 1) + 1 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_badIntegersBelow_card_le_log_length_linear hb hk w ε hε
  refine ⟨C, hC, ?_⟩
  intro Y
  have hL : (0 : ℝ) < ((Nat.log b (Y + 1) + 1 : ℕ) : ℝ) := by positivity
  calc
    _ ≤ ((Nat.log b (Y + 1) + 1 : ℕ) : ℝ) *
        ((badIntegersBelow b (by omega) w ε (Y + 1)).card : ℝ) := by
      exact_mod_cast badPrimeMass_le_length_mul_card (by omega : 1 < b) w ε Y
    _ ≤ ((Nat.log b (Y + 1) + 1 : ℕ) : ℝ) *
        (C * ((Y + 1 : ℕ) : ℝ) / ((Nat.log b (Y + 1) + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (hbound (Y + 1) (by omega)) hL.le
    _ = _ := by field_simp

/-- The integer logarithmic digit-length cutoff tends to infinity. -/
theorem tendsto_log_length_atTop (b : ℕ) (hb : 1 < b) :
    Tendsto (fun Y : ℕ ↦ Nat.log b (Y + 1) + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (b ^ n)] with Y hY
  have hlog : n ≤ Nat.log b (Y + 1) :=
    (Nat.le_log_iff_pow_le hb (by omega : Y + 1 ≠ 0)).2 (by omega)
  omega

/-- For every fixed nonempty pattern and positive tolerance, the digit mass of bad
primes is negligible compared with the total prime digit mass. -/
theorem tendsto_badPrimeMass_div_primeDigitMass (hb : 2 ≤ b) (hk : 1 ≤ k)
    (w : Fin k → Fin b) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun Y : ℕ ↦ (badPrimeMass b (by omega) w ε Y : ℝ) /
      (primeDigitMass b (by omega) Y : ℝ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbad⟩ := exists_badPrimeMass_le_div_log_length hb hk w ε hε
  obtain ⟨c, hc, hmass⟩ := exists_pos_eventually_primeDigitMass_ge b (by omega)
  let L : ℕ → ℝ := fun Y ↦ ((Nat.log b (Y + 1) + 1 : ℕ) : ℝ)
  have hL (Y : ℕ) : 0 < L Y := by dsimp [L]; positivity
  have hLtendsto : Tendsto L atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_log_length_atTop b (by omega))
  have hupper : ∀ᶠ Y : ℕ in atTop,
      (badPrimeMass b (by omega) w ε Y : ℝ) / (primeDigitMass b (by omega) Y : ℝ) ≤
        (2 * C / c) / L Y := by
    filter_upwards [hmass, eventually_ge_atTop 1] with Y hmass hY
    have hY0 : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
    have hcY : 0 < c * (Y : ℝ) := mul_pos hc hY0
    have hshift : ((Y + 1 : ℕ) : ℝ) ≤ 2 * (Y : ℝ) := by
      exact_mod_cast (by omega : Y + 1 ≤ 2 * Y)
    calc
      _ ≤ (badPrimeMass b (by omega) w ε Y : ℝ) / (c * (Y : ℝ)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hcY hmass
      _ ≤ (C * ((Y + 1 : ℕ) : ℝ) / L Y) / (c * (Y : ℝ)) :=
        div_le_div_of_nonneg_right (hbad Y) hcY.le
      _ ≤ (C * (2 * (Y : ℝ)) / L Y) / (c * (Y : ℝ)) :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hshift hC.le)
            (hL Y).le) hcY.le
      _ = _ := by field_simp
  apply squeeze_zero' (Eventually.of_forall fun Y ↦ by positivity) hupper
  exact hLtendsto.const_div_atTop _

end CopelandErdos.NumberTheory
