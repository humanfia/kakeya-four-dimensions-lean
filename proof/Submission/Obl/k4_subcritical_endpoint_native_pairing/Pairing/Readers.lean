import Mathlib

/-! Measurable readers for the comparison domains: the dyadic time block of a
time, and the velocity-bin/parameter-square/time-block domain of an incidence.
Times on the dyadic block boundaries form a countable set, which is null for
every incidence law dominated by a product with Lebesgue measure in time. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing

open MeasureTheory Set

noncomputable section

/-- The dyadic time block containing a time of the unit interval; the right
endpoint `1` is put into the last block. -/
def timeBlock (T : ℕ) (t : ℝ) : ℕ := min ⌊t * 2 ^ T⌋₊ (2 ^ T - 1)

theorem timeBlock_lt (T : ℕ) (t : ℝ) : timeBlock T t < 2 ^ T := by
  unfold timeBlock
  have : 0 < 2 ^ T := by positivity
  omega

theorem measurable_timeBlock (T : ℕ) : Measurable (timeBlock T) := by
  have hf : Measurable (fun t : ℝ => ⌊t * 2 ^ T⌋₊) :=
    Nat.measurable_floor.comp (measurable_id.mul_const _)
  exact (measurable_from_top (f := fun m : ℕ => min m (2 ^ T - 1))).comp hf

/-- A time of the unit interval lies in the closed dyadic block named by
`timeBlock`. -/
theorem mem_timeBlock {T : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t ∈ Icc ((timeBlock T t : ℝ) / 2 ^ T) (((timeBlock T t : ℝ) + 1) / 2 ^ T) := by
  have hpos : (0 : ℝ) < 2 ^ T := by positivity
  have hx0 : 0 ≤ t * 2 ^ T := mul_nonneg ht.1 hpos.le
  have hfl := Nat.floor_le hx0
  have hlt := Nat.lt_floor_add_one (t * 2 ^ T)
  unfold timeBlock
  rcases le_total ⌊t * 2 ^ T⌋₊ (2 ^ T - 1) with hle | hle
  · rw [min_eq_left hle]
    constructor
    · rw [div_le_iff₀ hpos]; exact hfl
    · rw [le_div_iff₀ hpos]; exact hlt.le
  · rw [min_eq_right hle]
    have h1 : 1 ≤ 2 ^ T := Nat.one_le_two_pow
    have hcast : ((2 ^ T - 1 : ℕ) : ℝ) = 2 ^ T - 1 := by
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [hcast]
    have hge : (2 : ℝ) ^ T - 1 ≤ t * 2 ^ T := by
      have : ((2 ^ T - 1 : ℕ) : ℝ) ≤ (⌊t * 2 ^ T⌋₊ : ℝ) := by exact_mod_cast hle
      rw [hcast] at this
      linarith
    constructor
    · rw [div_le_iff₀ hpos]; linarith
    · rw [le_div_iff₀ hpos]; nlinarith [ht.2]

/-- Away from the block endpoints, a time of a closed dyadic block reads that block. -/
theorem timeBlock_eq_of_mem_Ioo {T j : ℕ} (hj : j < 2 ^ T) {t : ℝ}
    (ht : t ∈ Ioo ((j : ℝ) / 2 ^ T) (((j : ℝ) + 1) / 2 ^ T)) : timeBlock T t = j := by
  have hpos : (0 : ℝ) < 2 ^ T := by positivity
  have h1 : (j : ℝ) < t * 2 ^ T := by
    have := ht.1; rw [div_lt_iff₀ hpos] at this; exact this
  have h2 : t * 2 ^ T < (j : ℝ) + 1 := by
    have := ht.2; rw [lt_div_iff₀ hpos] at this; exact this
  have hfl : ⌊t * 2 ^ T⌋₊ = j :=
    (Nat.floor_eq_iff ((Nat.cast_nonneg j).trans h1.le)).mpr ⟨h1.le, h2⟩
  unfold timeBlock
  rw [hfl]
  omega

/-- The dyadic block endpoints. -/
def dyadicEndpoints (T : ℕ) : Set ℝ := Set.range (fun m : ℕ => (m : ℝ) / 2 ^ T)

theorem dyadicEndpoints_countable (T : ℕ) : (dyadicEndpoints T).Countable :=
  Set.countable_range _

/-- A closed dyadic block minus its endpoints is the open block. -/
theorem timeBlock_eq_of_mem {T j : ℕ} (hj : j < 2 ^ T) {t : ℝ}
    (ht : t ∈ Icc ((j : ℝ) / 2 ^ T) (((j : ℝ) + 1) / 2 ^ T))
    (hnot : t ∉ dyadicEndpoints T) : timeBlock T t = j := by
  apply timeBlock_eq_of_mem_Ioo hj
  refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
  · intro heq; exact hnot ⟨j, heq⟩
  · intro heq; exact hnot ⟨j + 1, by rw [heq]; push_cast; ring⟩

/-- Countably many times are null for a law dominated by a product with
Lebesgue measure in time. -/
theorem measure_time_countable_eq_zero {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (c : ENNReal)
    (hμ : μ ≤ c • ν.prod volume) {C : Set ℝ} (hC : C.Countable) :
    μ {ω | ω.2 ∈ C} = 0 := by
  have hset : {ω : α × ℝ | ω.2 ∈ C} = univ ×ˢ C := by
    ext ω; simp
  rw [hset]
  apply le_antisymm _ bot_le
  calc μ (univ ×ˢ C) ≤ (c • ν.prod volume) (univ ×ˢ C) := hμ _
    _ = 0 := by
      rw [Measure.smul_apply]
      have hz : (ν.prod volume) (univ ×ˢ C) = 0 := by
        rw [Measure.prod_prod, hC.measure_zero, mul_zero]
      rw [hz, smul_zero]

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing
