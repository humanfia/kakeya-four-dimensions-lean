import Submission.Obl.k4_native_base_flattening.ObservationSupport

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set
open scoped ENNReal

def meshLeft (σ x : ℝ) : ℝ := (⌊x / σ⌋ : ℝ) * σ

def straddles (σ a : ℝ) : Set ℝ :=
  {x | ⌊x / a⌋ ≠ ⌊meshLeft σ x / a⌋}

/-- A fine cell whose left endpoint reads a different coarse bin is next to a
coarse boundary, even when the two grids are not nested. -/
theorem straddles_near_boundary {σ a x : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hx : x ∈ straddles σ a) :
    |x - (⌊x / a⌋ : ℝ) * a| ≤ σ := by
  have hleft : meshLeft σ x ≤ x := by
    exact (le_div_iff₀ hσ).mp (Int.floor_le (x / σ))
  have hright : x < meshLeft σ x + σ := by
    have h := (div_lt_iff₀ hσ).mp (Int.lt_floor_add_one (x / σ))
    simpa only [add_mul, one_mul, meshLeft] using h
  have hmono : ⌊meshLeft σ x / a⌋ ≤ ⌊x / a⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right hleft ha.le)
  have hstrict : ⌊meshLeft σ x / a⌋ < ⌊x / a⌋ :=
    lt_of_le_of_ne hmono (Ne.symm hx)
  have hstep : (⌊meshLeft σ x / a⌋ : ℝ) + 1 ≤ (⌊x / a⌋ : ℝ) := by
    exact_mod_cast (Int.add_one_le_iff.mpr hstrict)
  have hrep : meshLeft σ x < (⌊x / a⌋ : ℝ) * a := by
    have h := Int.lt_floor_add_one (meshLeft σ x / a)
    have h' : meshLeft σ x / a < (⌊x / a⌋ : ℝ) := h.trans_le hstep
    exact (div_lt_iff₀ ha).mp h'
  have hbin : (⌊x / a⌋ : ℝ) * a ≤ x :=
    (le_div_iff₀ ha).mp (Int.floor_le (x / a))
  rw [abs_of_nonneg (sub_nonneg.mpr hbin)]
  linarith

def boundarySlab (R σ a : ℝ) (j : ℤ) : Set (Fin 6 → ℝ) :=
  Icc (fun i => if i = 3 then (j : ℝ) * a - σ else -R)
    (fun i => if i = 3 then (j : ℝ) * a + σ else R)

theorem volume_boundarySlab (R σ a : ℝ) (hR : 0 ≤ R) (hσ : 0 ≤ σ) (j : ℤ) :
    volume (boundarySlab R σ a j) = ENNReal.ofReal (2 * σ * (2 * R) ^ 5) := by
  have hdiff : (j : ℝ) * a + σ - ((j : ℝ) * a - σ) = 2 * σ := by ring
  simp only [boundarySlab, Real.volume_Icc_pi, Fin.prod_univ_succ]
  norm_num [sub_neg_eq_add, ← two_mul, hdiff]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * σ),
    ENNReal.ofReal_pow (by positivity)]
  simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  ring

/-- The union of the exceptional fine cells has volume proportional to their
width and the number of coarse boundaries in the support cube. -/
theorem volume_straddling_cube {R σ a : ℝ} (hR : 0 ≤ R) (hσ : 0 < σ) (ha : 0 < a) :
    volume {z : Fin 6 → ℝ | (∀ i, |z i| ≤ R) ∧ z 3 ∈ straddles σ a} ≤
      ENNReal.ofReal ((2 * R / a + 5) * (2 * σ * (2 * R) ^ 5)) := by
  let J := Submission.Obl.k4_native_base_flattening.cubeBins R a
  have hcover : {z : Fin 6 → ℝ | (∀ i, |z i| ≤ R) ∧ z 3 ∈ straddles σ a} ⊆
      ⋃ j ∈ J, boundarySlab R σ a j := by
    intro z hz
    have hj : ⌊z 3 / a⌋ ∈ J :=
      Submission.Obl.k4_native_base_flattening.mem_cubeBins ha (hz.1 3)
    refine mem_iUnion.mpr ⟨⌊z 3 / a⌋, mem_iUnion.mpr ⟨hj, ?_⟩⟩
    change z ∈ Icc _ _
    have hnear := abs_le.mp (straddles_near_boundary hσ ha hz.2)
    constructor
    · intro i
      by_cases hi : i = 3
      · subst i
        simp only [ite_true]
        linarith [hnear.1]
      · simpa only [ite_eq_right hi] using (abs_le.mp (hz.1 i)).1
    · intro i
      by_cases hi : i = 3
      · subst i
        simp only [ite_true]
        linarith [hnear.2]
      · simpa only [ite_eq_right hi] using (abs_le.mp (hz.1 i)).2
  calc
    _ ≤ volume (⋃ j ∈ J, boundarySlab R σ a j) := measure_mono hcover
    _ ≤ ∑ j ∈ J, volume (boundarySlab R σ a j) := measure_biUnion_finset_le J _
    _ = ENNReal.ofReal ((J.card : ℝ) * (2 * σ * (2 * R) ^ 5)) := by
      simp [volume_boundarySlab R σ a hR hσ.le, ENNReal.ofReal_mul,
        ENNReal.ofReal_natCast, nsmul_eq_mul]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Submission.Obl.k4_native_base_flattening.card_cubeBins_le hR ha) (by positivity))

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
