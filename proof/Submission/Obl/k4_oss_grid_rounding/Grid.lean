import Mathlib
import Submission.Obl.k4_oss_collision_cauchy_schwarz.Cells

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Submission.Obl.k4_oss_grid_rounding

noncomputable section

abbrev cell := Submission.Obl.k4_oss_collision_cauchy_schwarz.cell

/-- The midpoint of an integer cell. -/
def center (δ : ℝ) (k : ℤ) : ℝ := δ * ((k : ℝ) + 1 / 2)

/-- Rounding to cell midpoints. -/
def rounding (δ : ℝ) (x : ℝ) : ℝ := center δ ⌊x / δ⌋

def gridIndices (δ : ℝ) : Finset ℤ := Finset.Icc ⌊(-1 : ℝ) / δ⌋ ⌊1 / δ⌋

def grid (δ : ℝ) : Finset ℝ := (gridIndices δ).image (center δ)

def weight (δ : ℝ) (α : Measure ℝ) (y : ℝ) : ℝ := α.real (rounding δ ⁻¹' {y})

theorem center_injective {δ : ℝ} (hδ : 0 < δ) : Function.Injective (center δ) := by
  intro k l h
  unfold center at h
  have h' := (mul_left_cancel₀ hδ.ne' h)
  exact_mod_cast (add_right_cancel h' : (k : ℝ) = (l : ℝ))

theorem measurable_rounding (δ : ℝ) : Measurable (rounding δ) := by
  unfold rounding center
  fun_prop

theorem rounding_fiber_center {δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    rounding δ ⁻¹' {center δ k} = cell δ k := by
  ext x
  exact (center_injective hδ).eq_iff

theorem weight_center {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ) (k : ℤ) :
    weight δ α (center δ k) = α.real (cell δ k) := by
  rw [weight, rounding_fiber_center hδ]

theorem rounding_dist {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    dist (rounding δ x) x ≤ δ / 2 := by
  have hlo := (le_div_iff₀ hδ).mp (Int.floor_le (x / δ))
  have hhi := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (x / δ))
  rw [Real.dist_eq, abs_le]
  unfold rounding center
  constructor <;> nlinarith

theorem index_mem {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ⌊x / δ⌋ ∈ gridIndices δ := by
  simp only [gridIndices, Finset.mem_Icc]
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hx.1 hδ.le),
    Int.floor_mono (div_le_div_of_nonneg_right hx.2 hδ.le)⟩

theorem rounding_mem {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    rounding δ x ∈ grid δ :=
  Finset.mem_image.mpr ⟨⌊x / δ⌋, index_mem hδ hx, rfl⟩

theorem weight_nonneg (δ : ℝ) (α : Measure ℝ) (y : ℝ) : 0 ≤ weight δ α y :=
  ENNReal.toReal_nonneg

theorem grid_separated {δ : ℝ} (hδ : 0 < δ) :
    ∀ x ∈ grid δ, ∀ y ∈ grid δ, x ≠ y → δ ≤ dist x y := by
  rintro x hx y hy hxy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hy
  have hkl : k - l ≠ 0 := by
    intro h
    exact hxy (congrArg (center δ) (sub_eq_zero.mp h))
  have habs : (1 : ℝ) ≤ |(k : ℝ) - (l : ℝ)| := by
    exact_mod_cast Int.one_le_abs hkl
  rw [Real.dist_eq, show center δ k - center δ l = δ * ((k : ℝ) - (l : ℝ)) by
    simp only [center]; ring, abs_mul, abs_of_pos hδ]
  nlinarith

theorem grid_card_le {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < (1 / 2 : ℝ)) :
    ((grid δ).card : ℝ) ≤ 4 / δ := by
  have hlohi : ⌊(-1 : ℝ) / δ⌋ ≤ ⌊1 / δ⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right (by norm_num) hδ.le)
  have hn : 0 ≤ ⌊1 / δ⌋ + 1 - ⌊(-1 : ℝ) / δ⌋ := by omega
  have hfloorlo := Int.sub_one_lt_floor ((-1 : ℝ) / δ)
  have hfloorhi := Int.floor_le (1 / δ)
  have hcard : ((grid δ).card : ℝ) =
      (⌊1 / δ⌋ : ℝ) + 1 - (⌊(-1 : ℝ) / δ⌋ : ℝ) := by
    rw [grid, Finset.card_image_iff.mpr (center_injective hδ).injOn,
      gridIndices, Int.card_Icc]
    exact_mod_cast Int.toNat_of_nonneg hn
  rw [hcard, le_div_iff₀ hδ]
  have hlow : -1 - δ < (⌊(-1 : ℝ) / δ⌋ : ℝ) * δ := by
    have := (div_lt_iff₀ hδ).mp (show (-1 : ℝ) / δ < (⌊(-1 : ℝ) / δ⌋ : ℝ) + 1 by
      linarith)
    nlinarith
  have hhigh := (le_div_iff₀ hδ).mp hfloorhi
  nlinarith

theorem rounding_ae_mem {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ)
    (hsupp : α (Icc (-1 : ℝ) 1)ᶜ = 0) :
    ∀ᵐ x ∂α, rounding δ x ∈ grid δ := by
  have hs : ∀ᵐ x ∂α, x ∈ Icc (-1 : ℝ) 1 := by
    exact ae_iff.mpr hsupp
  exact hs.mono fun x hx => rounding_mem hδ hx

theorem sum_weight {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ) [IsProbabilityMeasure α]
    (hsupp : α (Icc (-1 : ℝ) 1)ᶜ = 0) :
    ∑ y ∈ grid δ, weight δ α y = 1 := by
  change (∑ y ∈ grid δ, α.real (rounding δ ⁻¹' {y})) = 1
  rw [sum_measureReal_preimage_singleton _ (fun y hy =>
    (measurable_rounding δ) (measurableSet_singleton y))]
  have hfull : α (rounding δ ⁻¹' (grid δ : Set ℝ)) = 1 := by
    have hae := rounding_ae_mem hδ α hsupp
    have he : (rounding δ ⁻¹' (grid δ : Set ℝ)) =ᵐ[α] univ := by
      filter_upwards [hae] with x hx
      exact propext ⟨fun _ => mem_univ x, fun _ => hx⟩
    rw [measure_congr he, measure_univ]
  simp only [Measure.real, hfull, ENNReal.toReal_one]

theorem sum_weight_sq_pos {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ) [IsProbabilityMeasure α]
    (hsupp : α (Icc (-1 : ℝ) 1)ᶜ = 0) :
    0 < ∑ y ∈ grid δ, weight δ α y ^ 2 := by
  have hsum : 0 < ∑ y ∈ grid δ, weight δ α y := by rw [sum_weight hδ α hsupp]; norm_num
  obtain ⟨y, hy, hpos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun y hy => weight_nonneg δ α y)).mp hsum
  exact (Finset.sum_pos_iff_of_nonneg (fun y hy => sq_nonneg (weight δ α y))).mpr
    ⟨y, hy, sq_pos_of_pos hpos⟩

theorem ofReal_weight (δ : ℝ) (α : Measure ℝ) [IsFiniteMeasure α] (y : ℝ) :
    ENNReal.ofReal (weight δ α y) = α (rounding δ ⁻¹' {y}) := by
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem weighted_ball {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ) [IsFiniteMeasure α]
    (x u : ℝ) (hu : δ ≤ u) :
    ENNReal.ofReal (∑ y ∈ (grid δ).filter (fun y => dist y x ≤ u), weight δ α y) ≤
      α (Icc (x - 2 * u) (x + 2 * u)) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun y hy => weight_nonneg δ α y)]
  simp_rw [ofReal_weight]
  rw [sum_measure_preimage_singleton _ (fun y hy =>
    (measurable_rounding δ) (measurableSet_singleton y))]
  apply measure_mono
  intro y hy
  have hr := (Finset.mem_filter.mp (show rounding δ y ∈
    (grid δ).filter (fun z => dist z x ≤ u) from hy)).2
  have hd := (dist_triangle_left y x (rounding δ y)).trans
    (add_le_add (rounding_dist hδ y) hr)
  rw [Real.dist_eq, abs_le] at hd
  exact ⟨by linarith [hd.1], by linarith [hd.2]⟩

theorem cell_mass_zero {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ)
    (hsupp : α (Icc (-1 : ℝ) 1)ᶜ = 0) {k : ℤ} (hk : k ∉ gridIndices δ) :
    α (cell δ k) = 0 := by
  apply measure_mono_null _ hsupp
  intro x hx hxx
  exact hk (hx ▸ index_mem hδ hxx)

theorem square_energy {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ) [IsFiniteMeasure α]
    (hsupp : α (Icc (-1 : ℝ) 1)ᶜ = 0) :
    ENNReal.ofReal (∑ y ∈ grid δ, weight δ α y ^ 2) =
      ∑' k : ℤ, α (cell δ k) * α (cell δ k) := by
  rw [grid, Finset.sum_image (center_injective hδ).injOn]
  simp_rw [weight_center hδ]
  rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => sq_nonneg (α.real (cell δ k)))]
  have hreal (k : ℤ) : ENNReal.ofReal (α.real (cell δ k) ^ 2) =
      α (cell δ k) * α (cell δ k) := by
    rw [pow_two, ENNReal.ofReal_mul (show 0 ≤ α.real (cell δ k) from
      ENNReal.toReal_nonneg)]
    simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top α _)]
  simp_rw [hreal]
  symm
  apply tsum_eq_sum
  intro k hk
  rw [cell_mass_zero hδ α hsupp hk, zero_mul]

theorem energy_comparison {δ : ℝ} (hδ : 0 < δ) (α : Measure ℝ) [IsFiniteMeasure α]
    (hsupp : α (Icc (-1 : ℝ) 1)ᶜ = 0) :
    ENNReal.ofReal (∑ y ∈ grid δ, weight δ α y ^ 2) ≤
      (α.prod α) {q : ℝ × ℝ | |q.1 - q.2| ≤ δ} ∧
    (α.prod α) {q : ℝ × ℝ | |q.1 - q.2| ≤ δ} ≤
      ENNReal.ofReal (3 * (∑ y ∈ grid δ, weight δ α y ^ 2)) := by
  constructor
  · rw [square_energy hδ α hsupp]
    exact Submission.Obl.k4_oss_collision_cauchy_schwarz.cell_energy_le_collision α hδ
  · rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      square_energy hδ α hsupp]
    norm_num only [ENNReal.ofReal_ofNat]
    exact Submission.Obl.k4_oss_collision_cauchy_schwarz.collision_le_three_cell_energy α hδ

end
end Submission.Obl.k4_oss_grid_rounding
