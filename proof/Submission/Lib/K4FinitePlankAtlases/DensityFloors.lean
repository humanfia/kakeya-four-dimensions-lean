import Mathlib

/-!
Adapted from: here:o049

Original proof developed by session x0147 in
Submission/Obl/k4_cap_class_terminal_charts/DensityFloors.lean.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- A joint L1 error controls the old mass where a typical lower density floor
fails after cell averaging. All discrete labels can be retained in `X`. -/
theorem density_floor_transfer {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g) (ρ : ℝ) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) {x | ρ ≤ f x ∧ g x < ρ / 2} ≤
      2 * ∫⁻ x, ENNReal.ofReal |f x - g x| ∂μ := by
  have hbad : MeasurableSet {x | ρ ≤ f x ∧ g x < ρ / 2} :=
    (measurableSet_le measurable_const hf).inter (measurableSet_lt hg measurable_const)
  rw [withDensity_apply _ hbad]
  calc
    _ ≤ ∫⁻ x in {x | ρ ≤ f x ∧ g x < ρ / 2}, 2 * ENNReal.ofReal |f x - g x| ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hbad] with x hx
      calc
        ENNReal.ofReal (f x) ≤ ENNReal.ofReal (2 * |f x - g x|) :=
          ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (f x - g x), hx.1, hx.2])
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    _ = 2 * ∫⁻ x in {x | ρ ≤ f x ∧ g x < ρ / 2}, ENNReal.ofReal |f x - g x| ∂μ :=
      lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hf.sub hg).abs)
    _ ≤ _ := mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) _

/-- The averaged lower-floor exception consists of the original exception and
at most twice the joint L1 averaging error. -/
theorem density_floor_exception {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g) (ρ : ℝ) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) {x | g x < ρ / 2} ≤
      μ.withDensity (fun x => ENNReal.ofReal (f x)) {x | f x < ρ} +
      2 * ∫⁻ x, ENNReal.ofReal |f x - g x| ∂μ := by
  have hsub : {x | g x < ρ / 2} ⊆ {x | f x < ρ} ∪ {x | ρ ≤ f x ∧ g x < ρ / 2} := by
    intro x hx
    rcases lt_or_ge (f x) ρ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hx⟩
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (density_floor_transfer μ f g hf hg ρ)))

/-- Count good cells using their ORIGINAL whole-cell mass witnesses. Restricting
or deleting points later does not need to preserve these floors. -/
theorem old_cell_count {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    (μ : Measure X) [IsFiniteMeasure μ] (F : Finset ι) (cells : ι → Set X)
    (hdisj : (↑F : Set ι).PairwiseDisjoint cells)
    (hmeas : ∀ i ∈ F, MeasurableSet (cells i)) {θ : ℝ} (hθ : 0 < θ)
    (hfloor : ∀ i ∈ F, θ ≤ μ.real (cells i)) :
    (F.card : ℝ) ≤ μ.real univ / θ := by
  apply (le_div_iff₀ hθ).mpr
  calc
    _ = ∑ _i ∈ F, θ := by simp
    _ ≤ ∑ i ∈ F, μ.real (cells i) := Finset.sum_le_sum hfloor
    _ = μ.real (⋃ i ∈ F, cells i) := (measureReal_biUnion_finset (μ := μ) hdisj hmeas).symm
    _ ≤ _ := measureReal_mono (subset_univ _)

/-- The three-dimensional working cell volume gives the precise budget used
by the continuous atlas kernel. -/
theorem old_cell_density_count {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    (μ : Measure X) [IsFiniteMeasure μ] (F : Finset ι) (cells : ι → Set X)
    (hdisj : (↑F : Set ι).PairwiseDisjoint cells)
    (hmeas : ∀ i ∈ F, MeasurableSet (cells i)) {D ρ : ℝ} (hD : 0 < D) (hρ : 0 < ρ)
    (hfloor : ∀ i ∈ F, ρ / D ^ 3 ≤ μ.real (cells i)) :
    (F.card : ℝ) ≤ μ.real univ * D ^ 3 / ρ := by
  apply (old_cell_count μ F cells hdisj hmeas (by positivity) hfloor).trans_eq
  field_simp

end Submission.Lib.K4FinitePlankAtlases
