/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/AffineStripMass.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.TraceRectangle

/-! Original-prior and incidence ceilings for a bounded affine intercept strip. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem affine_intercept_strip_prior_cap {X : Type*} [MeasurableSpace X]
    (θ : Measure X) (Y V : X → ℝ) (π : Measure ℝ) (ξ R center : ℝ)
    (hξ : 0 < ξ) (hR : 0 ≤ R) (c : ℤ) (U : ℝ≥0∞)
    (hcap : ∀ q : ℤ, θ {l | Y l ∈ scalarVelocityBin ξ q ∧ V l ∈ scalarVelocityBin ξ c} ≤
      U * π (scalarVelocityBin ξ c)) :
    θ {l | |Y l - center| ≤ R * ξ ∧ V l ∈ scalarVelocityBin ξ c} ≤
      ENNReal.ofReal (4 * R + 2) * U * π (scalarVelocityBin ξ c) := by
  let C := {l | |Y l - center| ≤ R * ξ ∧ V l ∈ scalarVelocityBin ξ c}
  have hdiam : ∀ y ∈ Y '' C, ∀ y' ∈ Y '' C, dist y y' ≤ 2 * R * ξ := by
    rintro _ ⟨l,hl,rfl⟩ _ ⟨l',hl',rfl⟩
    rw [Real.dist_eq]
    calc
      _ ≤ |Y l - center| + |center - Y l'| := abs_sub_le _ _ _
      _ ≤ R * ξ + R * ξ := add_le_add hl.1 (by simpa only [abs_sub_comm] using hl'.1)
      _ = _ := by ring
  obtain ⟨hfin,hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (Y '' C) (by positivity : 0 ≤ 2 * R * ξ) hξ 0 hdiam
  simp only [sub_zero] at hfin hcard
  let Q := hfin.toFinset
  have hQc : (Q.card : ℝ) ≤ 4 * R + 2 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact hcard.trans_eq (by field_simp; ring)
  have hcover : C ⊆ ⋃ q ∈ Q, {l | Y l ∈ scalarVelocityBin ξ q ∧ V l ∈ scalarVelocityBin ξ c} := by
    intro l hl
    exact Set.mem_iUnion₂.mpr ⟨⌊Y l / ξ⌋,hfin.mem_toFinset.mpr ⟨Y l,⟨l,hl,rfl⟩,rfl⟩,rfl,hl.2⟩
  calc
    _ ≤ θ (⋃ q ∈ Q, {l | Y l ∈ scalarVelocityBin ξ q ∧ V l ∈ scalarVelocityBin ξ c}) := measure_mono hcover
    _ ≤ ∑ q ∈ Q, θ {l | Y l ∈ scalarVelocityBin ξ q ∧ V l ∈ scalarVelocityBin ξ c} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ Q, U * π (scalarVelocityBin ξ c) := Finset.sum_le_sum fun q _ => hcap q
    _ = (Q.card : ℝ≥0∞) * U * π (scalarVelocityBin ξ c) := by simp [mul_assoc]
    _ ≤ _ := by
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hQc

theorem affine_intercept_strip_incidence_cap {X : Type*} [MeasurableSpace X]
    (θ : Measure X) [SFinite θ] (μ : Measure (X × ℝ)) (Y V : X → ℝ)
    (π : Measure ℝ) (ξ R center D : ℝ) (hξ : 0 < ξ) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hdom : μ ≤ ENNReal.ofReal D • θ.prod volume) (c : ℤ) (U : ℝ≥0∞)
    (hcap : ∀ q : ℤ, θ {l | Y l ∈ scalarVelocityBin ξ q ∧ V l ∈ scalarVelocityBin ξ c} ≤
      U * π (scalarVelocityBin ξ c)) :
    μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |Y p.1 - center| ≤ R * ξ ∧ V p.1 ∈ scalarVelocityBin ξ c} ≤
      ENNReal.ofReal (D * (4 * R + 2)) * U * π (scalarVelocityBin ξ c) := by
  let C := {l | |Y l - center| ≤ R * ξ ∧ V l ∈ scalarVelocityBin ξ c}
  have he : {p : X × ℝ | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |Y p.1 - center| ≤ R * ξ ∧
      V p.1 ∈ scalarVelocityBin ξ c} = C ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp only [C,Set.mem_prod,Set.mem_ofPred_eq]
    tauto
  rw [he]
  calc
    _ ≤ (ENNReal.ofReal D • θ.prod volume) (C ×ˢ Set.Icc (0 : ℝ) 1) := hdom _
    _ = ENNReal.ofReal D * θ C := by simp [Measure.smul_apply,Measure.prod_prod,Real.volume_Icc]
    _ ≤ ENNReal.ofReal D * (ENNReal.ofReal (4 * R + 2) * U * π (scalarVelocityBin ξ c)) :=
      mul_le_mul' le_rfl (affine_intercept_strip_prior_cap θ Y V π ξ R center hξ hR c U hcap)
    _ = _ := by rw [ENNReal.ofReal_mul hD]; ring

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
