import Submission.Obl.k4_scalar_guarded_tangent_preparation.CodeVelocity
import Submission.Obl.k4_scalar_guarded_tangent_preparation.CodeReadout
import Submission.Obl.k4_scalar_guarded_tangent_preparation.SmoothedFrostman
import Submission.Obl.k4_scalar_guarded_tangent_preparation.VelocityReadoutAE

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The velocity palette is fixed from the original finite reference law.
Only its original total mass is used to form reference probabilities. -/
def fixedVelocityPalette {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : Measure Ω) (X : Ω → Fin n) (Z : Fin n → ℤ) (δ : ℝ) : Measure ℝ :=
  scatterPalette
    (fun i : velocityValues Z => (ProbabilityTheory.cond σ univ).real
      (finiteVelocityCode X Z ⁻¹' {i}))
    (fun i => (i.val : ℝ) * δ) δ

theorem fixedVelocityPalette_probability
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : Measure Ω) [IsFiniteMeasure σ] (hm : σ univ ≠ 0)
    (X : Ω → Fin n) (hX : Measurable X) (Z : Fin n → ℤ) {δ : ℝ} (hδ : 0 < δ) :
    IsProbabilityMeasure (fixedVelocityPalette σ X Z δ) := by
  let μ := ProbabilityTheory.cond σ univ
  letI : IsProbabilityMeasure μ :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hm (measure_ne_top σ univ)
  obtain ⟨hp, hp1, _⟩ := finite_code_probabilities μ (finiteVelocityCode X Z)
    (measurable_finiteVelocityCode X hX Z)
  exact scatterPalette_probability _ _ hδ hp hp1

theorem finiteVelocityCode_close_ae
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : Measure Ω) (X : Ω → Fin n) (Z : Fin n → ℤ) (V : Ω → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hcode : ∀ᵐ x ∂σ, Z (X x) = (⌊V x / δ⌋ : ℤ)) :
    ∀ᵐ x ∂σ, |V x - ((finiteVelocityCode X Z x).val : ℝ) * δ| ≤ δ := by
  filter_upwards [hcode] with x hx
  exact floor_center_error hδ _ hx.symm

/-- Angular caps for the old normalized velocity law pass to its fixed
blurred code palette. -/
theorem fixedVelocityPalette_cap
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : Measure Ω) [IsFiniteMeasure σ] (hm : σ univ ≠ 0)
    (X : Ω → Fin n) (hX : Measurable X) (Z : Fin n → ℤ) (V : Ω → ℝ)
    {δ width : ℝ} (hδ : 0 < δ) (hwidth : 2 * δ ≤ width)
    (hcode : ∀ᵐ x ∂σ, Z (X x) = (⌊V x / δ⌋ : ℤ))
    (C : ℝ≥0∞)
    (hcap : ∀ j : ℤ, ProbabilityTheory.cond σ univ {x | (⌊V x / width⌋ : ℤ) = j} ≤ C)
    (e : ℤ) : fixedVelocityPalette σ X Z δ {v | (⌊v / width⌋ : ℤ) = e} ≤ 6 * C := by
  let μ := ProbabilityTheory.cond σ univ
  letI : IsProbabilityMeasure μ :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hm (measure_ne_top σ univ)
  have hU := measurable_finiteVelocityCode X hX Z
  obtain ⟨_, _, hp⟩ := finite_code_probabilities μ (finiteVelocityCode X Z) hU
  have hclose := finiteVelocityCode_close_ae σ X Z V hδ hcode
  have hcloseμ : ∀ᵐ x ∂μ, |V x - ((finiteVelocityCode X Z x).val : ℝ) * δ| ≤ δ :=
    ProbabilityTheory.cond_absolutelyContinuous.ae_le hclose
  exact smoothed_floor_bin_cap μ (finiteVelocityCode X Z) hU V _ _ hδ hwidth hp hcloseμ C hcap e

/-- Original likelihood caps imply the exact requested velocity-bin cap
for every event predicted by the coarse state. The single fixed palette
is independent of that event and of every later incidence restriction. -/
theorem fixedVelocityPalette_joint_cap
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ ρ : Measure Ω) [IsFiniteMeasure σ] (hm : σ univ ≠ 0) (hρ : ρ ≤ σ)
    (X : Ω → Fin n) (hX : Measurable X) (Y : Fin n → ℕ) (Z : Fin n → ℤ)
    (V : Ω → ℝ) {δ width R : ℝ} (hδ : 0 < δ) (hwidth : 2 * δ ≤ width)
    (hR : 0 ≤ R) (hcode : ∀ᵐ x ∂σ, Z (X x) = (⌊V x / δ⌋ : ℤ))
    (hlikelihood : ∀ (e : ℕ) (z : ℤ),
      ρ.real {x | Y (X x) = e ∧ Z (X x) = z} * σ.real univ ≤
        R * σ.real {x | Y (X x) = e} * σ.real {x | Z (X x) = z})
    (P : Set Ω) (Q : ℕ → Prop) (hP : ∀ᵐ x ∂σ, x ∈ P ↔ Q (Y (X x))) (e : ℤ) :
    ρ (P ∩ {x | (⌊V x / width⌋ : ℤ) = e}) ≤
      4 * (ENNReal.ofReal R * σ P) *
        fixedVelocityPalette σ X Z δ {v | (⌊v / width⌋ : ℤ) = e} := by
  letI : IsFiniteMeasure ρ := isFiniteMeasure_of_le σ hρ
  let μ := ProbabilityTheory.cond σ univ
  letI : IsProbabilityMeasure μ :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hm (measure_ne_top σ univ)
  have htotal : 0 < σ.real univ := ENNReal.toReal_pos hm (measure_ne_top σ univ)
  have hfixed : ∀ (e : ℕ) (z : ℤ),
      ρ {x | Y (X x) = e ∧ Z (X x) = z} ≤
        ENNReal.ofReal R * σ {x | Y (X x) = e} * μ {x | Z (X x) = z} := by
    intro e z
    exact original_joint_to_fixed_palette σ ρ μ _ _ _ _ hR htotal
      (original_cond_mass_identity σ _) (hlikelihood e z)
  have hpred := predicted_event_joint_cap_ae σ ρ hρ X hX Y Z P Q hP
    (ENNReal.ofReal R) (fun z => μ {x | Z (X x) = z}) hfixed
  have hU := measurable_finiteVelocityCode X hX Z
  obtain ⟨_, _, hp⟩ := finite_code_probabilities μ (finiteVelocityCode X Z) hU
  have hclose := finiteVelocityCode_close_ae σ X Z V hδ hcode
  have hcloseρ : ∀ᵐ x ∂ρ, |V x - ((finiteVelocityCode X Z x).val : ℝ) * δ| ≤ δ :=
    (Measure.absolutelyContinuous_of_le hρ).ae_le hclose
  apply joint_floor_bin_from_fine_cells_ae ρ (finiteVelocityCode X Z) V _ _
    hδ hwidth P (ENNReal.ofReal R * σ P) hcloseρ
  intro i
  rw [hp, finiteVelocityCode_fiber]
  exact hpred i.val

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
