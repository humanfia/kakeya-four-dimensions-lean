import Submission.Obl.k4_horizon_light_cell_mass.Mesh
import Submission.Obl.k4_horizon_light_cell_mass.Source

namespace Submission.Obl.k4_horizon_light_cell_mass

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_native_base_flattening (ediff ediff_ofReal NativeMixtureFormat)
open Submission.Lib.K4ModelReduction (densityL1Distance)

noncomputable def stateCode (B a ρ₁ ρ₂ : ℝ) : State → CellCode :=
  meshCode ![ρ₁, ρ₂, ρ₂] ∘ pureMap B a

lemma stateCode_measurable (B a ρ₁ ρ₂ : ℝ) : Measurable (stateCode B a ρ₁ ρ₂) :=
  (meshCode_measurable _).comp (pureMap_measurable B a)

noncomputable def lightMass (μ : Measure State) (B a ρ₁ ρ₂ θ : ℝ) : ℝ≥0∞ :=
  μ {p | μ (stateCode B a ρ₁ ρ₂ ⁻¹' {stateCode B a ρ₁ ρ₂ p}) <
    ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2)}

/-- The entire one-world analytic estimate, uniform in both mesh widths and hidden scale. -/
theorem formatted_lightMass_le (n : ℝ) (M D : ℕ) (hn : 2 ≤ n)
    (μ : Measure State) (B a : ℝ)
    (f : Raw → ℝ) (hf : NativeMixtureFormat n M D f) (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfb : ∀ x, |f x| ≤ n ^ (2 * M))
    (hraw : μ.map rawChart = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (g : Observation → ℝ≥0∞) (hg : Measurable g)
    (hobs : μ.map (pureMap B a) = reference.withDensity g)
    (ρ₁ ρ₂ θ : ℝ) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hθ : 0 ≤ θ) :
    lightMass μ B a ρ₁ ρ₂ θ ≤
      ENNReal.ofReal (1769472 * (D : ℝ) * (n ^ M) ^ 9 * max ρ₁ ρ₂) +
        μ {p | g (pureMap B a p) < 4 * ENNReal.ofReal θ} := by
  obtain ⟨h, hhm, hh0, hhcell, hhe⟩ := rectangular_native_flattening
    n M D hn f hf hfm hf0 hfb hρ₁ hρ₂
  have hbound := light_mass_of_approx μ B a ρ₁ ρ₂ θ hρ₁ hρ₂ hθ
    (fun x => ENNReal.ofReal (f x)) (ENNReal.measurable_ofReal.comp hfm) hraw
    g hg hobs (fun x => ENNReal.ofReal (h x)) (ENNReal.measurable_ofReal.comp hhm)
    (pureMarginal_same_mesh B a ρ₁ ρ₂ h hhcell)
  have hdist : (∫⁻ x, ediff (ENNReal.ofReal (f x)) (ENNReal.ofReal (h x))) =
      densityL1Distance volume h f := by
    simp only [ediff_ofReal _ _ (hf0 _) (hh0 _), densityL1Distance, abs_sub_comm]
  rw [hdist] at hbound
  refine hbound.trans (add_le_add ?_ le_rfl)
  calc
    _ ≤ 3 * (6 * ENNReal.ofReal (98304 * (D : ℝ) * (n ^ M) ^ 9 * max ρ₁ ρ₂)) :=
      mul_le_mul_right hhe 3
    _ = ENNReal.ofReal (18 * (98304 * (D : ℝ) * (n ^ M) ^ 9 * max ρ₁ ρ₂)) := by
      rw [← mul_assoc, show (3 : ℝ≥0∞) * 6 = ENNReal.ofReal (18 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
    _ = _ := by congr 1; ring

lemma stateCode_eq_iff (B a ρ₁ ρ₂ : ℝ) (p q : State) :
    stateCode B a ρ₁ ρ₂ p = stateCode B a ρ₁ ρ₂ q ↔
      ⌊p.2 / ρ₁⌋ = ⌊q.2 / ρ₁⌋ ∧
      ⌊(p.1.2 0 + p.2 * p.1.2 3) / ρ₂⌋ = ⌊(q.1.2 0 + q.2 * q.1.2 3) / ρ₂⌋ ∧
      ⌊(p.1.2 1 + p.2 * p.1.2 4) / ρ₂⌋ = ⌊(q.1.2 1 + q.2 * q.1.2 4) / ρ₂⌋ ∧
      ⌊B * (p.1.2 2 + p.2 * p.1.2 5) / a⌋ =
        ⌊B * (q.1.2 2 + q.2 * q.1.2 5) / a⌋ := by
  simp only [stateCode, Function.comp_apply, meshCode, pureMap, Prod.ext_iff,
    funext_iff, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.forall_fin_zero, and_true]
  tauto

/-- Converting the restricted law back to the original measure keeps exactly the frozen event. -/
lemma original_lightMass_eq (μ : Measure State) (E : Set State) (B a ρ₁ ρ₂ θ : ℝ) :
    μ {p | p ∈ E ∧ μ {q | q ∈ E ∧ ⌊q.2 / ρ₁⌋ = ⌊p.2 / ρ₁⌋ ∧
      ⌊(q.1.2 0 + q.2 * q.1.2 3) / ρ₂⌋ = ⌊(p.1.2 0 + p.2 * p.1.2 3) / ρ₂⌋ ∧
      ⌊(q.1.2 1 + q.2 * q.1.2 4) / ρ₂⌋ = ⌊(p.1.2 1 + p.2 * p.1.2 4) / ρ₂⌋ ∧
      ⌊B * (q.1.2 2 + q.2 * q.1.2 5) / a⌋ = ⌊B * (p.1.2 2 + p.2 * p.1.2 5) / a⌋} <
        ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2)} = lightMass (μ.restrict E) B a ρ₁ ρ₂ θ := by
  let code := stateCode B a ρ₁ ρ₂
  have hc : Measurable code := stateCode_measurable B a ρ₁ ρ₂
  have hcell (p : State) : μ {q | q ∈ E ∧ ⌊q.2 / ρ₁⌋ = ⌊p.2 / ρ₁⌋ ∧
      ⌊(q.1.2 0 + q.2 * q.1.2 3) / ρ₂⌋ = ⌊(p.1.2 0 + p.2 * p.1.2 3) / ρ₂⌋ ∧
      ⌊(q.1.2 1 + q.2 * q.1.2 4) / ρ₂⌋ = ⌊(p.1.2 1 + p.2 * p.1.2 4) / ρ₂⌋ ∧
      ⌊B * (q.1.2 2 + q.2 * q.1.2 5) / a⌋ = ⌊B * (p.1.2 2 + p.2 * p.1.2 5) / a⌋} =
      μ.restrict E (code ⁻¹' {code p}) := by
    rw [Measure.restrict_apply (hc (measurableSet_singleton _))]
    congr 1
    ext q
    simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, mem_singleton_iff,
      code, stateCode_eq_iff]
    tauto
  simp_rw [hcell]
  have hb : MeasurableSet {p | μ.restrict E (code ⁻¹' {code p}) <
      ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2)} :=
    measurableSet_lt ((measurable_of_countable (fun c => μ.restrict E (code ⁻¹' {c}))).comp hc)
      measurable_const
  rw [lightMass, Measure.restrict_apply hb]
  congr 1
  ext p
  simp only [mem_setOf_eq, mem_inter_iff, code]
  tauto

end Submission.Obl.k4_horizon_light_cell_mass
