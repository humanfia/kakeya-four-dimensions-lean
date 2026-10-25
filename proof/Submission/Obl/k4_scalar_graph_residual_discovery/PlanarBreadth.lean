/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PlanarBreadth.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Breadth
import Submission.Obl.k4_scalar_graph_residual_discovery.PlanarLines

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory

/-- Renewed scalar velocity breadth gives the determinant-weighted success
mass used by the planar incidence Kakeya inequality. -/
theorem planar_determinant_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (v : X → ℝ) (hv : Measurable v)
    {H b : ℝ} (hH : 0 ≤ H) (hb : 0 ≤ b) (hbound : ∀ᵐ p ∂μ, |v p| ≤ H)
    (hcap : ∀ w, μ {p | |v p - w| ≤ b} ≤ (1 / 2 : ENNReal) * μ univ) :
    (1 / 2 : ENNReal) * (μ univ) ^ 2 ≤ Measure.pi (fun _ : Fin 2 => μ)
      {p | b / (1 + H) ^ 2 ≤
        |Matrix.det (Matrix.of fun i j : Fin 2 => BaseLine.direction (v (p i)) j)|} := by
  have hboth : ∀ᵐ p ∂Measure.pi (fun _ : Fin 2 => μ), ∀ i, |v (p i)| ≤ H := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 2 => μ) (i := i)).eventually hbound
  apply (separated_pi_pair_mass_ge_half μ v hv b hcap).trans
  apply measure_mono_ae
  filter_upwards [hboth] with p hp hsep
  have hvec : (![BaseLine.direction (v (p 0)), BaseLine.direction (v (p 1))] :
      Fin 2 → BaseLine.Plane) = fun i => BaseLine.direction (v (p i)) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hvec] using BaseLine.direction_det_ge hH hb (hp 0) (hp 1) hsep.le

/-- Restricting both independent samples to one actual cell gives precisely
the success event in `plane_strip_filling`; its mass stays unnormalized. -/
theorem planar_cell_determinant_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (A : Set X) (hA : MeasurableSet A)
    (v : X → ℝ) (hv : Measurable v) {H b : ℝ} (hH : 0 ≤ H) (hb : 0 ≤ b)
    (hbound : ∀ᵐ p ∂μ.restrict A, |v p| ≤ H)
    (hcap : ∀ w, (μ.restrict A) {p | |v p - w| ≤ b} ≤ (1 / 2 : ENNReal) * μ A) :
    (1 / 2 : ENNReal) * (μ A) ^ 2 ≤ Measure.pi (fun _ : Fin 2 => μ)
      {p | (∀ i, p i ∈ A) ∧ b / (1 + H) ^ 2 ≤
        |Matrix.det (Matrix.of fun i j : Fin 2 => BaseLine.direction (v (p i)) j)|} := by
  have h := planar_determinant_mass (μ.restrict A) v hv hH hb hbound
    (fun w => by simpa only [Measure.restrict_apply_univ] using hcap w)
  rw [← Measure.restrict_pi_pi (fun _ : Fin 2 => μ) (fun _ : Fin 2 => A),
    Measure.restrict_apply' (MeasurableSet.univ_pi (fun _ => hA))] at h
  have heq : {p : Fin 2 → X | b / (1 + H) ^ 2 ≤
      |Matrix.det (Matrix.of fun i j : Fin 2 => BaseLine.direction (v (p i)) j)|} ∩
        Set.univ.pi (fun _ : Fin 2 => A) =
      {p : Fin 2 → X | (∀ i, p i ∈ A) ∧ b / (1 + H) ^ 2 ≤
        |Matrix.det (Matrix.of fun i j : Fin 2 => BaseLine.direction (v (p i)) j)|} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, mem_univ_pi, and_comm]
  simpa only [heq, Measure.restrict_apply_univ] using h

end Submission.Obl.k4_scalar_graph_residual_discovery
