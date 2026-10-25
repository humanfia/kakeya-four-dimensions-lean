/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ConditionalNativeLaw.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentNativePartition
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Conditional native-point laws and restoration to original incidence mass. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set ProbabilityTheory
open Submission.Obl.k4_stable_native_signal_oscillation
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

def conditionalNativeLaw (μ : Measure Ω) (E : Set Ω) (f : Ω → NativePoint) :
    Measure NativePoint := Measure.map f (cond μ E)

theorem conditionalNativeLaw_probability (μ : Measure Ω) (E : Set Ω)
    (f : Ω → NativePoint) (h0 : μ E ≠ 0) (htop : μ E ≠ ⊤) :
    IsProbabilityMeasure (conditionalNativeLaw μ E f) := by
  have : IsProbabilityMeasure (cond μ E) := cond_isProbabilityMeasure_of_finite h0 htop
  change IsProbabilityMeasure (Measure.map f (cond μ E))
  exact inferInstance

theorem conditionalNativeLaw_ae (μ : Measure Ω) {E : Set Ω} (hE : MeasurableSet E)
    (f : Ω → NativePoint) (hf : Measurable f) {G : Set NativePoint} (hG : MeasurableSet G)
    (hgood : ∀ᵐ p ∂μ, p ∈ E → f p ∈ G) :
    ∀ᵐ p ∂conditionalNativeLaw μ E f, p ∈ G := by
  apply (ae_map_iff hf.aemeasurable hG).mpr
  have hg : ∀ᵐ p ∂cond μ E, p ∈ E → f p ∈ G := cond_absolutelyContinuous.ae_le hgood
  filter_upwards [hg, ae_cond_mem hE] with p hp hpE
  exact hp hpE

theorem conditionalNativeLaw_mesh_cap (μ : Measure Ω) {E : Set Ω}
    (hE : MeasurableSet E) (f : Ω → NativePoint) (hf : Measurable f)
    {C delta : ℝ}
    (h0 : μ E ≠ 0) (htop : μ E ≠ ⊤)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh delta (rootBaseCoordinates (f p)) = q ∧ p ∈ E} ≤
        ENNReal.ofReal (C * delta ^ 3)) :
    RootMeshCap (conditionalNativeLaw μ E f) (C / (μ E).toReal) delta := by
  intro q
  have hm : Measurable (fun p : NativePoint => baseMesh delta (rootBaseCoordinates p)) :=
    (measurable_baseMesh delta).comp measurable_rootBaseCoordinates
  have hset : MeasurableSet {p : NativePoint | baseMesh delta (rootBaseCoordinates p) = q} :=
    measurableSet_eq_fun hm measurable_const
  rw [conditionalNativeLaw, Measure.map_apply hf hset, cond_apply hE]
  have heq : E ∩ f ⁻¹' {p : NativePoint | baseMesh delta (rootBaseCoordinates p) = q} =
      {p | baseMesh delta (rootBaseCoordinates (f p)) = q ∧ p ∈ E} := by
    ext p
    exact and_comm
  rw [heq]
  have hmpos : 0 < (μ E).toReal := ENNReal.toReal_pos h0 htop
  have hinv : (μ E)⁻¹ = ENNReal.ofReal (((μ E).toReal)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hmpos, ENNReal.ofReal_toReal htop]
  calc
    _ ≤ (μ E)⁻¹ * ENNReal.ofReal (C * delta ^ 3) := mul_le_mul' le_rfl (hcap q)
    _ = ENNReal.ofReal (C / (μ E).toReal * delta ^ 3) := by
      rw [hinv, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- Pulling a loss back multiplies by the exact original parent mass. -/
theorem conditionalNativeLaw_restore_loss (μ : Measure Ω) {E : Set Ω}
    (hE : MeasurableSet E) (h0 : μ E ≠ 0) (htop : μ E ≠ ⊤)
    (f : Ω → NativePoint) (hf : Measurable f)
    (F : Fin 2 → Set NativePoint) (hF : ∀ i, MeasurableSet (F i))
    {eta : ℝ≥0∞} (hloss : conditionalNativeLaw μ E f (⋃ i, F i)ᶜ ≤ eta) :
    μ (E \ ⋃ i, f ⁻¹' F i) ≤ μ E * eta := by
  have hm : MeasurableSet (⋃ i, F i)ᶜ := (MeasurableSet.iUnion hF).compl
  rw [conditionalNativeLaw, Measure.map_apply hf hm, cond_apply hE] at hloss
  have heq : E ∩ f ⁻¹' (⋃ i, F i)ᶜ = E \ ⋃ i, f ⁻¹' F i := by
    simp only [preimage_compl, preimage_iUnion, sdiff_eq_compl_inter, inter_comm]
  rw [heq] at hloss
  calc
    _ = μ E * ((μ E)⁻¹ * μ (E \ ⋃ i, f ⁻¹' F i)) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel h0 htop, one_mul]
    _ ≤ μ E * eta := mul_le_mul' le_rfl hloss

end

end Submission.Obl.k4_general_parent_projected_layers
