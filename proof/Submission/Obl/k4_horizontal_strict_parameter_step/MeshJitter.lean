/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/MeshJitter.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Lib.K4AffineMeshCaps.Saturation

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps

noncomputable section

/-- Redistribute each cell's original mass uniformly inside that same cell.
No trajectory or entry weight is renormalized. -/
def meshJitter (δ : ℝ) (F : Finset (Fin 3 → ℤ)) (w : (Fin 3 → ℤ) → ENNReal) :
    Measure (Fin 3 → ℝ) :=
  ∑ q ∈ F, (w q / ENNReal.ofReal (δ ^ 3)) • volume.restrict (meshBox δ q)

theorem meshJitter_apply (δ : ℝ) (F : Finset (Fin 3 → ℤ)) (w : (Fin 3 → ℤ) → ENNReal)
    {B : Set (Fin 3 → ℝ)} (hB : MeasurableSet B) :
    meshJitter δ F w B = ∑ q ∈ F,
      (w q / ENNReal.ofReal (δ ^ 3)) * volume (B ∩ meshBox δ q) := by
  simp only [meshJitter, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hB]

/-- Redistribution preserves every original cell weight, hence their total mass. -/
theorem meshJitter_mass {δ : ℝ} (hδ : 0 < δ) (F : Finset (Fin 3 → ℤ))
    (w : (Fin 3 → ℤ) → ENNReal) :
    meshJitter δ F w univ = ∑ q ∈ F, w q := by
  rw [meshJitter_apply δ F w MeasurableSet.univ]
  apply Finset.sum_congr rfl
  intro q hq
  rw [univ_inter, volume_meshBox hδ, ENNReal.div_mul_cancel]
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  · exact ENNReal.ofReal_ne_top

/-- A finite cell cap becomes an actual continuous density ceiling after
redistribution. Distinct cells are disjoint, so no number of cells is paid. -/
theorem meshJitter_le_volume {δ : ℝ} (hδ : 0 < δ) (F : Finset (Fin 3 → ℤ))
    (w : (Fin 3 → ℤ) → ENNReal) (C : ENNReal)
    (hcap : ∀ q ∈ F, w q ≤ C * ENNReal.ofReal (δ ^ 3)) :
    meshJitter δ F w ≤ C • volume := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [meshJitter_apply δ F w hB, Measure.smul_apply, smul_eq_mul]
  have hcoef : ∀ q ∈ F, w q / ENNReal.ofReal (δ ^ 3) ≤ C := by
    intro q hq
    exact (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
      ENNReal.ofReal_ne_top).mpr (hcap q hq)
  calc
    _ ≤ ∑ q ∈ F, C * volume (B ∩ meshBox δ q) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (hcoef q hq) zero_le
    _ = C * ∑ q ∈ F, volume (B ∩ meshBox δ q) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * volume B := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      have hsum : volume (⋃ q ∈ F, B ∩ meshBox δ q) = ∑ q ∈ F, volume (B ∩ meshBox δ q) := by
        apply measure_biUnion_finset
        · intro q hq q' hq' hne
          exact (meshBox_pairwiseDisjoint δ hne).mono inter_subset_right inter_subset_right
        · intro q hq
          exact hB.inter (measurableSet_meshBox δ q)
      rw [← hsum]
      apply measure_mono
      intro z hz
      obtain ⟨q, hq, hz⟩ := mem_iUnion₂.mp hz
      exact hz.1

/-- Entry sums commute with redistribution. Consequently colour marginals
can be capped before redistributing, using their original disjoint assignments. -/
theorem meshJitter_sum {ι : Type*} (δ : ℝ) (F : Finset (Fin 3 → ℤ)) (J : Finset ι)
    (w : ι → (Fin 3 → ℤ) → ENNReal) :
    meshJitter δ F (fun q => ∑ j ∈ J, w j q) = ∑ j ∈ J, meshJitter δ F (w j) := by
  unfold meshJitter
  simp_rw [div_eq_mul_inv, Finset.sum_mul, Finset.sum_smul]
  exact Finset.sum_comm

/-- A cap on a whole original colour marginal becomes the same continuous
colour density cap, without paying for the number of paired entries. -/
theorem sum_meshJitter_le_volume {ι : Type*} {δ : ℝ} (hδ : 0 < δ)
    (F : Finset (Fin 3 → ℤ)) (J : Finset ι) (w : ι → (Fin 3 → ℤ) → ENNReal)
    (C : ENNReal) (hcap : ∀ q ∈ F, (∑ j ∈ J, w j q) ≤ C * ENNReal.ofReal (δ ^ 3)) :
    (∑ j ∈ J, meshJitter δ F (w j)) ≤ C • volume := by
  rw [← meshJitter_sum]
  exact meshJitter_le_volume hδ F _ C hcap

/-- Every property valid on cells with nonzero original weight remains almost
surely valid after redistribution. This transfers the graph agreement tests. -/
theorem meshJitter_ae {δ : ℝ} (F : Finset (Fin 3 → ℤ))
    (w : (Fin 3 → ℤ) → ENNReal) {P : (Fin 3 → ℝ) → Prop}
    (hP : ∀ q ∈ F, w q ≠ 0 → ∀ z ∈ meshBox δ q, P z) :
    ∀ᵐ z ∂meshJitter δ F w, P z := by
  classical
  unfold meshJitter
  rw [ae_finsetSum_measure_iff]
  intro q hq
  by_cases hw : w q = 0
  · simp only [hw, zero_div, zero_smul]
    simp
  · apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem (measurableSet_meshBox δ q)] with z hz
    exact hP q hq hw z hz

/-- For weights taken from a finite partition of the original law, the jittered
law has precisely its original, unnormalized total mass. -/
theorem meshJitter_original_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Z : Ω → Fin 3 → ℝ} (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (F : Finset (Fin 3 → ℤ))
    (hcover : ∀ᵐ p ∂μ, baseMesh δ (Z p) ∈ F) :
    meshJitter δ F (fun q => μ {p | baseMesh δ (Z p) = q}) univ = μ univ := by
  rw [meshJitter_mass hδ]
  have hm : Measurable (fun p => baseMesh δ (Z p)) := (measurable_baseMesh δ).comp hZ
  have hsets : ∀ q, MeasurableSet {p | baseMesh δ (Z p) = q} := fun q =>
    hm (measurableSet_singleton q)
  have hsum : μ (⋃ q ∈ F, {p | baseMesh δ (Z p) = q}) =
      ∑ q ∈ F, μ {p | baseMesh δ (Z p) = q} := by
    apply measure_biUnion_finset
    · intro q hq q' hq' hne
      apply disjoint_left.mpr
      intro p hp hp'
      exact hne (hp.symm.trans hp')
    · intro q hq
      exact hsets q
  rw [← hsum]
  apply measure_congr
  filter_upwards [hcover] with p hp
  apply propext
  exact ⟨fun _ => trivial, fun _ => mem_iUnion₂.mpr ⟨_, hp, rfl⟩⟩

/-- Original almost-everywhere tests transfer whenever they remain true for every
point of the same fine cell. Only nonzero original cells can contribute. -/
theorem meshJitter_transport_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (δ : ℝ) (F : Finset (Fin 3 → ℤ))
    {Q : Ω → Prop} {P : (Fin 3 → ℝ) → Prop} (hQ : ∀ᵐ p ∂μ, Q p)
    (htransport : ∀ p, Q p → ∀ z, baseMesh δ z = baseMesh δ (Z p) → P z) :
    ∀ᵐ z ∂meshJitter δ F (fun q => μ {p | baseMesh δ (Z p) = q}), P z := by
  apply meshJitter_ae
  intro q hq hw z hz
  obtain ⟨p, hp, hQp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hw (ae_restrict_of_ae hQ)
  exact htransport p hQp z (hz.trans hp.symm)

end

end Submission.Obl.k4_horizontal_strict_parameter_step
