-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalCoarsePalette, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalCoarsePalette.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalCoarsePalette.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalCoarsePalette.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.Conditioning

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Condition the unchanged original velocity palette on its original
coarse bin. No incidence law occurs in this denominator. -/
def originalCoarsePalette {V : Type*} [MeasurableSpace V]
    (π : Measure V) (I : Set V) : Measure V := (π I)⁻¹ • π.restrict I

theorem originalCoarsePalette_probability {V : Type*} [MeasurableSpace V]
    (π : Measure V) (I : Set V) (hI : π I ≠ 0) (hItop : π I ≠ ⊤) :
    IsProbabilityMeasure (originalCoarsePalette π I) := by
  have hh := Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior_probability
    π I (MeasurableEquiv.refl V) hI hItop
  change IsProbabilityMeasure ((π I)⁻¹ • Measure.map id (π.restrict I)) at hh
  simpa only [originalCoarsePalette,Measure.map_id] using hh

/-- An original reference floor containing the SAME coarse-palette
mass converts old joint caps to the common conditional palette. The
current entry stays unnormalized throughout. -/
theorem entry_cap_under_original_coarse_palette {Ω V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V]
    (μ : Measure Ω) (π : Measure V) (control : Ω → V) (I : Set V) (hI : MeasurableSet I)
    (weight C δ : ENNReal) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤)
    (hI0 : π I ≠ 0) (hItop : π I ≠ ⊤)
    (hfull : ∀ᵐ z ∂μ, control z ∈ I)
    (hfloor : δ * weight * π I ≤ μ univ)
    (hcap : ∀ A : Set V, MeasurableSet A → μ (control ⁻¹' A) ≤ C * weight * π A) :
    ∀ A : Set V, MeasurableSet A →
      μ (control ⁻¹' A) ≤ (C / δ) * μ univ * (originalCoarsePalette π I) A := by
  have hfirst : δ * weight ≤ (π I)⁻¹ * μ univ := by
    calc
      _ = (π I)⁻¹ * (δ * weight * π I) := by
        rw [mul_comm (δ * weight) (π I),← mul_assoc,ENNReal.inv_mul_cancel hI0 hItop,one_mul]
      _ ≤ (π I)⁻¹ * μ univ := mul_le_mul' le_rfl hfloor
  have href : weight ≤ δ⁻¹ * ((π I)⁻¹ * μ univ) := by
    calc
      _ = δ⁻¹ * (δ * weight) := by
        rw [← mul_assoc,ENNReal.inv_mul_cancel hδ0 hδtop,one_mul]
      _ ≤ _ := mul_le_mul' le_rfl hfirst
  intro A hA
  have heq : μ (control ⁻¹' A) = μ (control ⁻¹' (A ∩ I)) := by
    apply measure_congr
    filter_upwards [hfull] with z hz
    simp only [mem_preimage,mem_inter_iff,hz,and_true]
  calc
    _ = μ (control ⁻¹' (A ∩ I)) := heq
    _ ≤ C * weight * π (A ∩ I) := hcap _ (hA.inter hI)
    _ ≤ C * (δ⁻¹ * ((π I)⁻¹ * μ univ)) * π (A ∩ I) := by gcongr
    _ = (C / δ) * μ univ * (originalCoarsePalette π I) A := by
      rw [originalCoarsePalette,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hA,
        div_eq_mul_inv]
      ring

/-- Use the unchanged original prior in an inactive null coarse bin.
This gives a probability palette for every world, including empty ones. -/
def originalBinPalette {V : Type*} [MeasurableSpace V]
    (π : Measure V) (I : Set V) : Measure V :=
  if π I = 0 then π else originalCoarsePalette π I

theorem originalBinPalette_probability {V : Type*} [MeasurableSpace V]
    (π : Measure V) [IsProbabilityMeasure π] (I : Set V) :
    IsProbabilityMeasure (originalBinPalette π I) := by
  unfold originalBinPalette
  split_ifs with hI
  · infer_instance
  · exact originalCoarsePalette_probability π I hI (measure_ne_top _ _)

/-- An actual positive entry cannot lie in a null original coarse
palette bin. Thus its old joint caps and old reference floor yield the
COMMON bin palette used by every entry in that world. -/
theorem positive_entry_original_bin_cap {Ω V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V]
    (μ : Measure Ω) (π : Measure V) [IsProbabilityMeasure π]
    (control : Ω → V) (I : Set V) (hI : MeasurableSet I)
    (weight C δ : ENNReal) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤)
    (hpositive : μ univ ≠ 0) (hfull : ∀ᵐ z ∂μ, control z ∈ I)
    (hfloor : δ * weight * π I ≤ μ univ)
    (hcap : ∀ A : Set V, MeasurableSet A → μ (control ⁻¹' A) ≤ C * weight * π A) :
    ∀ A : Set V, MeasurableSet A →
      μ (control ⁻¹' A) ≤ (C/δ) * μ univ * (originalBinPalette π I) A := by
  have hI0 : π I ≠ 0 := by
    intro hzero
    have heq : μ univ = μ (control ⁻¹' I) := by
      apply measure_congr
      filter_upwards [hfull] with z hz
      simp only [mem_univ,mem_preimage,hz]
    have hh := hcap I hI
    rw [hzero,mul_zero,← heq] at hh
    exact hpositive (le_antisymm hh bot_le)
  rw [originalBinPalette,if_neg hI0]
  exact entry_cap_under_original_coarse_palette μ π control I hI weight C δ hδ0 hδtop
    hI0 (measure_ne_top _ _) hfull hfloor hcap

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
