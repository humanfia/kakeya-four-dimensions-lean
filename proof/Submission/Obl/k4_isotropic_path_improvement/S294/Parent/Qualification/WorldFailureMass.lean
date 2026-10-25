-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.WorldFailureMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/WorldFailureMass.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalWorldSelection
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FailureMass

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- A discovery in every dense original coefficient world controls the
ENTIRE original failed mass. There is no number-of-worlds factor and no
assumption that every participating world was initially dense. -/
theorem original_world_failure_mass_lt {Λ J : Type*}
    [MeasurableSpace Λ] [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]
    (ν : Measure Λ) [IsProbabilityMeasure ν]
    (world : Λ → J) (hworld : Measurable world)
    (E good : Set (Λ × ℝ)) (hE : MeasurableSet E) (hgood : MeasurableSet good)
    (hunit : E ⊆ univ ×ˢ Icc (0:ℝ) 1)
    {η : ℝ} (hη : 0 < η)
    (hdiscover : ∀ j : J, ν (world ⁻¹' {j}) ≠ 0 →
      ∀ A : Set (Λ × ℝ), MeasurableSet A → A ⊆ E ∩ ((world ⁻¹' {j}) ×ˢ univ) →
        ENNReal.ofReal η ≤
          (((ν (world ⁻¹' {j}))⁻¹ • ν.restrict (world ⁻¹' {j})).prod volume) A →
        ∃ x∈A, x∈good) :
    (ν.prod volume) (E \ good) < ENNReal.ofReal (2*η) := by
  let bad := E \ good
  have hbad : MeasurableSet bad := hE.diff hgood
  have hbadunit : bad ⊆ univ ×ˢ Icc (0:ℝ) 1 := sdiff_subset.trans hunit
  by_contra h
  have hmass : ENNReal.ofReal (2*η) ≤ (ν.prod volume) bad := le_of_not_gt h
  let reference := (ν.prod volume).restrict bad
  have hdom : reference ≤ ENNReal.ofReal (1:ℝ) • ν.prod volume := by
    simpa only [ENNReal.ofReal_one,one_smul] using
      (Measure.restrict_le_self : reference ≤ ν.prod volume)
  have hfull : reference badᶜ=0 := by
    rw [Measure.restrict_apply hbad.compl,compl_inter_self,measure_empty]
  have hmassref : ENNReal.ofReal (2*η) ≤ reference univ := by
    simpa only [reference,Measure.restrict_apply_univ] using hmass
  obtain ⟨j,hj,-,hdense⟩ := exists_original_parameter_world_of_unit_reference ν reference
    world hworld hbad hbadunit 1 (2*η) (by norm_num) (by positivity) hdom hfull hmassref
  have hworldm : MeasurableSet ((world ⁻¹' {j}) ×ˢ (univ : Set ℝ)) :=
    (hworld (measurableSet_singleton j)).prod MeasurableSet.univ
  have hdense' : ENNReal.ofReal η ≤
      (((ν (world ⁻¹' {j}))⁻¹ • ν.restrict (world ⁻¹' {j})).prod volume)
        (bad ∩ ((world ⁻¹' {j}) ×ˢ univ)) := by
    simpa only [mul_one,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hdense
  obtain ⟨x,hx,hxgood⟩ := hdiscover j hj (bad ∩ ((world ⁻¹' {j}) ×ˢ univ))
    (hbad.inter hworldm) (fun x hx => ⟨hx.1.1,hx.2⟩) hdense'
  exact hx.1.2 hxgood

/-- Native grid qualification fails on small original mass whenever the
actual source primitives build a scalar-normal world on any sufficiently
dense failure restriction. The original world priors are never reset. -/
theorem native_grid_failure_mass_from_original_worlds {Λ J ι : Type*}
    [MeasurableSpace Λ] [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]
    [MeasurableSpace ι]
    (ν : Measure Λ) [IsProbabilityMeasure ν]
    (world : Λ → J) (hworld : Measurable world)
    (E Eref : Set (Λ × ℝ)) (hE : MeasurableSet E) (hEref : MeasurableSet Eref)
    (hsub : E ⊆ Eref) (hunit : ∀ x∈Eref, x.2∈Icc (0:ℝ) 1)
    (cz : J → Λ → Fin 7 → ℝ) (F : J → ℝ → Fin 2 → ℝ)
    (piece : J → ℝ → Λ → Fin 7 → ℤ) {H ζ d : ℝ} (hH : 0 < H)
    (lab : Λ × ℝ → ι) (hlab : Measurable lab)
    (hdiag : MeasurableSet {q : ι × ι | q.1=q.2})
    (G : Λ × ℝ → Fin 3 → ℝ) (hG : Measurable G)
    (M T : ℕ) (mesh Kq err dur err' dur' : ℝ) (bound : ℤ)
    (hmesh : 0 < mesh) (hbound : Kq ≤ mesh*(bound-1))
    (herr : err+(M+1)*mesh ≤ err') (hdur : dur' ≤ dur)
    (hbuild : ∀ j : J, ν (world ⁻¹' {j}) ≠ 0 →
      ∀ A : Set (Λ × ℝ), MeasurableSet A → A ⊆ E ∩ ((world ⁻¹' {j}) ×ˢ univ) →
        ENNReal.ofReal H⁻¹ ≤
          (((ν (world ⁻¹' {j}))⁻¹ • ν.restrict (world ⁻¹' {j})).prod volume) A →
        Jets2.ScalarNormal
          ((ν (world ⁻¹' {j}))⁻¹ • ν.restrict (world ⁻¹' {j}))
          (cz j) A (F j) (piece j) H ζ d)
    (hjets : ∀ j : J, ∀ A : Set (Λ × ℝ),
      A ⊆ E ∩ ((world ⁻¹' {j}) ×ˢ univ) →
      Jets2.ScalarNormal ((ν (world ⁻¹' {j}))⁻¹ • ν.restrict (world ⁻¹' {j}))
        (cz j) A (F j) (piece j) H ζ d →
      ∃ x∈A, Jets2.NativeQualified A lab G M T Kq err dur x) :
    (ν.prod volume)
      (E \ {x | Jets2.NativeGridQualified Eref lab G M T mesh bound err' dur' x}) <
        ENNReal.ofReal (2*H⁻¹) := by
  let good := {x | Jets2.NativeGridQualified Eref lab G M T mesh bound err' dur' x}
  have hgood : MeasurableSet good :=
    Jets2.measurableSet_nativeGridQualified hEref hlab hdiag hG M T mesh bound err' dur'
  apply original_world_failure_mass_lt ν world hworld E good hE hgood
    (fun x hx => ⟨mem_univ _,hunit x (hsub hx)⟩) (inv_pos.mpr hH)
  intro j hj A hA hAE hmass
  have hSN := hbuild j hj A hA hAE hmass
  have hqual := hjets j A hAE hSN
  by_contra hnone
  have hfail : ∀ x∈A, ¬Jets2.NativeGridQualified Eref lab G M T mesh bound err' dur' x := by
    intro x hx hg
    exact hnone ⟨x,hx,hg⟩
  exact Jets2.false_of_world_in_failure_set hmesh
    ((hAE.trans inter_subset_left).trans hsub) hunit hbound herr hdur hfail hqual

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
