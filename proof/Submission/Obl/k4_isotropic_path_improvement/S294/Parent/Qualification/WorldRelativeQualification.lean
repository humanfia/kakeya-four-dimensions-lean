-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.WorldRelativeQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/Qualification/WorldRelativeQualification.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WorldNativeQualification

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- The floor exponent and the original-world failure budget can be fixed
before the actual clock exponent. Apply the checked total-world theorem at
analytic base `N ^ c_h` and clock exponent one. All measures, coefficient
worlds, labels, dyadic blocks and ordinary witness times stay the same. -/
theorem native_jet_world_grid_failure_relative_clock
    (d : ℝ) (hd : 0 ≤ d) (hd1 : d < 1) (M : ℕ) (hM : 2 ≤ M) :
    ∃ cζ : ℝ, 0 < cζ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ α : ℝ, 0 < α ∧ ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧
      ∀ N c_h : ℝ, 0 < N → 0 < c_h → Q₀ ≤ N^c_h →
      ∀ (Λ J ι : Type) [MeasurableSpace Λ] [MeasurableSpace J]
        [MeasurableSingletonClass J] [Countable J] [MeasurableSpace ι]
        (ν : Measure Λ) [IsProbabilityMeasure ν]
        (world : Λ → J), Measurable world →
      ∀ (cz : J → Λ → Fin 7 → ℝ) (E Eref : Set (Λ × ℝ)),
        MeasurableSet E → MeasurableSet Eref → E ⊆ Eref →
        (∀ z∈Eref, z.2∈Icc (0:ℝ) 1) →
      ∀ (F : J → ℝ → Fin 2 → ℝ) (piece : J → ℝ → Λ → Fin 7 → ℤ)
        (ζ : ℝ) (T : ℕ),
        N^(-c_h)/(N^(c_h*α)) ≤ ((2:ℝ)^T)⁻¹ →
        ((2:ℝ)^T)⁻¹ ≤ (N^(c_h*α))*N^(-c_h) → ζ ≤ ((2:ℝ)^T)⁻¹^cζ →
        (∀ j, ν (world ⁻¹' {j}) ≠ 0 → ∀ A : Set (Λ × ℝ),
          MeasurableSet A → A ⊆ E ∩ ((world ⁻¹' {j}) ×ˢ univ) →
          ENNReal.ofReal (N^(-(c_h*α))) ≤
            (((ν (world ⁻¹' {j}))⁻¹ • ν.restrict (world ⁻¹' {j})).prod volume) A →
          ScalarNormal ((ν (world ⁻¹' {j}))⁻¹ • ν.restrict (world ⁻¹' {j}))
            (cz j) A (F j) (piece j) (N^(c_h*α)) ζ d) →
      ∀ (lab : Λ × ℝ → ι) (G : Λ × ℝ → Fin 3 → ℝ),
        Measurable lab → MeasurableSet {q : ι × ι | q.1=q.2} → Measurable G →
      ∀ (c : Λ → Fin 7 → ℝ) (B graphError rowError : ℝ), 0 ≤ B →
        (∀ z∈E, |c z.1 1| ≤ B ∧ |c z.1 2| ≤ B ∧ |c z.1 4| ≤ B ∧ |c z.1 6| ≤ B) →
        (∀ z∈E, |c z.1 1+2*c z.1 2*z.2-
          (G z 0+G z 1*c z.1 4+G z 2*c z.1 6)| ≤ graphError) →
        (∀ z∈E, ∀ i : Fin 2, |G z i.succ-F (world z.1) z.2 i| ≤ rowError) →
        (∀ z∈E, ∀ v, (z.1,v)∈E → v∈dyadicBlock T z.2 → lab (z.1,v)=lab z) →
      ∀ (mesh err' dur' : ℝ) (bound : ℤ), 0 < mesh →
        3*B+(1+2*B)*N^(c_h*ε) ≤ mesh*(bound-1) →
        graphError+(1+2*B)*(rowError+((2:ℝ)^T)⁻¹^((M:ℝ)+1/8))+
          (M+1)*mesh ≤ err' → dur' ≤ ((2:ℝ)^T)⁻¹*N^(-(c_h*ε)) →
        (ν.prod volume)
          (E \ {z | NativeGridQualified Eref lab G M T mesh bound err' dur' z}) <
            ENNReal.ofReal (2*N^(-(c_h*α))) := by
  obtain ⟨cζ,hcζ,hnext⟩ := native_jet_world_grid_failure d hd hd1 M hM 1 zero_lt_one
  refine ⟨cζ,hcζ,?_⟩
  intro ε hε
  obtain ⟨α,hα,Q₀,hQ₀,hgood⟩ := hnext ε hε
  refine ⟨α,hα,Q₀,hQ₀,?_⟩
  intro N c_h hN _hch hQ Λ J ι _ _ _ _ _ ν _ world hworld cz E Eref
    hE hEref hsub hunit F piece ζ T hTlo hThi hζ hbuild lab G hlab hdiag hG
    c B graphError rowError hB hc hgraph hrow hlabel mesh err' dur' bound
    hmesh hbound herr hdur
  have hαeq : (N^c_h)^α = N^(c_h*α) := (Real.rpow_mul hN.le _ _).symm
  have hαneg : (N^c_h)^(-α) = N^(-(c_h*α)) := by
    rw [← Real.rpow_mul hN.le]
    congr 1
    ring
  have hclock : (N^c_h)^(-1:ℝ) = N^(-c_h) := by
    rw [← Real.rpow_mul hN.le]
    congr 1
    ring
  have hεeq : (N^c_h)^ε = N^(c_h*ε) := (Real.rpow_mul hN.le _ _).symm
  have hεneg : (N^c_h)^(-ε) = N^(-(c_h*ε)) := by
    rw [← Real.rpow_mul hN.le]
    congr 1
    ring
  have hout := hgood (N^c_h) hQ Λ J ι ν world hworld cz E Eref
    hE hEref hsub hunit F piece ζ T
    (by simpa only [hαeq,hclock] using hTlo)
    (by simpa only [hαeq,hclock] using hThi) hζ
    (by simpa only [hαeq,hαneg] using hbuild) lab G hlab hdiag hG
    c B graphError rowError hB hc hgraph hrow hlabel mesh err' dur' bound
    hmesh (by simpa only [hεeq] using hbound) herr
    (by simpa only [hεneg] using hdur)
  simpa only [hαneg] using hout

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
