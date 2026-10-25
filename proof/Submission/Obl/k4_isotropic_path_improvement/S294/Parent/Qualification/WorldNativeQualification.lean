-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.WorldNativeQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/WorldNativeQualification.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WorldFailureMass

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- The checked two-tangent higher jets control TOTAL original native
qualification failure, across every original coefficient world. Uniform
exponents precede all actual worlds, graphs, labels and reference laws.
The only source input is the scalar-normal builder on dense original
failure restrictions; native discovery itself is derived here. -/
theorem native_jet_world_grid_failure (d : ℝ) (hd : 0 ≤ d) (hd1 : d < 1)
    (M : ℕ) (hM : 2 ≤ M) (c_h : ℝ) (hch : 0 < c_h) :
    ∃ cζ : ℝ, 0 < cζ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ J ι : Type) [MeasurableSpace Λ] [MeasurableSpace J]
        [MeasurableSingletonClass J] [Countable J] [MeasurableSpace ι]
        (ν : Measure Λ) [IsProbabilityMeasure ν]
        (world : Λ → J), Measurable world →
      ∀ (cz : J → Λ → Fin 7 → ℝ) (E Eref : Set (Λ × ℝ)),
        MeasurableSet E → MeasurableSet Eref → E ⊆ Eref →
        (∀ z∈Eref, z.2∈Icc (0:ℝ) 1) →
      ∀ (F : J → ℝ → Fin 2 → ℝ) (piece : J → ℝ → Λ → Fin 7 → ℤ)
        (ζ : ℝ) (T : ℕ),
        N^(-c_h)/(N^α) ≤ ((2:ℝ)^T)⁻¹ →
        ((2:ℝ)^T)⁻¹ ≤ (N^α)*N^(-c_h) → ζ ≤ ((2:ℝ)^T)⁻¹^cζ →
        (∀ j, ν (world ⁻¹' {j}) ≠ 0 → ∀ A : Set (Λ × ℝ),
          MeasurableSet A → A ⊆ E ∩ ((world ⁻¹' {j}) ×ˢ univ) →
          ENNReal.ofReal (N^(-α)) ≤
            (((ν (world ⁻¹' {j}))⁻¹ • ν.restrict (world ⁻¹' {j})).prod volume) A →
          ScalarNormal ((ν (world ⁻¹' {j}))⁻¹ • ν.restrict (world ⁻¹' {j}))
            (cz j) A (F j) (piece j) (N^α) ζ d) →
      ∀ (lab : Λ × ℝ → ι) (G : Λ × ℝ → Fin 3 → ℝ),
        Measurable lab → MeasurableSet {q : ι × ι | q.1=q.2} → Measurable G →
      ∀ (c : Λ → Fin 7 → ℝ) (B graphError rowError : ℝ), 0 ≤ B →
        (∀ z∈E, |c z.1 1| ≤ B ∧ |c z.1 2| ≤ B ∧ |c z.1 4| ≤ B ∧ |c z.1 6| ≤ B) →
        (∀ z∈E, |c z.1 1+2*c z.1 2*z.2-
          (G z 0+G z 1*c z.1 4+G z 2*c z.1 6)| ≤ graphError) →
        (∀ z∈E, ∀ i : Fin 2, |G z i.succ-F (world z.1) z.2 i| ≤ rowError) →
        (∀ z∈E, ∀ v, (z.1,v)∈E → v∈dyadicBlock T z.2 → lab (z.1,v)=lab z) →
      ∀ (mesh err' dur' : ℝ) (bound : ℤ), 0 < mesh →
        3*B+(1+2*B)*N^ε ≤ mesh*(bound-1) →
        graphError+(1+2*B)*(rowError+((2:ℝ)^T)⁻¹^((M:ℝ)+1/8))+
          (M+1)*mesh ≤ err' → dur' ≤ ((2:ℝ)^T)⁻¹*N^(-ε) →
        (ν.prod volume)
          (E \ {z | NativeGridQualified Eref lab G M T mesh bound err' dur' z}) <
            ENNReal.ofReal (2*N^(-α)) := by
  obtain ⟨cζ,hcζ,hnext⟩ := nativeJetQualificationStatement d hd hd1 M hM c_h hch
  refine ⟨cζ,hcζ,fun ε hε => ?_⟩
  obtain ⟨α,hα,N₀,hN₀,hjet⟩ := hnext ε hε
  refine ⟨α,hα,N₀,hN₀,?_⟩
  intro N hN Λ J ι _ _ _ _ _ ν _ world hworld cz E Eref hE hEref hsub hunit
    F piece ζ T hTlo hThi hζ hbuild lab G hlab hdiag hG c B graphError rowError
    hB hc hgraph hrow hlabel mesh err' dur' bound hmesh hbound herr hdur
  have hNpos : 0 < N := zero_lt_one.trans_le (hN₀.trans hN)
  have hH : 0 < N^α := Real.rpow_pos_of_pos hNpos _
  have hout := native_grid_failure_mass_from_original_worlds ν world hworld E Eref hE hEref hsub hunit
    cz F piece hH lab hlab hdiag G hG M T mesh (3*B+(1+2*B)*N^ε)
    (graphError+(1+2*B)*(rowError+((2:ℝ)^T)⁻¹^((M:ℝ)+1/8)))
    (((2:ℝ)^T)⁻¹*N^(-ε)) err' dur' bound hmesh hbound herr hdur (by
      intro j hj A hA hAE hmass
      apply hbuild j hj A hA hAE
      simpa only [Real.rpow_neg hNpos.le] using hmass) (by
      intro j A hAE hSN
      let νj := (ν (world ⁻¹' {j}))⁻¹ • ν.restrict (world ⁻¹' {j})
      have hAE' : A ⊆ E := hAE.trans inter_subset_left
      apply hjet N hN Λ νj (cz j) A (F j) (piece j) (N^α) ζ T
        le_rfl hTlo hThi hζ hSN ι lab c G B graphError rowError hB
        (fun z hz => hc z (hAE' hz)) (fun z hz => hgraph z (hAE' hz))
      · intro z hz i
        have hh := hrow z (hAE' hz) i
        have hj : world z.1=j := (hAE hz).2.1
        simpa only [hj] using hh
      · intro z hz v hv hblock
        exact hlabel z (hAE' hz) v (hAE' hv) hblock)
  simpa only [Real.rpow_neg hNpos.le] using hout

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
