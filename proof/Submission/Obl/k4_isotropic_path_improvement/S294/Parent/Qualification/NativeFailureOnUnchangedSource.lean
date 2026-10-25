-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.NativeFailureOnUnchangedSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeFailureFromControlSelection

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Both spatial-entry pruning and residual comparison occur only
inside the failure argument. The physical source and its final witness
reference can be fixed first, without changing any statewise breadth. -/
theorem NativeQualificationAt.failure_on_unchanged_source
    {d ε cζ α Q₀ : ℝ} {M : ℕ}
    (hqualification : NativeQualificationAt d M ε cζ α Q₀) :
      ∀ N c_h : ℝ, 0 < N → 0 < c_h → Q₀ ≤ N^c_h →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsProbabilityMeasure ν]
        (c : Λ → Fin 7 → ℝ), Measurable c →
      ∀ E Eref : Set (Λ × ℝ), MeasurableSet E → MeasurableSet Eref → E⊆Eref →
        (∀ z∈Eref, z.2∈Icc (0:ℝ) 1) →
      ∀ ρ ζ cut C amplitude Kcap Kss Krc Kres : ℝ,
        0 < ρ → 0 < ζ → ζ ≤ 1 → ρ ≤ ζ → 0 < cut →
        0 ≤ C → 0 ≤ amplitude → 0 < Kcap → 625*C/cut ≤ Kcap →
        8*Kcap^2 ≤ N^(c_h*α) → Kss ≤ N^(c_h*α) →
        0 ≤ Krc → Krc ≤ N^(c_h*α) → Kres ≤ N^(c_h*α) →
      (∀ n : ℕ, n ≤ parameterLevel ζ →
        ((fun z : Λ × ℝ => originalZoomBlock c ρ (dyadicParameterWidth n) z.1) '' E).Finite) →
      ∀ π : Measure (Fin 2 → ℝ),
      (∀ q : ℝ, ζ ≤ q → q ≤ 1 → ∀ world cell β,
        ((ν.prod volume).restrict E) {z | parameterCode ρ (c z.1)=world ∧
          canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell ∧
          parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) (zv (c z.1))=β} ≤
        ENNReal.ofReal (C*dyadicParameterWidth (parameterLevel q)*
          (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+d)*amplitude)*
          π {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) v=β}) →
        ∀ F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ,
        ∀ factor residualLoss : ENNReal,
          (∀ U : Set (Λ × ℝ), MeasurableSet U → U⊆E →
            ∃ selected : Set (Λ × ℝ), MeasurableSet selected ∧ selected⊆U ∧
              (ν.prod volume) U≤factor*(ν.prod volume) selected+residualLoss ∧
              OriginalWorldControl ν c selected F ρ ζ d (N^(c_h*α)) Kcap Kss Krc Kres amplitude π) →
        ∀ T : ℕ,
          N^(-c_h)/(N^(c_h*α)) ≤ ((2:ℝ)^T)⁻¹ →
          ((2:ℝ)^T)⁻¹ ≤ (N^(c_h*α))*N^(-c_h) → ζ ≤ ((2:ℝ)^T)⁻¹^cζ →
        ∀ (ι : Type) [MeasurableSpace ι] (lab : Λ × ℝ → ι)
          (G : Λ × ℝ → Fin 3 → ℝ),
          Measurable lab → MeasurableSet {q : ι × ι | q.1=q.2} → Measurable G →
        ∀ B graphError rowError : ℝ, 0 ≤ B →
          (∀ z∈E, |c z.1 1| ≤ B ∧ |c z.1 2| ≤ B ∧ |c z.1 4| ≤ B ∧ |c z.1 6| ≤ B) →
          (∀ z∈E, |c z.1 1+2*c z.1 2*z.2-
            (G z 0+G z 1*c z.1 4+G z 2*c z.1 6)| ≤ graphError) →
          (∀ z∈E, ∀ i : Fin 2,
            |G z i.succ-F (parameterCode ρ (c z.1)) z.2 i| ≤ rowError) →
          (∀ z∈E, ∀ v, (z.1,v)∈E → v∈dyadicBlock T z.2 → lab (z.1,v)=lab z) →
        ∀ (mesh err' dur' : ℝ) (bound : ℤ), 0 < mesh →
          3*B+(1+2*B)*N^(c_h*ε) ≤ mesh*(bound-1) →
          graphError+(1+2*B)*(rowError+((2:ℝ)^T)⁻¹^((M:ℝ)+1/8))+
            (M+1)*mesh ≤ err' → dur' ≤ ((2:ℝ)^T)⁻¹*N^(-(c_h*ε)) →
          (ν.prod volume)
            (E\{z | NativeGridQualified Eref lab G M T mesh bound err' dur' z}) ≤
              ((parameterLevel ζ+1:ℕ):ENNReal)*ENNReal.ofReal (cut*zoomBlockVisitConstant)+
                factor*ENNReal.ofReal (2*N^(-(c_h*α)))+residualLoss := by
  intro N c_h hN hch hQ Λ _ ν _ c hc E Eref hE hEref hEEref ht
    ρ ζ cut C amplitude Kcap Kss Krc Kres hρ hζ hζ1 hρζ hcut hC hamp hKcap hnum
    hcapH hssH hrc0 hrcH hresH hfinite π hcap
  obtain ⟨R,hR,hRE,hloss,hafter⟩ := hqualification.failure_of_control_selection
    N c_h hN hch hQ Λ ν c hc E Eref hE hEref hEEref ht
    ρ ζ cut C amplitude Kcap Kss Krc Kres hρ hζ hζ1 hρζ hcut hC hamp hKcap hnum
    hcapH hssH hrc0 hrcH hresH hfinite π hcap
  intro F factor residualLoss hselection T hTlo hThi hζT ι _ lab G hlab hdiag hG
    B graphError rowError hB hcB hgraph hrow hlabel mesh err' dur' bound
    hmesh hbound herr hdur
  have hfailedR := hafter R hR (Subset.refl R) F factor residualLoss
    (fun U hU hUR => hselection U hU (hUR.trans hRE))
    T hTlo hThi hζT ι lab G hlab hdiag hG B graphError rowError hB
    (fun z hz => hcB z (hRE hz)) (fun z hz => hgraph z (hRE hz))
    (fun z hz => hrow z (hRE hz))
    (fun z hz v hv => hlabel z (hRE hz) v (hRE hv))
    mesh err' dur' bound hmesh hbound herr hdur
  let good := {z | NativeGridQualified Eref lab G M T mesh bound err' dur' z}
  calc
    (ν.prod volume) (E\good)≤(ν.prod volume) ((E\R)∪(R\good)) := by
      apply measure_mono
      intro z hz
      by_cases hzR : z∈R
      · exact Or.inr ⟨hzR,hz.2⟩
      · exact Or.inl ⟨hz.1,hzR⟩
    _ ≤ (ν.prod volume) (E\R)+(ν.prod volume) (R\good) := measure_union_le _ _
    _ ≤ ((parameterLevel ζ+1:ℕ):ENNReal)*ENNReal.ofReal (cut*zoomBlockVisitConstant)+
        (factor*ENNReal.ofReal (2*N^(-(c_h*α)))+residualLoss) := add_le_add hloss hfailedR
    _ = _ := (add_assoc _ _ _).symm

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
