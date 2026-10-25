-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.IncidenceWorldQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.IncidenceWorldControl
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WorldRelativeQualification

/-! Total original-world qualification directly from current incidence caps.

The entry preparation is done once, before the final source and its row
and residual cuts are chosen. Every later measurable source with the
hereditary world estimates has the same original-prior failure bound.
The higher-jet constants precede the actual relative clock and the data.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Current singleton velocity caps give one entry cut and a uniform
native qualification estimate on every later controlled source. Neither
original time-fiber caps nor scalar-normal failure worlds are premises. -/
theorem prepare_native_qualification_from_current_velocity_caps
    (d : ℝ) (hd : 0 ≤ d) (hd1 : d < 1) (M : ℕ) (hM : 2 ≤ M) :
    ∃ cζ : ℝ, 0 < cζ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ α : ℝ, 0 < α ∧ ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧
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
      ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R⊆E ∧
        (ν.prod volume) (E\R) ≤ ((parameterLevel ζ+1:ℕ):ENNReal)*
          ENNReal.ofReal (cut*zoomBlockVisitConstant) ∧
        ∀ S : Set (Λ × ℝ), MeasurableSet S → S⊆R →
        ∀ F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ,
          OriginalWorldControl ν c S F ρ ζ d (N^(c_h*α)) Kcap Kss Krc Kres amplitude π →
        ∀ T : ℕ,
          N^(-c_h)/(N^(c_h*α)) ≤ ((2:ℝ)^T)⁻¹ →
          ((2:ℝ)^T)⁻¹ ≤ (N^(c_h*α))*N^(-c_h) → ζ ≤ ((2:ℝ)^T)⁻¹^cζ →
        ∀ (ι : Type) [MeasurableSpace ι] (lab : Λ × ℝ → ι)
          (G : Λ × ℝ → Fin 3 → ℝ),
          Measurable lab → MeasurableSet {q : ι × ι | q.1=q.2} → Measurable G →
        ∀ B graphError rowError : ℝ, 0 ≤ B →
          (∀ z∈S, |c z.1 1| ≤ B ∧ |c z.1 2| ≤ B ∧ |c z.1 4| ≤ B ∧ |c z.1 6| ≤ B) →
          (∀ z∈S, |c z.1 1+2*c z.1 2*z.2-
            (G z 0+G z 1*c z.1 4+G z 2*c z.1 6)| ≤ graphError) →
          (∀ z∈S, ∀ i : Fin 2,
            |G z i.succ-F (parameterCode ρ (c z.1)) z.2 i| ≤ rowError) →
          (∀ z∈S, ∀ v, (z.1,v)∈S → v∈dyadicBlock T z.2 → lab (z.1,v)=lab z) →
        ∀ (mesh err' dur' : ℝ) (bound : ℤ), 0 < mesh →
          3*B+(1+2*B)*N^(c_h*ε) ≤ mesh*(bound-1) →
          graphError+(1+2*B)*(rowError+((2:ℝ)^T)⁻¹^((M:ℝ)+1/8))+
            (M+1)*mesh ≤ err' → dur' ≤ ((2:ℝ)^T)⁻¹*N^(-(c_h*ε)) →
          (ν.prod volume)
            (S\{z | NativeGridQualified Eref lab G M T mesh bound err' dur' z}) <
              ENNReal.ofReal (2*N^(-(c_h*α))) := by
  obtain ⟨cζ,hcζ,hnext⟩ := native_jet_world_grid_failure_relative_clock d hd hd1 M hM
  refine ⟨cζ,hcζ,?_⟩
  intro ε hε
  obtain ⟨α,hα,Q₀,hQ₀,hqual⟩ := hnext ε hε
  refine ⟨α,hα,Q₀,hQ₀,?_⟩
  intro N c_h hN hch hQ Λ _ ν _ c hc E Eref hE hEref hEEref ht
    ρ ζ cut C amplitude Kcap Kss Krc Kres hρ hζ hζ1 hρζ hcut hC hamp hKcap hnum
    hcapH hssH hrc0 hrcH hresH hfinite π hcap
  obtain ⟨R,hR,hRE,hloss,hcoarse,hfine⟩ :=
    prepare_original_spatial_cap_source_of_velocity_bins (ν.prod volume) ν c hc E hE
      (fun z hz => ht z (hEEref hz)) hρ hζ hcut hC hamp hd hfinite π hcap
  refine ⟨R,hR,hRE,?_,?_⟩
  · simpa only [measure_univ,mul_one] using hloss
  · intro S hS hSR F control T hTlo hThi hζT ι _ lab G hlab hdiag hG
      B graphError rowError hB hcB hgraph hrow hlabel mesh err' dur' bound
      hmesh hbound herr hdur
    have hH : 1 ≤ N^(c_h*α) := by
      have : 1 ≤ (N^c_h)^α := Real.one_le_rpow (hQ₀.trans hQ) hα.le
      simpa only [←Real.rpow_mul hN.le] using this
    have hSE : S⊆E := hSR.trans hRE
    have hbuild := OriginalWorldControl.scalar_normal_builder ν c hc R S hSR F
      ρ ζ d (N^(c_h*α)) Kcap (625*C/cut) Kss Krc Kres amplitude
      hρ hζ hζ1 hd hd1 hH hKcap hnum hamp hcapH hssH hrc0 hrcH hresH hρζ
      (fun z hz => ht z (hEEref (hSE hz))) π control hcoarse hfine
    exact hqual N c_h hN hch hQ Λ (Fin 7 → ℤ) ι ν
      (fun l => parameterCode ρ (c l)) ((measurable_parameterCode ρ).comp hc)
      (fun world l => zoomCoefficients ρ (parameterCenter ρ world) (c l))
      S Eref hS hEref (hSE.trans hEEref) ht F
      (fun _ => zoomParameterPiece ρ c) ζ T hTlo hThi hζT
      (by simpa only [Real.rpow_neg hN.le,Set.preimage,Set.mem_singleton_iff] using hbuild)
      lab G hlab hdiag hG c B graphError rowError hB hcB hgraph hrow hlabel
      mesh err' dur' bound hmesh hbound herr hdur

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
