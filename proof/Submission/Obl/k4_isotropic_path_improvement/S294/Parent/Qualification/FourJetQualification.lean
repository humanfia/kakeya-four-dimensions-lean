-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FourJetQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FourJetQualification.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 7b3e681d23558c54d60b4f0a189273376405519e,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FourJetQualification.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

/-! # Native qualification with arbitrary intercepts

The native polynomial uses exactly the two signal jets and the two
planar velocities. The three intercepts need no bound.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open MeasureTheory Set
noncomputable section

def tangentCoefficients (c : Fin 7 → ℝ) : Fin 7 → ℝ := ![0,c 1,c 2,0,c 4,0,c 6]

theorem tangentCoefficients_bound {c : Fin 7 → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hc : |c 1| ≤ B ∧ |c 2| ≤ B ∧ |c 4| ≤ B ∧ |c 6| ≤ B) :
    ∀ j, |tangentCoefficients c j| ≤ B := by
  intro j
  fin_cases j
  · change |(0:ℝ)| ≤ B
    simpa only [abs_zero] using hB
  · exact hc.1
  · exact hc.2.1
  · change |(0:ℝ)| ≤ B
    simpa only [abs_zero] using hB
  · exact hc.2.2.1
  · change |(0:ℝ)| ≤ B
    simpa only [abs_zero] using hB
  · exact hc.2.2.2

theorem nativeRowPoly_tangentCoefficients (c : Fin 7 → ℝ) (P : Fin 2 → Polynomial ℝ) :
    nativeRowPoly (tangentCoefficients c) P=nativeRowPoly c P := rfl

/-- The scalar-normal world is the same world as before. Only the four
coefficients entering the original derivative and physical velocity are
required in the native polynomial coefficient budget. -/
def NativeJetQualificationStatement : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ M : ℕ, 2 ≤ M → ∀ c_h : ℝ, 0 < c_h →
    ∃ c_ζ : ℝ, 0 < c_ζ ∧ ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) (cz : Λ → Fin 7 → ℝ) (E : Set (Λ×ℝ))
        (F : ℝ → Fin 2 → ℝ) (piece : ℝ → Λ → Fin 7 → ℤ) (K ζ : ℝ) (T : ℕ),
        K ≤ N^α → N^(-c_h)/K ≤ ((2:ℝ)^T)⁻¹ → ((2:ℝ)^T)⁻¹ ≤ K*N^(-c_h) →
        ζ ≤ ((2:ℝ)^T)⁻¹^c_ζ → ScalarNormal ν cz E F piece K ζ d →
        ∀ (ι : Type) (lab : Λ×ℝ → ι) (c : Λ → Fin 7 → ℝ) (G : Λ×ℝ → Fin 3 → ℝ)
          (B graphError rowError : ℝ), 0 ≤ B →
        (∀ z ∈ E, |c z.1 1| ≤ B ∧ |c z.1 2| ≤ B ∧ |c z.1 4| ≤ B ∧ |c z.1 6| ≤ B) →
        (∀ z ∈ E, |c z.1 1+2*c z.1 2*z.2-
          (G z 0+G z 1*c z.1 4+G z 2*c z.1 6)| ≤ graphError) →
        (∀ z ∈ E, ∀ i : Fin 2, |G z i.succ-F z.2 i| ≤ rowError) →
        (∀ z ∈ E, ∀ v, (z.1,v) ∈ E → v ∈ dyadicBlock T z.2 → lab (z.1,v)=lab z) →
        ∃ z ∈ E, NativeQualified E lab G M T (3*B+(1+2*B)*N^ε)
          (graphError+(1+2*B)*(rowError+((2:ℝ)^T)⁻¹^((M:ℝ)+1/8)))
          (((2:ℝ)^T)⁻¹*N^(-ε)) z

theorem nativeJetQualificationStatement_of_nativeQualification
    (h : NativeQualificationStatement) : NativeJetQualificationStatement := by
  intro d hd0 hd1 M hM c_h hch
  obtain ⟨cζ,hcζ,hε⟩ := h d hd0 hd1 M hM c_h hch
  refine ⟨cζ,hcζ,fun ε hε0 => ?_⟩
  obtain ⟨α,hα,N₀,hN₀,hnext⟩ := hε ε hε0
  refine ⟨α,hα,N₀,hN₀,?_⟩
  intro N hN Λ _ ν cz E F piece K ζ T hK hTlo hThi hζ hSN
    ι lab c G B graphError rowError hB hjets hgraph hrow hlab
  exact hnext N hN Λ ν cz E F piece K ζ T hK hTlo hThi hζ hSN
    ι lab (fun l => tangentCoefficients (c l)) G B graphError rowError hB
    (fun z hz => tangentCoefficients_bound hB (hjets z hz)) hgraph hrow hlab

theorem nativeJetQualificationStatement_of_higherJets (hHJ : HigherJetsStatement) :
    NativeJetQualificationStatement :=
  nativeJetQualificationStatement_of_nativeQualification (nativeQualificationStatement_of_higherJets hHJ)

theorem nativeJetQualificationStatement : NativeJetQualificationStatement :=
  nativeJetQualificationStatement_of_nativeQualification nativeQualificationStatement

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
