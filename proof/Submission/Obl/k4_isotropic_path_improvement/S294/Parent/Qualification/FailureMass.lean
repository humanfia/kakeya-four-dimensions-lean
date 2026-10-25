-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FailureMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FailureMass.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Restrict

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Restrict to the measurable failure set while retaining the same
original prior. A discovery theorem in every dense restriction then
bounds its original mass. Witness times are restored to the fixed
reference before the contradiction is taken. -/
theorem native_grid_failure_mass_lt {Λ ι : Type*}
    [MeasurableSpace Λ] [MeasurableSpace ι]
    {ν : Measure Λ} {c : Λ → Fin 7 → ℝ} {E Eref : Set (Λ × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ}
    {K H ζ d : ℝ} (hSN : ScalarNormal ν c E F piece K ζ d)
    (hKH : K ≤ H) (hsub : E ⊆ Eref) (hEref : MeasurableSet Eref)
    (hunit : ∀ z ∈ Eref, z.2 ∈ Icc (0 : ℝ) 1)
    (lab : Λ × ℝ → ι) (hlab : Measurable lab)
    (hdiag : MeasurableSet {q : ι × ι | q.1 = q.2})
    (G : Λ × ℝ → Fin 3 → ℝ) (hG : Measurable G)
    (M T : ℕ) (mesh Kq err dur err' dur' : ℝ) (L : ℤ)
    (hmesh : 0 < mesh) (hL : Kq ≤ mesh * (L - 1))
    (herr : err + (M + 1) * mesh ≤ err') (hdur : dur' ≤ dur)
    (hdiscover : ∀ E₁ : Set (Λ × ℝ), E₁ ⊆ E →
      ScalarNormal ν c E₁ F piece H ζ d →
      ∃ z ∈ E₁, NativeQualified E₁ lab G M T Kq err dur z) :
    (ν.prod volume) (E \ {z | NativeGridQualified Eref lab G M T mesh L err' dur' z}) <
      ENNReal.ofReal H⁻¹ := by
  let bad := E \ {z | NativeGridQualified Eref lab G M T mesh L err' dur' z}
  have hbad : MeasurableSet bad := hSN.measurableSet_E.diff
    (measurableSet_nativeGridQualified hEref hlab hdiag hG M T mesh L err' dur')
  have hbadsub : bad ⊆ E := sdiff_subset
  by_contra h
  have hmass : ENNReal.ofReal H⁻¹ ≤ (ν.prod volume) bad := le_of_not_gt h
  have hnormal := hSN.restrict hbadsub hbad hKH hmass
  have hq := hdiscover bad hbadsub hnormal
  exact false_of_world_in_failure_set hmesh (hbadsub.trans hsub) hunit hL herr hdur
    (fun _ hz => hz.2) hq

/-- The two-tangent higher jets give a quantitative failure estimate
under the unchanged original scalar-normal prior. The exponent and
threshold precede the actual world, graph and original indexed lines. -/
theorem native_jet_small_grid_failure (d : ℝ) (hd : 0 ≤ d) (hd1 : d < 1)
    (M : ℕ) (hM : 2 ≤ M) (c_h : ℝ) (hch : 0 < c_h) :
    ∃ cζ : ℝ, 0 < cζ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ ι : Type) [MeasurableSpace Λ] [MeasurableSpace ι]
        (ν : Measure Λ) (cz : Λ → Fin 7 → ℝ) (E Eref : Set (Λ × ℝ))
        (F : ℝ → Fin 2 → ℝ) (piece : ℝ → Λ → Fin 7 → ℤ)
        (K ζ : ℝ) (T : ℕ),
      K ≤ N^α → N^(-c_h)/K ≤ ((2:ℝ)^T)⁻¹ →
      ((2:ℝ)^T)⁻¹ ≤ K*N^(-c_h) → ζ ≤ ((2:ℝ)^T)⁻¹^cζ →
      ScalarNormal ν cz E F piece K ζ d → E ⊆ Eref → MeasurableSet Eref →
      (∀ z ∈ Eref, z.2 ∈ Icc (0:ℝ) 1) →
      ∀ (lab : Λ × ℝ → ι) (G : Λ × ℝ → Fin 3 → ℝ),
      Measurable lab → MeasurableSet {q : ι × ι | q.1 = q.2} → Measurable G →
      ∀ (c : Λ → Fin 7 → ℝ) (B graphError rowError : ℝ), 0 ≤ B →
      (∀ z ∈ E, |c z.1 1| ≤ B ∧ |c z.1 2| ≤ B ∧ |c z.1 4| ≤ B ∧ |c z.1 6| ≤ B) →
      (∀ z ∈ E, |c z.1 1+2*c z.1 2*z.2-
        (G z 0+G z 1*c z.1 4+G z 2*c z.1 6)| ≤ graphError) →
      (∀ z ∈ E, ∀ i : Fin 2, |G z i.succ-F z.2 i| ≤ rowError) →
      (∀ z ∈ E, ∀ v, (z.1,v) ∈ E → v ∈ dyadicBlock T z.2 → lab (z.1,v)=lab z) →
      ∀ (mesh err' dur' : ℝ) (L : ℤ), 0 < mesh →
      3*B+(1+2*B)*N^ε ≤ mesh*(L-1) →
      graphError+(1+2*B)*(rowError+((2:ℝ)^T)⁻¹^((M:ℝ)+1/8))+
        (M+1)*mesh ≤ err' → dur' ≤ ((2:ℝ)^T)⁻¹*N^(-ε) →
      (ν.prod volume) (E \ {z | NativeGridQualified Eref lab G M T mesh L err' dur' z}) <
        ENNReal.ofReal (N^(-α)) := by
  obtain ⟨cζ,hcζ,hnext⟩ := nativeJetQualificationStatement d hd hd1 M hM c_h hch
  refine ⟨cζ,hcζ,fun ε hε => ?_⟩
  obtain ⟨α,hα,N₀,hN₀,hgood⟩ := hnext ε hε
  refine ⟨α,hα,N₀,hN₀,?_⟩
  intro N hN Λ ι _ _ ν cz E Eref F piece K ζ T hK hTlo hThi hζ hSN
    hsub hEref hunit lab G hlab hdiag hG c B graphError rowError hB hjets hgraph hrow
    hlabel mesh err' dur' L hmesh hL herr hdur
  have hN1 : 1 ≤ N := hN₀.trans hN
  have hNpos : 0 < N := zero_lt_one.trans_le hN1
  have hHpos : 0 < N^α := Real.rpow_pos_of_pos hNpos _
  have hKpos : 0 < K := zero_lt_one.trans_le hSN.one_le_K
  have hTlo' : N^(-c_h)/(N^α) ≤ ((2:ℝ)^T)⁻¹ :=
    (div_le_div_of_nonneg_left (Real.rpow_nonneg hNpos.le _) hKpos hK).trans hTlo
  have hThi' : ((2:ℝ)^T)⁻¹ ≤ N^α*N^(-c_h) :=
    hThi.trans (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hNpos.le _))
  have hfail := native_grid_failure_mass_lt hSN hK hsub hEref hunit lab hlab hdiag G hG
    M T mesh (3*B+(1+2*B)*N^ε)
    (graphError+(1+2*B)*(rowError+((2:ℝ)^T)⁻¹^((M:ℝ)+1/8)))
    (((2:ℝ)^T)⁻¹*N^(-ε)) err' dur' L hmesh hL herr hdur (by
      intro E₁ hE₁ hnormal
      exact hgood N hN Λ ν cz E₁ F piece (N^α) ζ T le_rfl hTlo' hThi' hζ hnormal
        ι lab c G B graphError rowError hB
        (fun z hz => hjets z (hE₁ hz)) (fun z hz => hgraph z (hE₁ hz))
        (fun z hz => hrow z (hE₁ hz))
        (fun z hz v hv hb => hlabel z (hE₁ hz) v (hE₁ hv) hb))
  simpa only [Real.rpow_neg hNpos.le] using hfail

/-- Original reference weights pay the exceptional mass once, without
a factor for the number of worlds or states. -/
theorem weighted_failure_mass_le {I : Type*} [Fintype I]
    (weight failure : I → ENNReal) (budget : ENNReal)
    (hweight : ∑ i, weight i ≤ 1)
    (hfailure : ∀ i, failure i ≤ budget * weight i) :
    ∑ i, failure i ≤ budget := by
  calc
    _ ≤ ∑ i, budget * weight i := Finset.sum_le_sum fun i _ => hfailure i
    _ = budget * ∑ i, weight i := (Finset.mul_sum _ _ _).symm
    _ ≤ budget * 1 := mul_le_mul' le_rfl hweight
    _ = budget := mul_one _

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
