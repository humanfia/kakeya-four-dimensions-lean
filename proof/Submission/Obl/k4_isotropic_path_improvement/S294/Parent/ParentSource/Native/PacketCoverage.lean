-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PacketCoverage, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PacketCoverage.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PacketCoverage.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PacketCoverage.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFineHistory
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeConditionalOmissions

/-! Almost every prepared incidence has an actual positive original packet.
The packet code is the table fixed before selecting the residual. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

theorem preparedResidualLaw_positive_weight {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X) :
    ∀ᵐ z ∂preparedResidualLaw μ ω H, 0 < ω z.1 := by
  have hD : MeasurableSet {z : Fin W × X | ¬ 0 < ω z.1} :=
    (measurableSet_lt measurable_const ((measurable_of_countable ω).comp measurable_fst)).compl
  apply ae_iff.mpr
  rw [preparedResidualLaw_apply μ ω H _ hD]
  have hzero (w : Fin W) : ENNReal.ofReal (ω w) *
      μ w (H w ∩ {x | (w, x) ∈ {z : Fin W × X | ¬ 0 < ω z.1}}) = 0 := by
    by_cases hw : 0 < ω w
    · simp only [mem_ofPred_eq, hw, not_true_eq_false, ofPred_false, inter_empty, measure_empty, mul_zero]
    · rw [ENNReal.ofReal_of_nonpos (le_of_not_gt hw), zero_mul]
  simp only [hzero, Finset.sum_const_zero, ENNReal.zero_div]

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

noncomputable def PreparedAngularPath.zeroCurrentOmissions (b : Fin p.C) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := by
  classical
  exact if Q.currentParentLaw b univ = 0 then Q.residual (p.γ b) ∩ p.F b else ∅

theorem PreparedAngularPath.ae_current_packet_positive (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (i : ℕ) (hi : i < m) :
    ∀ᵐ z ∂Q.law, z.2 ∈ Q.residual z.1 →
      ∀ b, p.lev b = i → p.γ b = z.1 → z.2 ∈ p.F b → Q.currentParentLaw b univ ≠ 0 := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hmeas (b : Fin p.C) : MeasurableSet (Q.zeroCurrentOmissions b) := by
    unfold zeroCurrentOmissions
    split_ifs
    · exact (Q.residual_measurable _).inter (hF b)
    · exact MeasurableSet.empty
  have hsub (b : Fin p.C) : Q.zeroCurrentOmissions b ⊆ Q.residual (p.γ b) ∩ p.F b := by
    unfold zeroCurrentOmissions
    split_ifs
    · exact Subset.rfl
    · exact empty_subset _
  have hcap (b : Fin p.C) (_ : p.lev b = i) :
      ProbabilityTheory.cond (Q.currentParentLaw b) univ (Q.zeroCurrentOmissions b) ≤ 0 := by
    by_cases hb : Q.currentParentLaw b univ = 0
    · rw [ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hb]
      simp
    · simp only [zeroCurrentOmissions, ite_eq_right hb, measure_empty, le_refl]
  have hnull := Q.conditional_omission_prepared_mass_le hd hp hHE hH i hi
    Q.zeroCurrentOmissions hmeas hsub 0 hcap
  have hae : ∀ᵐ z ∂Q.law, z ∉ labelledSupport (Q.packetFamilyResidual i Q.zeroCurrentOmissions) :=
    ae_iff.mpr (by simpa only [not_not, setOf_mem_eq] using (le_antisymm hnull zero_le))
  filter_upwards [hae] with z hz hzres b hbi hbγ hzb hbzero
  apply hz
  refine ⟨b, hbi, hbγ, ?_⟩
  simpa only [zeroCurrentOmissions, ite_eq_left hbzero, mem_inter_iff, hbγ] using ⟨hzres, hzb⟩

theorem PreparedAngularPath.coarse_code_eq_packetCoding
    (q : PacketCoding p (d.ν k)) (hF : ∀ b, MeasurableSet (p.F b))
    (b : Fin p.C) (c : ℕ)
    (hPacket : ∀ z ∈ Q.coarseSupport (p.lev b) c, z.1 = p.γ b ∧ z.2 ∈ p.F b)
    (hCpos : Q.law (Q.coarseSupport (p.lev b) c) ≠ 0) : c = q.code b := by
  have hcore : ∀ᵐ z ∂Q.law, z.2 ∈ q.core z.1 :=
    preparedResidualLaw_original_ae (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual
      q.core (q.measurableSet_core hF) q.ae_core
  have heq : Q.law (Q.coarseSupport (p.lev b) c ∩ labelledSupport q.core) =
      Q.law (Q.coarseSupport (p.lev b) c) := by
    apply measure_congr
    filter_upwards [hcore] with z hz
    simp only [mem_inter_iff, labelledSupport, mem_ofPred_eq, hz, and_true]
  obtain ⟨z, hzC, hzcore⟩ := nonempty_of_measure_ne_zero (heq.trans_ne hCpos)
  have hpacket := hPacket z hzC
  have hcode := q.code_eq_of_mem_core z.1 hzcore b hpacket.1.symm hpacket.2
  exact hzC.2.symm.trans hcode

theorem PreparedAngularPath.ae_current_coarse_coverage (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (q : PacketCoding p (d.ν k)) (i : ℕ) (hi : i < m) (code : Fin p.C → ℕ)
    (hcode : ∀ b, p.lev b = i → 0 < d.ω k (p.γ b) → Q.currentParentLaw b univ ≠ 0 →
      (∀ z ∈ Q.coarseSupport (p.lev b) (code b), z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
      Q.law (Q.coarseSupport (p.lev b) (code b)) ≠ 0) :
    ∀ᵐ z ∂Q.law, ∃ b, p.lev b = i ∧ p.γ b = z.1 ∧ z.2 ∈ p.F b ∧
      0 < d.ω k (p.γ b) ∧ Q.currentParentLaw b univ ≠ 0 ∧
      finitePacketHistory p.lev p.γ p.F i z = code b := by
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hcore : ∀ᵐ z ∂Q.law, z.2 ∈ q.core z.1 :=
    preparedResidualLaw_original_ae (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual
      q.core (q.measurableSet_core hF) q.ae_core
  have hres : ∀ᵐ z ∂Q.law, z.2 ∈ Q.residual z.1 := ae_iff.mpr
    (preparedResidualLaw_support (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual Q.residual_measurable)
  have hweight : ∀ᵐ z ∂Q.law, 0 < d.ω k z.1 :=
    preparedResidualLaw_positive_weight (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual
  have hpositive := Q.ae_current_packet_positive hd hp hHE hH i hi
  have hcover := hp.covered_at_level Q.residual i hi
    (fun w => (Q.residual_subset w).trans ((Q.base_subset w).trans (hH w)))
  filter_upwards [hcore, hres, hweight, hpositive] with z hzcore hzres hzweight hzpositive
  obtain ⟨b, hbi, hbγ, hzb⟩ := hcover z.1 hzres
  have hω : 0 < d.ω k (p.γ b) := by simpa only [hbγ] using hzweight
  have hcur := hzpositive hzres b hbi hbγ hzb
  have hc := hcode b hbi hω hcur
  have hfixed := Q.coarse_code_eq_packetCoding q hF b (code b) hc.1 hc.2
  refine ⟨b, hbi, hbγ, hzb, hω, hcur, ?_⟩
  have hh := q.code_eq_of_mem_core z.1 hzcore b hbγ hzb
  rw [hbi, ← hfixed] at hh
  exact hh

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
