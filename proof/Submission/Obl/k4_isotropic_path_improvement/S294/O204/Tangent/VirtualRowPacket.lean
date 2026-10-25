-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.VirtualRowPacket, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1080,
-- branch x1080, commit 5a0a478a0, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/VirtualRowPacket.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- o295's RowPacket at exactly the virtual instance of x1078's `VirtualPPP` (x1080, o204).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.RowTransport
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Orchestration

/-!
# The forward transport at `VirtualPPP`'s data

`virtualRowPacket_of_relative` restates `rowPacket_of_relative` at the literal data of the virtual
instance used by `Tangent.Orchestration.VirtualPPP`: frame `vFrame N L sA jA TA cA B`, tangent
prior, hidden unit one, depth `rb - sA*L`, clock `Tb - TA`, block `jb - jA*2^(Tb-TA)`, centre
`2^TA • (cb + (jA/2^TA) • ub - cA)`, signal `normTest δ(N, sA L) RA`, image sets, length
`L - sA*L`, gain `gain*L/(L - sA*L)` and slack `2κ`. With o295 (`RowPacket → PhysicalPotentialPacket`)
it supplies the `PhysicalPotentialPacket` conjunct of `VirtualPPP` from original-unit clauses.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory MvPolynomial
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split

noncomputable section

lemma image_tanLine_eq (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0) (X : Set Ln) :
    tanLine (isoPFrame t₀ q c sc) 0 '' X = invLine t₀ q c sc ⁻¹' X := by
  apply Set.Subset.antisymm
  · intro l' hl'
    obtain ⟨l, hl, hll⟩ := hl'
    rw [Set.mem_preimage, ← hll, invLine_tanLine t₀ q c sc hq hsc]
    exact hl
  · intro l' hl'
    exact ⟨invLine t₀ q c sc l', hl', tanLine_invLine t₀ q c sc hq hsc l'⟩

lemma image_tanEvent_eq (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0) (X : Set Ev) :
    tanEvent (isoPFrame t₀ q c sc) 0 '' X = invEvent t₀ q c sc ⁻¹' X := by
  apply Set.Subset.antisymm
  · intro p' hp'
    obtain ⟨p, hp, hpp⟩ := hp'
    rw [Set.mem_preimage, ← hpp, invEvent_tanEvent t₀ q c sc hq hsc]
    exact hp
  · intro p' hp'
    exact ⟨invEvent t₀ q c sc p', hp', tanEvent_invEvent t₀ q c sc hq hsc p'⟩

lemma relCenter_eq (TA T' jA j' : ℕ) (cA cb ub : P2) :
    relCenter TA T' jA j' cA cb ub = ((2:ℝ)^TA) • (cb + ((jA:ℝ)/(2:ℝ)^TA) • ub - cA) := by
  unfold relCenter
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, inv_inv]
  push_cast
  rw [pow_add]
  field_simp
  ring

lemma vFrame_eq (N L sA : ℝ) (jA TA : ℕ) (cA : P2) (B : ℝ) :
    vFrame N L sA jA TA cA B =
      isoPFrame ((jA : ℝ) * ((2 : ℝ) ^ TA)⁻¹) ((2 : ℝ) ^ TA)⁻¹ cA (B / Split.δ N (sA * L)) := by
  simp only [vFrame, virtualFrame, isoPFrame, isoFrame, div_eq_mul_inv]

/-- The forward transport at the literal data of `VirtualPPP`. -/
theorem virtualRowPacket_of_relative (M Ep : ℕ) (precision loss N L d₁ gain κ : ℝ)
    (ν : Measure Ln) [SFinite ν] (B : ℝ) (hB : 0 < B) (sA : ℝ)
    (TA jA : ℕ) (cA : P2) (A_A : Set Ln) (hAA : MeasurableSet A_A) (hAA0 : ν A_A ≠ 0)
    (hAAT : ν A_A ≠ ⊤) (RA : Po) (hRA : RA.totalDegree ≤ 2)
    (rb : ℝ) (T' j' : ℕ) (cb ub : P2) (Ab : Set Ln) (hAb : MeasurableSet Ab) (hAbA : Ab ⊆ A_A)
    (Fb H₀ : Set Ev)
    (h : RelativeRowPacket M Ep precision loss N (L - sA * L) d₁ (gain * L / (L - sA * L))
      (2 * κ) ν B TA jA (Split.δ N (sA * L)) RA T' j' cb ub
      (Split.δ N (sA * L) * Split.δ N (rb - sA * L)) (Split.δ N (rb - sA * L)) Ab Fb H₀) :
    RowPacket M Ep precision loss N (L - sA * L) d₁ (gain * L / (L - sA * L)) (2 * κ)
      (tanPrior (vFrame N L sA jA TA cA B) 0 ν A_A) 1 (rb - sA * L) T' j'
      (((2:ℝ)^TA) • (cb + ((jA:ℝ)/(2:ℝ)^TA) • ub - cA)) ub
      ((vFrame N L sA jA TA cA B).normTest (Split.δ N (sA * L)) RA)
      (tanLine (vFrame N L sA jA TA cA B) 0 '' Ab)
      (tanEvent (vFrame N L sA jA TA cA B) 0 '' Fb)
      (tanEvent (vFrame N L sA jA TA cA B) 0 '' H₀) := by
  have haA : 0 < Split.δ N (sA * L) := by unfold Split.δ; positivity
  have haB : 0 < Split.δ N (sA * L) * Split.δ N (rb - sA * L) := by
    have : 0 < Split.δ N (rb - sA * L) := by unfold Split.δ; positivity
    positivity
  have hq : ((2 : ℝ) ^ TA)⁻¹ ≠ 0 := by positivity
  have hsc : B / Split.δ N (sA * L) ≠ 0 := (div_pos hB haA).ne'
  have key := rowPacket_of_relative M Ep precision loss N (L - sA * L) d₁ (gain * L / (L - sA * L))
    (2 * κ) ν B hB TA jA cA A_A hAA hAA0 hAAT (Split.δ N (sA * L)) haA RA hRA T' j' cb ub
    (Split.δ N (sA * L) * Split.δ N (rb - sA * L)) (rb - sA * L) haB rfl Ab hAb hAbA Fb H₀ h
  simp only at key
  rw [vFrame_eq, image_tanLine_eq _ _ _ _ hq hsc, image_tanEvent_eq _ _ _ _ hq hsc,
    image_tanEvent_eq _ _ _ _ hq hsc, ← relCenter_eq TA T' jA j' cA cb ub]
  exact key

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
