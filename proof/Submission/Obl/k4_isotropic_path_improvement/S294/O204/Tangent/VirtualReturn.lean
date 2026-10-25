-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.VirtualReturn, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1078,
-- branch x1078, commit c3fccb87c, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/VirtualReturn.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- The assembled virtual return: a direct candidate of the virtual packet below an ancestor
-- returns to the original packet (x1078, o204).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Schedule
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Injective

/-!
# Returning from the virtual packet below an ancestor

`virtualFrame t₀ q c sc` is o280's `PFrame` with unsheared centre `c`, no centre velocity and
`D = q • 1`: time `(t - t₀)/q`, base `(y - c)/q`, velocity unchanged, hidden coordinate times
`sc`. For an ancestor block (clock `TA`, block `jA`) take `t₀ = jA/2^TA`, `q = 2^-TA`, the
ancestor's unsheared centre `c = c_A + t₀ u_A`, and `sc = B / δ(N, rA)`.

`virtual_direct_return`: the direct candidate of the virtual instance (prior
`tanPrior Φ a ν A_A`, assignment `tanLine '' Ab`, residual `tanEvent '' H₀`, unit one, same `N`,
`L - rA`, gain `gain * L / (L - rA)`, depth `rb - rA`, clock `Tb - TA`, block
`jb - jA 2^(Tb - TA)`) is the direct candidate of the original packet. Only a coefficient
budget and the slack `2 ≤ N^(ε - εt)` remain as numerical hypotheses.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split

noncomputable section

/-- The virtual frame of an ancestor: unsheared centre, isotropic dilation, hidden scale. -/
def virtualFrame (t₀ q : ℝ) (c : P2) (sc : ℝ) : PFrame :=
  ⟨⟨t₀, q, c, 0, q • (1 : Matrix (Fin 2) (Fin 2) ℝ)⟩, sc⟩

lemma virtualFrame_det (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) :
    (virtualFrame t₀ q c sc).F.D.det ≠ 0 := by
  simp [virtualFrame, hq]

/-- Image sets: the hypotheses of `directAt_return` on assignments and residual events. -/
theorem directAt_return_image
    (Φ : PFrame) (a : Fin 4 → ℝ) (hq : 0 < Φ.F.q) (hD : Φ.F.D.det ≠ 0)
    (ν : Measure Ln) [SFinite ν] (A₀ Ab : Set Ln) (H₀ H : Set Ev)
    (hAb : MeasurableSet Ab) (hAbA₀ : Ab ⊆ A₀) (h0 : ν A₀ ≠ 0) (hT : ν A₀ ≠ ⊤)
    (hH₀ : MeasurableSet H₀) (hH₀H : H₀ ⊆ H)
    (B δA : ℝ) (hB : 0 < B) (hδA : 0 < δA) (hsc : Φ.sc = B / δA)
    (N L d₁ ρ gain ε rb : ℝ) (Mc Tb jb : ℕ)
    (Nt Lt ρt gaint εt rt : ℝ) (Mct Tt jt : ℕ) (hNt : 0 < Nt)
    (hblock : ∀ t, t ∈ Set.Icc ((jb:ℝ)/(2:ℝ)^Tb) (((jb:ℝ)+1)/(2:ℝ)^Tb) ↔
      (t - Φ.F.t₀)/Φ.F.q ∈ Set.Icc ((jt:ℝ)/(2:ℝ)^Tt) (((jt:ℝ)+1)/(2:ℝ)^Tt))
    (hcoeff : 81 * |δA| * Nt^Mct * residualBudget a 1 ^ 2 * Φ.substBudget ^ 2 ≤ N^Mc)
    (hpar : ∀ agt : ℝ, gaint ≤ agt → agt ≤ 1/8 → rt + 2*agt*Lt ≤ Lt → ∃ ag : ℝ,
      gain ≤ ag ∧ ag ≤ 1/8 ∧ rb + 2*ag*L ≤ L ∧
      δA * (Nt^(ρt*gaint*Lt+εt) * Split.δ Nt (rt + agt*Lt)) ≤
        N^(ρ*gain*L+ε) * Split.δ N (rb + ag*L) ∧
      Nt^(ρt*gaint*Lt+εt) ≤ N^(ρ*gain*L+ε) ∧
      Nt^(ρt*gaint*Lt+εt) * Split.δ N (rb + ag*L) ≤
        N^(ρ*gain*L+ε) * δA * Split.δ Nt (rt + agt*Lt) ∧
      ENNReal.ofReal (N^(-((d₁*ag+ρ*gain)*L) - ε)/(2:ℝ)^Tb) ≤
        ENNReal.ofReal Φ.F.q * ENNReal.ofReal (Nt^(-((d₁*agt+ρt*gaint)*Lt) - εt)/(2:ℝ)^Tt))
    (htan : DirectAt Nt Lt (tanPrior Φ a ν A₀) 1 Mct d₁ ρt gaint εt rt Tt jt
      (tanLine Φ a '' Ab) (tanEvent Φ a '' H₀)) :
    DirectAt N L ν B Mc d₁ ρ gain ε rb Tb jb Ab H := by
  have hsc0 : Φ.sc ≠ 0 := by rw [hsc]; exact div_ne_zero hB.ne' hδA.ne'
  have hLe := measurableEmbedding_tanLine Φ a hq.ne' hD hsc0
  have hEe := measurableEmbedding_tanEvent Φ a hq.ne' hD hsc0
  have hLi := tanLine_injective Φ a hq.ne' hD hsc0
  have hEi := tanEvent_injective Φ a hq.ne' hD hsc0
  refine directAt_return Φ a hq ν A₀ Ab (tanLine Φ a '' Ab) H (tanEvent Φ a '' H₀) hAb hAbA₀ h0 hT
    (hLe.measurableSet_image.mpr hAb) (hEe.measurableSet_image.mpr hH₀)
    (fun l hl => ⟨l, hl, rfl⟩) ?_ ?_ B δA hB hδA hsc N L d₁ ρ gain ε rb Mc Tb jb
    Nt Lt ρt gaint εt rt Mct Tt jt hNt (fun t ht => (hblock t).mp ht)
    (fun t ht => (hblock t).mpr ht) hcoeff hpar htan
  · rintro l - ⟨l', hl', hll'⟩
    rwa [← hLi hll']
  · rintro p - ⟨p', hp', hpp'⟩
    exact hH₀H (by rwa [← hEi hpp'])

/-- The assembled return from the virtual packet below an ancestor, at the same `N`. -/
theorem virtual_direct_return
    (ν : Measure Ln) [SFinite ν] (A_A Ab : Set Ln) (H₀ H : Set Ev)
    (hAb : MeasurableSet Ab) (hAbA : Ab ⊆ A_A) (h0 : ν A_A ≠ 0) (hT : ν A_A ≠ ⊤)
    (hH₀ : MeasurableSet H₀) (hH₀H : H₀ ⊆ H)
    (c : P2) (a : Fin 4 → ℝ) (jA TA jb Tb : ℕ) (hTT : TA ≤ Tb) (hj : jA * 2 ^ (Tb - TA) ≤ jb)
    (B N L d₁ ρ gain ε εt rA rb : ℝ) (Mc Mct : ℕ) (hB : 0 < B) (hN : 1 ≤ N)
    (hgain : 0 ≤ gain) (hrA : 0 ≤ rA) (hrAL : rA < L) (hεt : εt ≤ ε)
    (htwo : 2 ≤ N ^ (ε - εt))
    (hcoeff : 81 * |Split.δ N rA| * N^Mct * residualBudget a 1 ^ 2 *
      (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ c (B / Split.δ N rA)).substBudget ^ 2 ≤ N^Mc)
    (htan : DirectAt N (L - rA)
      (tanPrior (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ c (B / Split.δ N rA)) a ν A_A)
      1 Mct d₁ ρ (gain * L / (L - rA)) εt (rb - rA) (Tb - TA) (jb - jA * 2 ^ (Tb - TA))
      (tanLine (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ c (B / Split.δ N rA)) a '' Ab)
      (tanEvent (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ c (B / Split.δ N rA)) a '' H₀)) :
    DirectAt N L ν B Mc d₁ ρ gain ε rb Tb jb Ab H := by
  set Φ := virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ c (B / Split.δ N rA) with hΦ
  have hq : 0 < Φ.F.q := by simp [hΦ, virtualFrame]
  have hD : Φ.F.D.det ≠ 0 := virtualFrame_det _ _ _ _ (by positivity)
  exact directAt_return_image Φ a hq hD ν A_A Ab H₀ H hAb hAbA h0 hT hH₀ hH₀H
    B (Split.δ N rA) hB (δ_pos _ _) rfl N L d₁ ρ gain ε rb Mc Tb jb
    N (L - rA) ρ (gain * L / (L - rA)) εt (rb - rA) Mct (Tb - TA) (jb - jA * 2 ^ (Tb - TA))
    (by linarith) (block_iff_virtual TA Tb jA jb hTT hj) hcoeff
    (hpar_virtual N L d₁ ρ gain ε εt rA rb Tb TA hN hgain hrA hrAL hεt htwo hTT) htan

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
