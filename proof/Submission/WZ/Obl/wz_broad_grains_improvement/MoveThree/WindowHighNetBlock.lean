-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.WindowHighNetBlock.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/WindowHighNetBlock.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BoundedHighNetBlock
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockWindowRows

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric

noncomputable section

/-- All high carriers of a single old block, with their actual growing windows
at the original long length. No common angular scale is assumed. -/
structure WindowHighNetBlock {ω ζ δ ξ b ρ c β τ : ℝ} {p n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    {D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y}
    {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
    (A : BlockAngularData D R G β τ) (hδ : 0 < δ)
    (σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp : ℝ) (d : ℕ) where
  high : HighNetBlock A σ Cnet e t ν d
  carriers : ∀ l ∈ high.nets.highLabels, ∀ j : Fin (high.nets.N l),
    ∃ B : PhysicalCarrierBox high.nets loss (2 * ν) l j,
      ∃ Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂,
        Nonempty (CarrierWindowRows Q widthJump fillExp)

/-- The same cutoff constructs the fixed-length windows for every high
carrier and every old block, after the ambient shading has been cleared. -/
theorem window_high_net_block_uniform
    {ω t loss β₂ q₀ jump jump' τ₂ widthJump s h rowExp fillExp : ℝ}
    (hβ : 0 < β₂) (hwidth : 0 < widthJump) (hwidthgap : β₂ + 3 * widthJump < q₀)
    (hs : 0 < s) (hsjump : s ≤ jump') (hhu : h < rowExp)
    (hloss : 0 ≤ loss) (hfill : 3 * rowExp + s + loss < fillExp)
    (hmass : t + τ₂ + loss < h) (hsmall : loss < ω / 100) (hjumpgap : jump' < jump) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ : ℝ,
      ∀ hδ : 0 < δ, δ ≤ d₀ →
      ∀ {σ ζ ξ b ρ c β τ Cnet e ν : ℝ} {p n d : ℕ}
        {x v : Fin n → V} {Y : Fin n → Set V}
        {D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y}
        {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
        {A : BlockAngularData D R G β τ}
        (H : BoundedClippedHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂
          rowExp fillExp (1 / 2 ^ 35) d),
      (∀ i, ‖v i‖ = 1) → (∀ i, D.Z i ⊆ T δ (x i) (v i)) →
      (∀ i, Disjoint (D.Z i) (WangZahlLot.Obl.wz_coarse_tube_grains.RIS.tubeEnds δ c (x i) (v i))) →
      Nonempty (WindowHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ widthJump fillExp d) := by
  obtain ⟨dW, hdW, hdW1, HW⟩ := block_window_rows_uniform hβ hwidth hwidthgap
    hs hsjump hhu hloss hfill
  obtain ⟨dM, hdM, hdM1, HM⟩ := const_absorption
    (C := firstFillingMassConstant / 24) (p := t + τ₂ + loss) (q := h)
    (by norm_num [firstFillingMassConstant]) hmass
  obtain ⟨dS, hdS, hdS1, HS⟩ := renorm_radius_small hsmall
  obtain ⟨dG, hdG, hdG1, HG⟩ := renorm_growth
    (t := jump') (t0 := jump) (vLoss := 0) (by simpa using hjumpgap)
  refine ⟨min dW (min dM (min dS dG)), by positivity,
    (min_le_left _ _).trans hdW1, ?_⟩
  intro δ hδ hδ0 σ ζ ξ b ρ c β τ Cnet e ν p n d x v Y D R G A H hv hZT hclear
  obtain ⟨hδW, hδM, hδS, hδG⟩ : δ ≤ dW ∧ δ ≤ dM ∧ δ ≤ dS ∧ δ ≤ dG := by
    simpa only [le_min_iff] using hδ0
  have hδ1 : δ ≤ 1 := (hδW.trans hdW1).trans (by norm_num)
  have hρ := (D.dimensions hδ).2.1
  have hradius := HS δ ρ hδ hδS D.scale_stop
  have hbase : 2 * ρ ≤ 1 / 100 := by
    have hp : 1 ≤ δ ^ (-loss) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    nlinarith only [hρ, hp, hradius]
  have hmass' : δ ^ h ≤ (24 / firstFillingMassConstant) * δ ^ (t + τ₂ + loss) := by
    have hh := mul_le_mul_of_nonneg_left (HM δ hδ hδM)
      (by norm_num [firstFillingMassConstant] : 0 ≤ 24 / firstFillingMassConstant)
    have he : (24 / firstFillingMassConstant) * (firstFillingMassConstant / 24 * δ ^ h) =
        δ ^ h := by norm_num [firstFillingMassConstant]; ring
    rwa [he] at hh
  refine ⟨{high := H.high, carriers := ?_}⟩
  intro l hl j
  obtain ⟨B, Q, hmax, _⟩ := H.carriers l hl j
  have hslab : B.slabWidth ≤ 1 / 8 :=
    (B.slabWidth_bound hδ hδ1 hloss).trans (by nlinarith only [hradius])
  have hgrow : δ ^ (-jump') * (2 * ρ) ≤ Q.scale := by
    simpa only [neg_zero, Real.rpow_zero, mul_one] using
      HG δ ρ Q.scale hδ hδG hρ.le Q.growth
  exact ⟨B, Q, HW δ hδ hδW Q (Finset.mem_filter.mp hl).1 hv hZT hclear
    hbase hslab hgrow hmax hmass'⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
