-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BoundedHighNetBlock.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BoundedHighNetBlock.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedCarrierFilling
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.HighNetConcentration
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BoundedCarrierPackets

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric

noncomputable section

/-- A high-net block with bounded second angles, actual physical carrier boxes, second angular
packets and filled prisms. Every stage retains the original finite indices. -/
structure BoundedClippedHighNetBlock {ω ζ δ ξ b ρ c β τ : ℝ} {p n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    {D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y}
    {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
    (A : BlockAngularData D R G β τ) (hδ : 0 < δ)
    (σ Cnet e t ν loss β₂ q₀ jump τ₂ rowExp fillExp angleMax : ℝ) (d : ℕ) where
  high : HighNetBlock A σ Cnet e t ν d
  carriers : ∀ l ∈ high.nets.highLabels, ∀ j : Fin (high.nets.N l),
    ∃ B : PhysicalCarrierBox high.nets loss (2 * ν) l j,
      ∃ Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂,
        Q.scale ≤ angleMax ∧ Nonempty (Q.Filling rowExp fillExp)

/-- One cutoff supplies all the geometry and analytic budgets for every
actual high carrier of every old block. -/
theorem bounded_clipped_high_net_block_uniform
    {ω ζ s capLoss ν t loss β₂ q₀ jump jump' τ₂ sfill h rowExp fillExp angleMax : ℝ}
    (hs : 0 < s) (hν : 0 < ν) (hcapgap : capLoss + 2 * ν < loss * s)
    (hβ : 0 < β₂) (hβ1 : β₂ ≤ 1) (hjump : 0 < jump)
    (hangle : β₂ + 3 * jump < q₀) (hτ₂ : 0 < τ₂)
    (hoverlap : 0 < ζ / 2 - q₀ - t)
    (hsfill : 0 < sfill) (hsjump : sfill ≤ jump') (hh : h < rowExp)
    (hloss : 0 ≤ loss) (hfill : 3 * rowExp + sfill + loss < fillExp)
    (hmass : t + τ₂ + loss < h) (hsmall : loss < ω / 100) (hjumpgap : jump' < jump) (hangleMax : 0 < angleMax) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ : ℝ,
      ∀ hδ : 0 < δ, δ ≤ d₀ →
      ∀ {σ ξ b ρ c β τ Cnet e : ℝ} {p n d : ℕ}
        {x v : Fin n → V} {Y : Fin n → Set V}
        {D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y}
        {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
        {A : BlockAngularData D R G β τ}
        (H : HighNetBlock A σ Cnet e t ν d),
      8 * c ≤ 1 →
      (∀ q ∈ ⋃ i, Y i, ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ ((⋃ i, Y i) ∩ ball q r) ≤ O (δ ^ (-capLoss) * (δ / r) ^ s * r ^ 3)) →
      Nonempty (BoundedClippedHighNetBlock A hδ σ Cnet e t ν loss β₂ q₀ jump τ₂ rowExp fillExp angleMax d) := by
  obtain ⟨dB, hdB, hdB1, HB⟩ := physical_carrier_box_uniform hs (by linarith : ν < 2 * ν) hcapgap
  obtain ⟨dQ, hdQ, hdQ1, HQ⟩ := bounded_clipped_carrier_angular_data_uniform
    hβ hβ1 hjump hangle hτ₂ hoverlap hangleMax
  obtain ⟨dF, hdF, hdF1, HF⟩ := clipped_carrier_packet_fillings_uniform
    hβ hsfill hsjump hh hloss hfill
  have hk := firstFillingShrink_pos
  have hH : 0 < firstFillingMassConstant := by norm_num [firstFillingMassConstant]
  obtain ⟨dD, hdD, HD⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (by linarith : 0 < ν / 2) (K := firstFillingShrink / (16000 * 6144)) (by positivity)
  obtain ⟨dM, hdM, hdM1, HM⟩ := const_absorption
    (C := firstFillingMassConstant / 24) (p := t + τ₂ + loss) (q := h) (by positivity) hmass
  obtain ⟨dS, hdS, hdS1, HS⟩ := renorm_radius_small hsmall
  obtain ⟨dG, hdG, hdG1, HG⟩ := renorm_growth
    (t := jump') (t0 := jump) (vLoss := 0) (by simpa using hjumpgap)
  refine ⟨min dB (min dQ (min dF (min dD (min dM (min dS dG))))),
    by positivity, ?_, ?_⟩
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans hdQ1)
  intro δ hδ hδ0 σ ξ b ρ c β τ Cnet e p n d x v Y D R G A H hcsmall hcap
  obtain ⟨hδB, hδQ, hδF, hδD, hδM, hδS, hδG⟩ :
      δ ≤ dB ∧ δ ≤ dQ ∧ δ ≤ dF ∧ δ ≤ dD ∧ δ ≤ dM ∧ δ ≤ dS ∧ δ ≤ dG := by
    simpa only [le_min_iff] using hδ0
  have hδ1 : δ ≤ 1 := hδB.trans hdB1
  obtain ⟨ha, hρ, hρ1, hc, _⟩ := D.dimensions hδ
  have hlam : 0 < δ ^ t / firstFillingMassConstant := by positivity
  have hden : δ ^ ν ≤ δ ^ (ν / 2) * firstFillingShrink / (16000 * 6144) := by
    have hh := HD δ hδ hδD
    have hpow : δ ^ ν = δ ^ (ν / 2) * δ ^ (ν / 2) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [hpow]
    have hh' := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hδ.le (ν / 2))
    linarith
  have hradius := HS δ ρ hδ hδS D.scale_stop
  have hbase : 2 * ρ ≤ 1 / 100 := by
    have hp : 1 ≤ δ ^ (-loss) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    nlinarith
  have hmass' : δ ^ h ≤ (24 / firstFillingMassConstant) * δ ^ (t + τ₂ + loss) := by
    have hh := HM δ hδ hδM
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 24 / firstFillingMassConstant)
    have he : (24 / firstFillingMassConstant) * (firstFillingMassConstant / 24 * δ ^ h) =
        δ ^ h := by field_simp
    rwa [he] at hh'
  refine ⟨{high := H, carriers := ?_}⟩
  intro l hl j
  have hlgood := (Finset.mem_filter.mp hl).1
  obtain ⟨B⟩ := HB δ hδ hδB H.nets hlam (by positivity) hcsmall hden hcap l hlgood j
  obtain ⟨Q, hmax⟩ := HQ δ hδ hδQ H.nets l hl j B
  have hslab : B.slabWidth ≤ 1 / 8 :=
    (B.slabWidth_bound hδ hδ1 hloss).trans (by nlinarith only [hradius])
  have hgrow : δ ^ (-jump') * (2 * ρ) ≤ Q.scale := by
    simpa only [neg_zero, Real.rpow_zero, mul_one] using
      HG δ ρ Q.scale hδ hδG hρ.le Q.growth
  exact ⟨B, Q, hmax, HF δ hδ hδF B Q hlgood hbase hslab hgrow hmass'⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
