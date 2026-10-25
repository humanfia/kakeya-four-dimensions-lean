-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BoundedConcentration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BoundedConcentration.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BoundedHighNetBlock
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.FrozenClear

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric

noncomputable section

/-- The original frozen stage yields a gain, its terminal local-count
condition, or actual second filled packets in every retained high carrier.
The cap and every intermediate parameter are uniform in the input family. -/
theorem gain_terminal_or_bounded_clipped_concentration {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000)
    (hε : 0 < ε) (hεζ : ε ≤ ζ / 100) (angleMax : ℝ) (hangleMax : 0 < angleMax) :
    ∃ (β τ ξ b t ν e Cnet loss capLoss α κ θ d₀ : ℝ) (p d : ℕ),
      0 < β ∧ β ≤ 1 ∧ β ≤ ζ * σ / 128 ∧ 0 < τ ∧
      0 < ξ ∧ ξ ≤ ε / 4 ∧ ξ ≤ 1 ∧ 0 < b ∧ b ≤ ξ / 384 ∧
      0 < t ∧ t ≤ ν / 50 ∧ τ + 21 * ξ / 40 ≤ t ∧
      0 < ν ∧ ν ≤ ε / 1000 ∧ ν ≤ ζ * σ / 100 ∧
      0 < e ∧ e ≤ ε / 1000 ∧ e ≤ ζ * σ / 128 ∧ 0 < Cnet ∧
      0 < loss ∧ loss ≤ ε / 100000 ∧ ν ≤ loss / 10 ∧ t ≤ loss / 500 ∧
      0 < capLoss ∧ capLoss ≤ loss * (ω + σ) / 4 ∧
      0 < α ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1 / 4096 ∧ 0 < p ∧ 0 < d ∧
      ∀ δ h : ℝ, ∀ hδ : 0 < δ, δ ≤ d₀ → 0 ≤ h → h ≤ θ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ ρ c, J ω ζ δ h ρ c n x v Y 2 →
      Gain σ ω κ α δ n Y ∨ J ω ζ δ ε ρ c n x v Y 3 ∨
        ∃ Y' : Fin n → Set V,
          (∀ i, Y' i ⊆ Y i) ∧
          O (δ ^ (ε / 8)) * ∑ i, μ (Y i) ≤ ∑ i, μ (Y' i) ∧
          A δ (ξ / 4) (δ ^ (-(ξ / 4))) (δ ^ (-(ξ / 4))) n x v Y' ∧
          (∀ q ∈ ⋃ i, Y' i, ∀ r : ℝ, 0 < r → r ≤ 1 →
            μ ((⋃ i, Y' i) ∩ ball q r) ≤
              O (δ ^ (-capLoss) * (δ / r) ^ (ω + σ) * r ^ 3)) ∧
          ∃ (D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y')
            (F : AngularBlockFamily D β τ),
            ∀ R : F.blocks,
              Nonempty (BoundedClippedHighNetBlock (F.angular R) hδ σ Cnet e t ν loss
                (ω * ζ / 100) (ζ / 4) (ζ / 100) loss (5 * loss) (100 * loss) angleMax d) := by
  let loss := ε / 100000
  have hloss : 0 < loss := by dsimp [loss]; positivity
  have hlossζ : loss ≤ ζ / 10000000 := by dsimp [loss]; linarith
  have hlosssmall : loss < ω / 100 := by dsimp [loss]; linarith
  have hs : 0 < ω + σ := add_pos hω hσ
  let ε₀ := min (ε / 1000) (loss * (ω + σ) / 1000)
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (by positivity)
  have hε₀ε : ε₀ ≤ ε := (min_le_left _ _).trans (by linarith)
  have hε₀loss : ε₀ ≤ 100 * loss := by
    have hh := min_le_left (ε / 1000) (loss * (ω + σ) / 1000)
    change ε₀ ≤ ε / 1000 at hh
    dsimp [loss]
    linarith
  have hε₀cap : ε₀ ≤ loss * (ω + σ) / 1000 := min_le_right _ _
  let capLoss := min (ζ * σ / 32) (loss * (ω + σ) / 4)
  have hcapLoss : 0 < capLoss := lt_min (by positivity) (by positivity)
  have hcapMax : capLoss ≤ ζ * σ / 16 :=
    (min_le_left _ _).trans (by nlinarith [mul_pos hζ hσ])
  have hcaploss : capLoss ≤ loss * (ω + σ) / 4 := min_le_right _ _
  obtain ⟨β, τ, ξ, b, t, ν, e, Cnet, α, κ, θ, dH, p, d,
    hβ, hβ1, hβζ, hτ, hξ, hξε, hξ1, hb, hbξ, ht, htν, hmass,
    hν, hνε, hνζ, he, heε, heζ, hCnet, hα, hκ, hθ, hθε, hdH, hdH1, hp, hd, HH⟩ :=
    gain_terminal_or_high_net_concentration_with_cap hσ hσhalf hω hE hζ hε₀ hcapLoss hcapMax
  have hνloss : ν ≤ loss / 10 := by linarith
  have htloss : t ≤ loss / 500 := by linarith
  have hνcap : ν ≤ loss * (ω + σ) / 1000000 := by linarith
  have hcapgap : capLoss + 2 * ν < loss * (ω + σ) := by
    nlinarith [mul_pos hloss hs]
  have hβ₂ : 0 < ω * ζ / 100 := by positivity
  have hβ₂1 : ω * ζ / 100 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hω1 hζ.le
    nlinarith
  have hangle : ω * ζ / 100 + 3 * (ζ / 100) < ζ / 4 := by
    have hh := mul_le_mul_of_nonneg_right hω1 hζ.le
    nlinarith
  obtain ⟨dC, hdC, hdC1, HC⟩ := bounded_clipped_high_net_block_uniform
    (ω := ω) (ζ := ζ) (s := ω + σ) (capLoss := capLoss)
    (ν := ν) (t := t) (loss := loss) (β₂ := ω * ζ / 100) (q₀ := ζ / 4)
    (jump := ζ / 100) (jump' := ζ / 200) (τ₂ := loss) (sfill := loss)
    (h := 4 * loss) (rowExp := 5 * loss) (fillExp := 100 * loss)
    hs hν hcapgap hβ₂ hβ₂1 (by positivity) hangle hloss
    (by linarith) hloss (by linarith) (by linarith) hloss.le (by linarith)
    (by linarith) hlosssmall (by linarith) hangleMax
  obtain ⟨θL, dL, hθL, hdL, HL⟩ := Clear.stage_length_small_frozen hω hω1 hζ hζω
  obtain ⟨dS, hdS, HS⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (p := ω ^ 2 * ζ / 40000) (by positivity) (K := 1 / 8) (by norm_num)
  refine ⟨β, τ, ξ, b, t, ν, e, Cnet, loss, capLoss, α, κ, min θ θL,
    min dH (min dC (min dL dS)), p, d,
    hβ, hβ1, hβζ, hτ, hξ, by linarith, hξ1, hb, hbξ, ht, htν, hmass,
    hν, by linarith, hνζ, he, by linarith, heζ, hCnet,
    hloss, le_rfl, hνloss, htloss, hcapLoss, hcaploss, hα, hκ, lt_min hθ hθL,
    (min_le_left _ _).trans (hθε.trans hε₀ε), by positivity,
    (min_le_left _ _).trans hdH1, hp, hd, ?_⟩
  intro δ h hδ hδ0 hh hhθ n x v Y hA ρ c hJ
  obtain ⟨hδH, hδC, hδL, hδS⟩ : δ ≤ dH ∧ δ ≤ dC ∧ δ ≤ dL ∧ δ ≤ dS := by
    simpa only [le_min_iff] using hδ0
  have hδ1 : δ ≤ 1 := (hδH.trans hdH1).trans (by norm_num)
  have hcsmall : 8 * c ≤ 1 := by
    have hh := (HL δ h hδ hδL (hhθ.trans (min_le_right _ _)) n x v Y hA ρ c 2 hJ).1
    have hs := HS δ hδ hδS
    linarith
  rcases HH δ h hδ hδH hh (hhθ.trans (min_le_left _ _)) n x v Y hA ρ c hJ with
    hgain | hterminal | hdata
  · exact Or.inl hgain
  · exact Or.inr (Or.inl (stage_mono hδ hδ1 hε₀ε hterminal))
  obtain ⟨Y', hsub, hYret, hA', hcap, D, F, HF⟩ := hdata
  right; right
  refine ⟨Y', hsub, ?_, hA', hcap, D, F, ?_⟩
  · apply le_trans ?_ hYret
    apply mul_le_mul' _ le_rfl
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : ε₀ / 8 ≤ ε / 8))
  · intro R
    obtain ⟨H⟩ := HF R
    exact HC δ hδ hδC H hcsmall hcap

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
