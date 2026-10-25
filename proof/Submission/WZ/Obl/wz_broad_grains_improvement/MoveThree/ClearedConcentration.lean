-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClearedConcentration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClearedConcentration.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BoundedConcentration
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClearedAmbient

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric

noncomputable section

/-- The original frozen stage yields a gain, its terminal local-count
condition, or actual second filled packets in every retained high carrier.
The cap and every intermediate parameter are uniform in the input family. -/
theorem gain_terminal_or_cleared_bounded_concentration {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000)
    (hε : 0 < ε) (hεζ : ε ≤ ζ / 100) (angleMax Kc : ℝ) (hangleMax : 0 < angleMax) (hKc : 1 ≤ Kc) :
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
          (∀ i, Disjoint (Y' i) (WangZahlLot.Obl.wz_coarse_tube_grains.RIS.tubeEnds δ (Kc * c) (x i) (v i))) ∧
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
  obtain ⟨β, τ, ξ, b, t, ν, e, Cnet, loss, capLoss, α, κ, θ, dH, p, d,
    hβ, hβ1, hβζ, hτ, hξ, hξε, hξ1, hb, hbξ, ht, htν, hmass,
    hν, hνε, hνζ, he, heε, heζ, hCnet, hloss, hlosse, hνloss, htloss,
    hcapLoss, hcaploss, hα, hκ, hθ, hθε, hdH, hdH1, hp, hd, HH⟩ :=
    gain_terminal_or_bounded_clipped_concentration hσ hσhalf hω hω1 hE hζ hζω
      (ε := ε / 4) (by positivity) (by linarith) angleMax hangleMax
  obtain ⟨θC, dC, hθC, hθCθ, hdC, hdC1, HC⟩ := cleared_ambient_stage_uniform
    hω hω1 hζ hζω (ε := θ / 2) (by positivity) hKc
  refine ⟨β, τ, ξ, b, t, ν, e, Cnet, loss, capLoss, α, κ, θC,
    min dH dC, p, d,
    hβ, hβ1, hβζ, hτ, hξ, by linarith, hξ1, hb, hbξ, ht, htν, hmass,
    hν, by linarith, hνζ, he, by linarith, heζ, hCnet,
    hloss, by linarith, hνloss, htloss, hcapLoss, hcaploss, hα, hκ, hθC,
    by linarith, lt_min hdH hdC, (min_le_left _ _).trans hdH1, hp, hd, ?_⟩
  intro δ h hδ hδ0 hh hhθ n x v Y hA ρ c hJ
  have hδH := hδ0.trans (min_le_left _ _)
  have hδC := hδ0.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδC.trans hdC1
  obtain ⟨Y₀, hY₀, hkeep₀, hA₀, hJ₀⟩ := HC δ h hδ hδC hhθ n x v Y hA ρ c 2 hJ
  have hkeep₀' : O (δ ^ (θ / 8)) * ∑ i, μ (Y i) ≤ ∑ i, μ (Y₀ i) := by
    simpa only [show (θ / 2) / 4 = θ / 8 by ring] using hkeep₀
  rcases HH δ (θ / 2) hδ hδH (by positivity) (by linarith) n x v Y₀ hA₀ ρ c hJ₀ with
    hgain | hterminal | hdata
  · exact Or.inl (hgain.trans (measure_mono (iUnion_mono (fun i => (hY₀ i).1))))
  · right; left
    exact stage_mono hδ hδ1 (by linarith : ε / 4 + θ / 8 ≤ ε)
      (stage_of_ambient_refinement hδ hδ1 (by positivity : 0 ≤ θ / 8)
        (fun i => (hY₀ i).1) hkeep₀' hterminal)
  obtain ⟨Y', hsub, hkeep, hA', hcap, D, F, HF⟩ := hdata
  right; right
  refine ⟨Y', fun i => (hsub i).trans (hY₀ i).1,
    fun i => ((hY₀ i).2).mono (hsub i) Subset.rfl, ?_, hA', hcap, D, F, HF⟩
  calc
    _ ≤ (O (δ ^ ((ε / 4) / 8)) * O (δ ^ (θ / 8))) * ∑ i, μ (Y i) := by
      apply mul_le_mul' _ le_rfl
      dsimp only [O]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
    _ = O (δ ^ ((ε / 4) / 8)) * (O (δ ^ (θ / 8)) * ∑ i, μ (Y i)) := mul_assoc _ _ _
    _ ≤ O (δ ^ ((ε / 4) / 8)) * ∑ i, μ (Y₀ i) := mul_le_mul' le_rfl hkeep₀'
    _ ≤ _ := hkeep

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
