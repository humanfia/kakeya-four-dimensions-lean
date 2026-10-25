-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FlatConcentration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FlatConcentration.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CappedConcentration
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CappedBlocksFlat
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenBridge

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (body_estimate_of_tube_estimate)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (tubeEstimate_of_E)

noncomputable section

/-- A smaller cap exponent gives a stronger all-radius density bound. -/
theorem ball_density_cap_mono {δ s t t' : ℝ} {Γ : Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (htt' : t ≤ t')
    (hcap : ∀ z ∈ Γ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ (Γ ∩ ball z r) ≤ O (δ ^ (-t) * (δ / r) ^ s * r ^ 3)) :
    ∀ z ∈ Γ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ (Γ ∩ ball z r) ≤ O (δ ^ (-t') * (δ / r) ^ s * r ^ 3) := by
  intro z hz r hr hr1
  apply (hcap z hz r hr hr1).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg htt'))
      (Real.rpow_nonneg (div_nonneg hδ.le hr.le) _)) (pow_nonneg hr.le _)

/-- The uniform reduction to flat saturated blocks, including retention of
the ambient family and the cap that rules out every nonflat block. -/
theorem gain_terminal_or_flat_concentration_with_cap {σ ω ζ ε capLoss : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hζ : 0 < ζ) (hε : 0 < ε) (hcapLoss : 0 < capLoss)
    (hcapMax : capLoss ≤ ζ * σ / 16) :
    ∃ (ξ b α κ θ d₀ : ℝ) (p : ℕ),
      0 < ξ ∧ ξ ≤ ε / 4 ∧ ξ ≤ 1 ∧ 0 < b ∧ b ≤ ξ / 384 ∧
      0 < α ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ 0 < p ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
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
          ∃ D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y',
            ∀ (R : Finset (Fin D.L)), R.Nonempty → ∀ G : D.NormalizedBlock R,
              G.short / G.middle < δ ^ (ζ / 4) := by
  have hbody := body_estimate_of_tube_estimate hσ.le hσhalf hω (tubeEstimate_of_E hE)
  obtain ⟨η, hη, hηsize, Hflat⟩ := capped_normalized_blocks_flat hσ hω hζ hbody
  let ξ := min η (ε / 4)
  have hξ : 0 < ξ := lt_min hη (by positivity)
  have hξη : ξ ≤ η := min_le_left _ _
  have hξε : ξ ≤ ε / 4 := min_le_right _ _
  have hξ1 : ξ ≤ 1 := hξη.trans (hηsize.trans (min_le_left _ _))
  obtain ⟨b, κ, θ, d₁, p, hb, hbξ, hκ, hθ, hθξ, hd₁, hd₁small, hp, Hreduce⟩ :=
    gain_terminal_or_capped_concentration hσ.le hσhalf hω hE hζ hξ hξ1
      hcapLoss
  obtain ⟨d₂, hd₂, hd₂small, Hflat⟩ := Hflat ξ hξ hξη p
  refine ⟨ξ, b, min (capLoss / 4) (b * ω / 2), κ, θ, min d₁ d₂, p,
    hξ, hξε, hξ1, hb, hbξ, lt_min (by positivity) (by positivity), hκ, hθ,
    by linarith, lt_min hd₁ hd₂, (min_le_left _ _).trans hd₁small, hp, ?_⟩
  intro δ h hδ hδd hh hhθ n x v Y hA ρ c hJ
  have hδd₁ := hδd.trans (min_le_left _ _)
  have hδd₂ := hδd.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδd₁.trans (hd₁small.trans (by norm_num))
  rcases Hreduce δ h hδ hδd₁ hh hhθ n x v Y hA ρ c hJ with hgain | hrest
  · exact Or.inl hgain
  rcases hrest with hterminal | hdata
  · exact Or.inr (Or.inl (stage_mono hδ hδ1 (by linarith) hterminal))
  obtain ⟨Y', hsub, hret, hA', hcap, ⟨D⟩⟩ := hdata
  right; right
  refine ⟨Y', hsub, ?_, hA', hcap, D, ?_⟩
  · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))) le_rfl).trans hret
  · exact Hflat δ hδ hδd₂ b ρ c n x v Y' hA' (ball_density_cap_mono hδ hδ1 hcapMax hcap) D


theorem gain_terminal_or_flat_concentration {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ (ξ b α κ θ d₀ : ℝ) (p : ℕ),
      0 < ξ ∧ ξ ≤ ε / 4 ∧ ξ ≤ 1 ∧ 0 < b ∧ b ≤ ξ / 384 ∧
      0 < α ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ 0 < p ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
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
              O (δ ^ (-(ζ * σ / 16)) * (δ / r) ^ (ω + σ) * r ^ 3)) ∧
          ∃ D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y',
            ∀ (R : Finset (Fin D.L)), R.Nonempty → ∀ G : D.NormalizedBlock R,
              G.short / G.middle < δ ^ (ζ / 4) := by
  exact gain_terminal_or_flat_concentration_with_cap hσ hσhalf hω hE hζ hε
    (by positivity : 0 < ζ * σ / 16) le_rfl

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
