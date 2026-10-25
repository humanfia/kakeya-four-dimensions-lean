-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.AngularConcentration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/AngularConcentration.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AngularBlockFamily
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FlatConcentration

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (body_estimate_of_tube_estimate)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (tubeEstimate_of_E)
open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)

noncomputable section

/-- The remaining case of Move 3 has actual angular packet selections on
disjoint saturated blocks. The angular mass loss is arbitrarily small relative
to its exponent, as needed by the subsequent flat filling. -/
theorem angular_concentration_with_fixed_exponent_and_cap {σ ω ζ : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hζ : 0 < ζ) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ β ≤ ζ * σ / 128 ∧ ∀ ε s capLoss : ℝ, 0 < ε → 0 < s →
      0 < capLoss → capLoss ≤ ζ * σ / 16 →
    ∃ (τ ξ b α κ θ d₀ : ℝ) (p : ℕ),
      0 < τ ∧ τ ≤ s * β ∧ τ ≤ s ∧
      0 < ξ ∧ ξ ≤ ε / 4 ∧ ξ ≤ s * β ∧ ξ ≤ 1 ∧ 0 < b ∧ b ≤ ξ / 384 ∧
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
            Nonempty (AngularBlockFamily D β τ) := by
  classical
  have hbody := body_estimate_of_tube_estimate hσ.le hσhalf hω (tubeEstimate_of_E hE)
  obtain ⟨β, hβ, hβ1, hβsmall, Hangle⟩ := capped_block_angular_packets_with_relative_budget
    hσ hω hζ hbody (show 0 < ζ * σ / 128 by positivity)
  refine ⟨β, hβ, hβ1, hβsmall, ?_⟩
  intro ε s capLoss hε hs hcapLoss hcapMax
  obtain ⟨τ, η, hτ, hτβ, hτs, hη, _, Hangle⟩ := Hangle s hs
  let ε' := min ε (min (4 * η) (4 * s * β))
  have hε' : 0 < ε' := lt_min hε (by positivity)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'η : ε' ≤ 4 * η := (min_le_right _ _).trans (min_le_left _ _)
  have hε'sβ : ε' ≤ 4 * s * β := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ξ, b, α, κ, θ, d₁, p, hξ, hξε', hξ1, hb, hbξ, hα, hκ, hθ,
    hθε', hd₁, hd₁small, hp, Hflat⟩ :=
    gain_terminal_or_flat_concentration_with_cap hσ hσhalf hω hE hζ hε' hcapLoss hcapMax
  have hξη : ξ ≤ η := by linarith
  obtain ⟨d₂, hd₂, _, Hangle⟩ := Hangle ξ hξ hξη p
  obtain ⟨d₃, hd₃, Hshort⟩ := exists_rpow_cutoff (by positivity : 0 < ζ / 4)
    (by norm_num : (0 : ℝ) < 1 / 32)
  refine ⟨τ, ξ, b, α, κ, θ, min d₁ (min d₂ d₃), p, hτ, hτβ,
    hτs, hξ, by linarith, by linarith, hξ1, hb, hbξ, hα, hκ, hθ, hθε'.trans hε'ε,
    lt_min hd₁ (lt_min hd₂ hd₃), (min_le_left _ _).trans hd₁small, hp, ?_⟩
  intro δ h hδ hδd hh hhθ n x v Y hA ρ c hJ
  have hδd₁ := hδd.trans (min_le_left _ _)
  have hδd₂ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₃ := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := hδd₁.trans (hd₁small.trans (by norm_num))
  rcases Hflat δ h hδ hδd₁ hh hhθ n x v Y hA ρ c hJ with hgain | hterminal | hdata
  · exact Or.inl hgain
  · exact Or.inr (Or.inl (stage_mono hδ hδ1 hε'ε hterminal))
  obtain ⟨Y', hsub, hret, hA', hcap, D, hflat⟩ := hdata
  obtain ⟨F, hF, hdisj, hcard⟩ := D.normalized_saturated_blocks hδ
  let G (R : F) : D.NormalizedBlock R.val := Classical.choice (hF R.val R.property).2.2
  have hang (R : F) : Nonempty (BlockAngularData D R.val (G R) β τ) := by
    apply Hangle δ hδ hδd₂ b ρ c n x v Y' hA' (ball_density_cap_mono hδ hδ1 hcapMax hcap) D R.val
      (hF R.val R.property).1 (G R)
    have hmid : 0 < (G R).middle := (G R).short_pos.trans_le (G R).ordered
    have hh := (div_lt_iff₀ hmid).mp (hflat R.val (hF R.val R.property).1 (G R))
    have hm := mul_le_mul_of_nonneg_left (G R).middle_le (Real.rpow_nonneg hδ.le (ζ / 4))
    have hc := Hshort δ hδ hδd₃
    nlinarith only [hh, hm, hc]
  right; right
  refine ⟨Y', hsub, ?_, hA', hcap, D, ⟨{
    blocks := F, subset := fun R hR => (hF R hR).2.1,
    disjoint := hdisj, card := hcard, frame := G,
    angular := fun R => Classical.choice (hang R) }⟩⟩
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))) le_rfl).trans hret


theorem angular_concentration_with_fixed_exponent {σ ω ζ : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hζ : 0 < ζ) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ β ≤ ζ * σ / 128 ∧ ∀ ε s : ℝ, 0 < ε → 0 < s →
    ∃ (τ ξ b α κ θ d₀ : ℝ) (p : ℕ),
      0 < τ ∧ τ ≤ s * β ∧ τ ≤ s ∧
      0 < ξ ∧ ξ ≤ ε / 4 ∧ ξ ≤ s * β ∧ ξ ≤ 1 ∧ 0 < b ∧ b ≤ ξ / 384 ∧
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
            Nonempty (AngularBlockFamily D β τ) := by
  obtain ⟨β, hβ, hβ1, hβsmall, H⟩ :=
    angular_concentration_with_fixed_exponent_and_cap hσ hσhalf hω hE hζ
  exact ⟨β, hβ, hβ1, hβsmall, fun ε s hε hs =>
    H ε s (ζ * σ / 16) hε hs (by positivity) le_rfl⟩

/-- The convenient form where the final error and relative angular loss are
specified together. The stronger theorem above fixes beta before both. -/
theorem gain_terminal_or_angular_concentration {σ ω ζ ε s : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hζ : 0 < ζ) (hε : 0 < ε) (hs : 0 < s) :
    ∃ (β τ ξ b α κ θ d₀ : ℝ) (p : ℕ),
      0 < β ∧ β ≤ 1 ∧ 0 < τ ∧ τ ≤ s * β ∧ τ ≤ s ∧
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
            Nonempty (AngularBlockFamily D β τ) := by
  obtain ⟨β, hβ, hβ1, _, H⟩ := angular_concentration_with_fixed_exponent hσ hσhalf hω hE hζ
  obtain ⟨τ, ξ, b, α, κ, θ, d₀, p, hτ, hτβ, hτs, hξ, hξε, _, hξ1,
    hb, hbξ, hα, hκ, hθ, hθε, hd₀, hd₀max, hp, H⟩ := H ε s hε hs
  exact ⟨β, τ, ξ, b, α, κ, θ, d₀, p, hβ, hβ1, hτ, hτβ, hτs, hξ, hξε, hξ1,
    hb, hbξ, hα, hκ, hθ, hθε, hd₀, hd₀max, hp, H⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
