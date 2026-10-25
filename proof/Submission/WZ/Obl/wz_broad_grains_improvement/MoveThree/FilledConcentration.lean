-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FilledConcentration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FilledConcentration.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AngularConcentration
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockFirstFilling

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric

noncomputable section

def firstFillingShrink : ℝ := 1 / 10000000000

theorem firstFillingShrink_pos : 0 < firstFillingShrink := by
  norm_num [firstFillingShrink]

/-- The full frozen-input reduction through the first filling. Its density
can meet any preassigned net-estimate threshold, with all exponents chosen
before the original scale or the family is known. -/
theorem gain_terminal_or_filled_concentration_with_cap {σ ω ζ ε ν capLoss : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hζ : 0 < ζ) (hε : 0 < ε) (hν : 0 < ν) (hcapLoss : 0 < capLoss)
    (hcapMax : capLoss ≤ ζ * σ / 16) :
    ∃ (β τ ξ b t α κ θ d₀ : ℝ) (p : ℕ),
      0 < β ∧ β ≤ 1 ∧ β ≤ ζ * σ / 128 ∧ 0 < τ ∧ 0 < ξ ∧ ξ ≤ ε / 4 ∧ ξ ≤ 1 ∧
      0 < b ∧ b ≤ ξ / 384 ∧ 0 < t ∧ t ≤ ν / 50 ∧ τ + 21 * ξ / 40 ≤ t ∧
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
          6144 * δ ^ ν ≤ δ ^ (ν / 2) * firstFillingShrink / 16000 ∧
          ∃ (D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y')
            (F : AngularBlockFamily D β τ),
            ∀ R : F.blocks, Nonempty (BlockFirstFilling (F.angular R)
              (δ ^ t / firstFillingMassConstant) (δ ^ (ν / 2))
              firstFillingShrink firstFillingShrink_pos) := by
  classical
  obtain ⟨β, hβ, hβ1, hβsmall, Hangle⟩ := angular_concentration_with_fixed_exponent_and_cap
    hσ hσhalf hω hE hζ
  let s := min (ζ / 64) (ν / 100)
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hsζ : s ≤ ζ / 64 := min_le_left _ _
  have hsν : s ≤ ν / 100 := min_le_right _ _
  let t := 2 * s * β
  have ht : 0 < t := by dsimp [t]; positivity
  have htbound : t ≤ 2 * s := by
    dsimp [t]
    exact mul_le_of_le_one_right (by positivity) hβ1
  have htν : t ≤ ν / 50 := by linarith
  obtain ⟨τ, ξ, b, α, κ, θ, d₁, p, hτ, hτβ, _, hξ, hξε, hξβ, hξ1,
    hb, hbξ, hα, hκ, hθ, hθε, hd₁, hd₁small, hp, Hangle⟩ := Hangle ε s capLoss hε hs hcapLoss hcapMax
  have hmass : τ + 21 * ξ / 40 ≤ t := by dsimp [t]; linarith
  have hts : t < (4 * s) * β := by dsimp [t]; nlinarith only [mul_pos hs hβ]
  obtain ⟨d₂, hd₂, _, Hfill⟩ := block_first_filling_uniform hζ hβ
    (by positivity : 0 < 4 * s) (by linarith : 4 * s < ζ / 8) hts
    (by linarith : 4 * s + 3 * t < ν / 2) (by linarith : ν / 2 < ν)
    firstFillingShrink_pos (by norm_num [firstFillingShrink])
  refine ⟨β, τ, ξ, b, t, α, κ, θ, min d₁ d₂, p, hβ, hβ1, hβsmall, hτ, hξ, hξε, hξ1,
    hb, hbξ, ht, htν, hmass, hα, hκ, hθ, hθε,
    lt_min hd₁ hd₂, (min_le_left _ _).trans hd₁small, hp, ?_⟩
  intro δ h hδ hδd hh hhθ n x v Y hA ρ c hJ
  have hδd₁ := hδd.trans (min_le_left _ _)
  have hδd₂ := hδd.trans (min_le_right _ _)
  rcases Hangle δ h hδ hδd₁ hh hhθ n x v Y hA ρ c hJ with hgain | hterminal | hdata
  · exact Or.inl hgain
  · exact Or.inr (Or.inl hterminal)
  obtain ⟨Y', hsub, hret, hA', hcap, D, ⟨F⟩⟩ := hdata
  have hfill (R : F.blocks) := Hfill δ hδ hδd₂ ω ξ b ρ c τ p n x v Y' D R.val
    (by
      by_contra hnone
      have hempty : R.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
      have hcard0 : R.val.card = 0 := by rw [hempty]; rfl
      have hsat := (F.frame R).saturated
      rw [hcard0, Nat.cast_zero, mul_zero, zero_mul] at hsat
      have hcoef := D.large
      have hshortpos := (F.frame R).short_pos
      have hmid := (F.frame R).short_pos.trans_le (F.frame R).ordered
      have hpos : 0 < grainCoefficient D.a ρ c D.z D.e D.Q *
          (4 * (F.frame R).short * (F.frame R).middle) :=
        mul_pos ((Real.rpow_pos_of_pos hδ _).trans hcoef) (by positivity)
      exact (not_lt_of_ge hsat) hpos)
    (F.frame R) (F.angular R) hmass
  have hFne : F.blocks.Nonempty := by
    have hQ : (0 : ℝ) < D.Q.card := Nat.cast_pos.mpr (Finset.card_pos.mpr D.selected_nonempty)
    by_contra hh
    have he := Finset.not_nonempty_iff_eq_empty.mp hh
    have hc := F.card
    simp only [he, Finset.biUnion_empty, Finset.card_empty, Nat.cast_zero, mul_zero] at hc
    exact (not_lt_of_ge hc) hQ
  obtain ⟨R₀, hR₀⟩ := hFne
  right; right
  exact ⟨Y', hsub, hret, hA', hcap, (hfill ⟨R₀, hR₀⟩).2, D, F, fun R => (hfill R).1⟩


theorem gain_terminal_or_filled_concentration {σ ω ζ ε ν : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hζ : 0 < ζ) (hε : 0 < ε) (hν : 0 < ν) :
    ∃ (β τ ξ b t α κ θ d₀ : ℝ) (p : ℕ),
      0 < β ∧ β ≤ 1 ∧ β ≤ ζ * σ / 128 ∧ 0 < τ ∧ 0 < ξ ∧ ξ ≤ ε / 4 ∧ ξ ≤ 1 ∧
      0 < b ∧ b ≤ ξ / 384 ∧ 0 < t ∧ t ≤ ν / 50 ∧ τ + 21 * ξ / 40 ≤ t ∧
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
          6144 * δ ^ ν ≤ δ ^ (ν / 2) * firstFillingShrink / 16000 ∧
          ∃ (D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y')
            (F : AngularBlockFamily D β τ),
            ∀ R : F.blocks, Nonempty (BlockFirstFilling (F.angular R)
              (δ ^ t / firstFillingMassConstant) (δ ^ (ν / 2))
              firstFillingShrink firstFillingShrink_pos) := by
  exact gain_terminal_or_filled_concentration_with_cap hσ hσhalf hω hE hζ hε hν
    (by positivity : 0 < ζ * σ / 16) le_rfl

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
