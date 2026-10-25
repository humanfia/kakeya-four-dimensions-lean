-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_ad_dichotomy_from_separated.LocalizationBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.PowerBudget

namespace WangZahlLot.Obl.wz_ad_dichotomy_from_separated

structure LocalizationBudget (δ η ε θ : ℝ) : Prop where
  delta_pos : 0 < δ
  delta_le_one : δ ≤ 1
  delta_le_separation : δ ≤ δ ^ (10 * η)
  small_balls : 1000 * δ ^ (12 * η) ≤ δ ^ (10 * η)
  remove_degeneracies : (900 * (75 : ℝ) ^ 3) * δ ^ (2 * η) ≤ 1
  density_reserve : ((75 : ℝ) ^ 3 * (2 * (25 : ℝ) ^ 3)) * δ ^ (4 * η) ≤ 1
  zoom_reserve : 16 * δ ^ (4 * η) ≤ 1
  frostman_reserve : 450 * δ ^ (-84 * η) ≤ δ ^ (-θ)
  projection_reserve : 3 * δ ^ (-24 * η) ≤ δ ^ (-(θ * ε / 4))
  line_reserve : 9 * δ ^ (ε - 24 * η - 1) ≤ δ ^ (ε / 4 - 1)

/-- A single positive eta and a single positive cutoff meet all the numerical
reserves in the final localization and rescaling argument. -/
theorem exists_localization_budget {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ η ≤ 1 / 100 ∧ 84 * η < θ ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → LocalizationBudget δ η ε θ := by
  let η := min (1 / 100 : ℝ) (min (ε / 1000) (min (θ / 200) (θ * ε / 1000)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hbounds : η ≤ 1 / 100 ∧ η ≤ ε / 1000 ∧ η ≤ θ / 200 ∧ η ≤ θ * ε / 1000 := by
    have h : η ≤ min (1 / 100 : ℝ) (min (ε / 1000) (min (θ / 200) (θ * ε / 1000))) := le_rfl
    simpa only [le_min_iff] using h
  have h84 : 84 * η < θ := by nlinarith [hbounds.2.2.1]
  obtain ⟨d₁, hd₁, hd₁1, H₁⟩ :=
    exists_monomial_bound 1000 (a := 12 * η) (b := 10 * η) (by nlinarith)
  obtain ⟨d₂, hd₂, hd₂1, H₂⟩ :=
    exists_monomial_bound (900 * (75 : ℝ) ^ 3) (a := 2 * η) (b := 0) (by positivity)
  obtain ⟨d₃, hd₃, hd₃1, H₃⟩ :=
    exists_monomial_bound ((75 : ℝ) ^ 3 * (2 * (25 : ℝ) ^ 3))
      (a := 4 * η) (b := 0) (by positivity)
  obtain ⟨d₄, hd₄, hd₄1, H₄⟩ :=
    exists_monomial_bound 16 (a := 4 * η) (b := 0) (by positivity)
  obtain ⟨d₅, hd₅, hd₅1, H₅⟩ :=
    exists_monomial_bound 450 (a := -84 * η) (b := -θ) (by linarith)
  obtain ⟨d₆, hd₆, hd₆1, H₆⟩ :=
    exists_monomial_bound 3 (a := -24 * η) (b := -(θ * ε / 4))
      (by nlinarith [hbounds.2.2.2, mul_pos hθ hε])
  obtain ⟨d₇, hd₇, hd₇1, H₇⟩ :=
    exists_monomial_bound 9 (a := ε - 24 * η - 1) (b := ε / 4 - 1)
      (by nlinarith [hbounds.2.1])
  refine ⟨η, min d₁ (min d₂ (min d₃ (min d₄ (min d₅ (min d₆ d₇))))),
    hη, hbounds.1, h84, by positivity, ?_⟩
  intro δ hδ hsmall
  have hcuts : δ ≤ d₁ ∧ δ ≤ d₂ ∧ δ ≤ d₃ ∧ δ ≤ d₄ ∧ δ ≤ d₅ ∧ δ ≤ d₆ ∧ δ ≤ d₇ := by
    simpa only [le_min_iff] using hsmall
  have hδ1 : δ ≤ 1 := hcuts.1.trans hd₁1
  refine ⟨hδ, hδ1, ?_, H₁ δ hδ hcuts.1, ?_, ?_, ?_,
    H₅ δ hδ hcuts.2.2.2.2.1, H₆ δ hδ hcuts.2.2.2.2.2.1,
    H₇ δ hδ hcuts.2.2.2.2.2.2⟩
  · calc δ = δ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ δ ^ (10 * η) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith [hbounds.1])
  · simpa only [Real.rpow_zero] using H₂ δ hδ hcuts.2.1
  · simpa only [Real.rpow_zero] using H₃ δ hδ hcuts.2.2.1
  · simpa only [Real.rpow_zero] using H₄ δ hδ hcuts.2.2.2.1

end WangZahlLot.Obl.wz_ad_dichotomy_from_separated
