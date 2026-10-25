-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.ProjectionParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.PowerBudget

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

/-- Numeric reserves used in the localization and rescaling reduction. -/
structure ProjectionParameterBounds (ε ℓ α β η ζ θ t : ℝ) : Prop where
  epsilon_pos : 0 < ε
  epsilon_le_one : ε ≤ 1
  ell_pos : 0 < ℓ
  alpha_pos : 0 < α
  beta_pos : 0 < β
  beta_le_one : β ≤ 1
  beta_le_epsilon : β ≤ ε
  eta_pos : 0 < η
  zeta_pos : 0 < ζ
  zeta_le_one : ζ ≤ 1
  theta_pos : 0 < θ
  theta_le_eta : θ ≤ η
  theta_le_t : θ ≤ t
  t_pos : 0 < t
  t_le_one : t ≤ 1
  alignment_reserve : 4 * θ + ζ < η
  uniform_reserve : θ < η
  line_reserve : 4 * θ + ζ + t < ε
  frostman_reserve : 4 * θ + ζ < t * ℓ
  line_count_reserve : 2 * θ + 2 * β * ζ < t * ℓ * ζ
  small_normal_reserve : 4 * θ + 2 * ζ < β
  density_reserve : θ < t * α

theorem projection_parameter_bounds {ε ℓ α β η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hℓ : 0 < ℓ) (hα : 0 < α) (hη : 0 < η)
    (hβ : 0 < β) (hβε : β ≤ ε / 1000) (hβℓ : β ≤ ε * ℓ / 1000) :
    ProjectionParameterBounds ε ℓ α β η (min β η / 100)
      (min (min β η / 100) (min ((ε / 10) * α) ((ε / 10) * ℓ * (min β η / 100))) / 100)
      (ε / 10) := by
  let ζ := min β η / 100
  let θ := min ζ (min ((ε / 10) * α) ((ε / 10) * ℓ * ζ)) / 100
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hζβ : ζ ≤ β / 100 := by dsimp [ζ]; gcongr; exact min_le_left _ _
  have hζη : ζ ≤ η / 100 := by dsimp [ζ]; gcongr; exact min_le_right _ _
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθζ : θ ≤ ζ / 100 := by dsimp [θ]; gcongr; exact min_le_left _ _
  have hθα : θ ≤ ((ε / 10) * α) / 100 := by
    dsimp [θ]
    gcongr
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hθℓ : θ ≤ ((ε / 10) * ℓ * ζ) / 100 := by
    dsimp [θ]
    gcongr
    exact (min_le_right _ _).trans (min_le_right _ _)
  change ProjectionParameterBounds ε ℓ α β η ζ θ (ε / 10)
  refine ⟨hε, hε1, hℓ, hα, hβ, by linarith, by linarith, hη, hζ, by linarith,
    hθ, by linarith, by linarith, by positivity, by linarith, by linarith,
    by linarith, by linarith, by nlinarith, ?_, by linarith, by nlinarith⟩
  have hp : 0 < ε * ℓ * ζ := by positivity
  have hbz : β * ζ ≤ (ε * ℓ / 1000) * ζ := mul_le_mul_of_nonneg_right hβℓ hζ.le
  nlinarith

structure ProjectionScaleBudget (δ ε ℓ α β η ζ θ t dNC : ℝ) : Prop where
  scale_le_one : δ ≤ 1
  angular_small : 2 * δ ^ β ≤ 1
  alignment_frostman : 27648 * δ ^ (-(4 * θ + ζ)) ≤ δ ^ (-η)
  alignment_uniform : 1728 * δ ^ η ≤ δ ^ θ
  narrow_card : 4147200 * δ ^ (ε - 1) ≤ δ ^ (4 * θ + ζ + t - 1)
  frostman : 55296 * δ ^ (-(4 * θ + ζ)) ≤ δ ^ (-(t * ℓ))
  line_count : 13824 * δ ^ (-(2 * θ + 2 * β * ζ)) ≤ δ ^ (-(t * ℓ * ζ))
  small_normal : 276480 * δ ^ (β - 4 * θ - ζ) ≤ δ ^ ζ
  density : 1728 * δ ^ (t * α) ≤ δ ^ θ
  projection_power : 50 * δ ^ (t * ε / 2) ≤ 1
  input_scale : δ ^ t ≤ dNC

theorem exists_projection_scale_budget {ε ℓ α β η ζ θ t dNC : ℝ}
    (hp : ProjectionParameterBounds ε ℓ α β η ζ θ t) (hdNC : 0 < dNC) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ProjectionScaleBudget δ ε ℓ α β η ζ θ t dNC := by
  obtain ⟨d₁, hd₁, hd₁1, hb₁⟩ := exists_monomial_bound 2 (a := β) (b := 0) hp.beta_pos
  obtain ⟨d₂, hd₂, hd₂1, hb₂⟩ := exists_monomial_bound 27648
    (a := -(4 * θ + ζ)) (b := -η) (by linarith [hp.alignment_reserve])
  obtain ⟨d₃, hd₃, hd₃1, hb₃⟩ := exists_monomial_bound 1728 hp.uniform_reserve
  obtain ⟨d₄, hd₄, hd₄1, hb₄⟩ := exists_monomial_bound 4147200
    (a := ε - 1) (b := 4 * θ + ζ + t - 1) (by linarith [hp.line_reserve])
  obtain ⟨d₅, hd₅, hd₅1, hb₅⟩ := exists_monomial_bound 55296
    (a := -(4 * θ + ζ)) (b := -(t * ℓ)) (by linarith [hp.frostman_reserve])
  obtain ⟨d₆, hd₆, hd₆1, hb₆⟩ := exists_monomial_bound 13824
    (a := -(2 * θ + 2 * β * ζ)) (b := -(t * ℓ * ζ)) (by linarith [hp.line_count_reserve])
  obtain ⟨d₇, hd₇, hd₇1, hb₇⟩ := exists_monomial_bound 276480
    (a := β - 4 * θ - ζ) (b := ζ) (by linarith [hp.small_normal_reserve])
  obtain ⟨d₈, hd₈, hd₈1, hb₈⟩ := exists_monomial_bound 1728 hp.density_reserve
  obtain ⟨d₉, hd₉, hd₉1, hb₉⟩ := exists_monomial_bound 50
    (a := t * ε / 2) (b := 0) (by have := hp.t_pos; have := hp.epsilon_pos; positivity)
  obtain ⟨d₁₀, hd₁₀, hd₁₀1, hb₁₀⟩ := exists_monomial_bound dNC⁻¹ (a := t) (b := 0) hp.t_pos
  refine ⟨min d₁ (min d₂ (min d₃ (min d₄ (min d₅ (min d₆ (min d₇ (min d₈ (min d₉ d₁₀)))))))), by positivity, ?_⟩
  intro δ hδ hs
  simp only [le_min_iff] at hs
  refine ⟨hs.1.trans hd₁1, ?_, hb₂ δ hδ hs.2.1, hb₃ δ hδ hs.2.2.1,
    hb₄ δ hδ hs.2.2.2.1, hb₅ δ hδ hs.2.2.2.2.1, hb₆ δ hδ hs.2.2.2.2.2.1,
    hb₇ δ hδ hs.2.2.2.2.2.2.1, hb₈ δ hδ hs.2.2.2.2.2.2.2.1, ?_, ?_⟩
  · simpa only [Real.rpow_zero] using hb₁ δ hδ hs.1
  · simpa only [Real.rpow_zero] using hb₉ δ hδ hs.2.2.2.2.2.2.2.2.1
  · have hc := hb₁₀ δ hδ hs.2.2.2.2.2.2.2.2.2
    rw [Real.rpow_zero] at hc
    have hh := mul_le_mul_of_nonneg_left hc hdNC.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hdNC.ne', one_mul, mul_one] using hh

end WangZahlLot.Obl.wz_separated_projection_dichotomy
