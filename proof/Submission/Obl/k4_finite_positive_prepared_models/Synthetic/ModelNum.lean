import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.ModelLabels

/-!
# Exponent bookkeeping for the true labels of the synthetic model

At a scale `s ∈ [1/n, 1]` with level `d = lev s`, the rounded exponents of the time blocks,
transverse cells and hidden cells differ from `κ₁ s Λ`, `(κ₁ + ℓ) s Λ` and `s Λ` by at most the
loss exponent `σ = Λ/(n+1)`. Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

noncomputable section

namespace Par

variable (p : Par)

theorem rpow_two_nat (n : ℕ) : (2 : ℝ) ^ n = (2 : ℝ) ^ (n : ℝ) := (Real.rpow_natCast 2 n).symm

theorem one_div_two_pow (n : ℕ) : 1 / (2 : ℝ) ^ n = (2 : ℝ) ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

theorem two_zpow_neg (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) = (2 : ℝ) ^ (-(n : ℝ)) := by
  rw [zpow_neg, zpow_natCast, Real.rpow_neg (by norm_num), Real.rpow_natCast]

/-- The exponent facts at the level of a scale. -/
structure LevFacts (s : ℝ) : Prop where
  hs : p.sc (p.lev s) ≤ s
  hs' : s ≤ p.sc (p.lev s) + 1 / (p.n * p.m₀)
  hs1 : s ≤ 1
  hT1 : (p.T (p.lev s) : ℝ) ≤ p.κ₁ * p.sc (p.lev s) * p.Λ
  hT2 : p.κ₁ * p.sc (p.lev s) * p.Λ < p.T (p.lev s) + 1
  hF1 : (⌊p.ℓ * p.sc (p.lev s) * p.Λ⌋₊ : ℝ) ≤ p.ℓ * p.sc (p.lev s) * p.Λ
  hF2 : p.ℓ * p.sc (p.lev s) * p.Λ < ⌊p.ℓ * p.sc (p.lev s) * p.Λ⌋₊ + 1
  hG1 : (p.Gh (p.lev s) : ℝ) ≤ p.sc (p.lev s) * p.Λ / p.e
  hG2 : p.sc (p.lev s) * p.Λ / p.e < p.Gh (p.lev s) + 1

theorem levFacts {s : ℝ} (h1 : 1 / (p.n : ℝ) ≤ s) (h2 : s ≤ 1) : p.LevFacts s := by
  obtain ⟨hs, hs'⟩ := p.lev_bounds h1 h2
  have hsc := p.sc_pos (p.lev s)
  have hΛ : (0 : ℝ) ≤ p.Λ := by positivity
  have he : (0 : ℝ) < p.e := by unfold e; positivity
  have hκ := p.hκ
  have hℓ := p.hℓ
  exact ⟨hs, hs', h2, Nat.floor_le (by positivity), Nat.lt_floor_add_one _,
    Nat.floor_le (by positivity), Nat.lt_floor_add_one _, Nat.floor_le (by positivity),
    Nat.lt_floor_add_one _⟩

theorem e_le_σ : (p.e : ℝ) + 1 ≤ p.σ / 4 := by
  have := p.σ_ge
  have : (0 : ℝ) ≤ p.B := by positivity
  unfold e; push_cast; linarith

theorem stepΛ : p.Λ * (1 / (p.n * p.m₀)) ≤ p.σ / (4 * (p.ℓ + 2)) := by
  have := p.step_le_σ
  rw [mul_one_div]; exact this

/-- Time blocks. -/
theorem time_bounds {s : ℝ} (hf : p.LevFacts s) :
    p.sN ^ (p.κ₁ * s) / p.sK ≤ (2 : ℝ) ^ p.T (p.lev s) ∧
      (2 : ℝ) ^ p.T (p.lev s) ≤ p.sK * p.sN ^ (p.κ₁ * s) := by
  have hκ := p.hκ
  have hκ1 := p.hκ'
  have hst := p.stepΛ
  have hσ := p.e_le_σ
  have hℓ := p.hℓ
  have hΛ : (0 : ℝ) ≤ p.Λ := by positivity
  have hstep : p.κ₁ * p.Λ * (1 / (p.n * p.m₀)) ≤ p.σ / 8 := by
    have h1 : p.σ / (4 * (p.ℓ + 2)) ≤ p.σ / 8 := by
      apply div_le_div_of_nonneg_left (by linarith [p.σ_pos]) (by norm_num) (by linarith)
    have h2 : p.κ₁ * p.Λ * (1 / (p.n * p.m₀)) ≤ p.Λ * (1 / (p.n * p.m₀)) := by
      have h0 : 0 ≤ (p.Λ : ℝ) * (1 / (p.n * p.m₀)) := by have := p.nm₀_pos; positivity
      calc p.κ₁ * p.Λ * (1 / (p.n * p.m₀)) = p.κ₁ * (p.Λ * (1 / (p.n * p.m₀))) := by ring
        _ ≤ 1 * (p.Λ * (1 / (p.n * p.m₀))) := mul_le_mul_of_nonneg_right hκ1 h0
        _ = p.Λ * (1 / (p.n * p.m₀)) := one_mul _
    linarith
  rw [sN_rpow, sK_eq, rpow_two_nat]
  constructor
  · rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num)]
    apply two_rpow_le
    have h1 := hf.hT2
    have hs' := hf.hs'
    have h3 : p.κ₁ * s * p.Λ ≤ p.κ₁ * (p.sc (p.lev s) + 1 / (p.n * p.m₀)) * p.Λ := by
      apply mul_le_mul_of_nonneg_right _ hΛ
      exact mul_le_mul_of_nonneg_left hs' hκ.le
    have h4 : p.κ₁ * (p.sc (p.lev s) + 1 / (p.n * p.m₀)) * p.Λ =
        p.κ₁ * p.sc (p.lev s) * p.Λ + p.κ₁ * p.Λ * (1 / (p.n * p.m₀)) := by ring
    have h5 : (1 : ℝ) ≤ 7 * p.σ / 8 := by
      have := p.σ_ge
      have : (0 : ℝ) ≤ p.B := by positivity
      have := p.n_pos
      linarith
    nlinarith
  · rw [← Real.rpow_add (by norm_num)]
    apply two_rpow_le
    have := hf.hT1
    have hs := hf.hs
    have : p.κ₁ * p.sc (p.lev s) * p.Λ ≤ p.κ₁ * s * p.Λ := by
      apply mul_le_mul_of_nonneg_right _ hΛ
      exact mul_le_mul_of_nonneg_left hs hκ.le
    nlinarith [p.σ_pos]

theorem e_cast : (p.e : ℝ) = p.n + 1 := by unfold e; push_cast; ring

theorem σ_eq : p.σ = p.Λ / p.e := by rw [e_cast]; rfl

theorem x_step : (1 + p.ℓ) * (p.Λ * (1 / (p.n * p.m₀))) ≤ p.σ / 4 := by
  have h := p.stepΛ
  have hℓ := p.hℓ
  have hσ := p.σ_pos
  calc (1 + p.ℓ) * (p.Λ * (1 / (p.n * p.m₀))) ≤ (1 + p.ℓ) * (p.σ / (4 * (p.ℓ + 2))) := by
        gcongr
    _ ≤ p.σ / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

/-- Label floors, in exponents. -/
theorem floor_exps {s : ℝ} (hf : p.LevFacts s) :
    (p.e₁ * p.Gh (p.lev s) : ℝ) + ⌊p.ℓ * p.sc (p.lev s) * p.Λ⌋₊ ≤
        p.Λ * s * p.d₁ + p.Λ * p.ℓ * s + p.σ ∧
      p.Λ * s * p.d₁ + p.Λ * p.ℓ * s ≤
        (p.e₁ * p.Gh (p.lev s) : ℝ) + ⌊p.ℓ * p.sc (p.lev s) * p.Λ⌋₊ + p.σ := by
  have he : (0 : ℝ) < p.e := by rw [e_cast]; linarith [p.n_pos]
  have he₁a : p.d₁ * p.e ≤ p.e₁ := Nat.le_ceil _
  have he₁b : (p.e₁ : ℝ) < p.d₁ * p.e + 1 := Nat.ceil_lt_add_one (by
    have := p.hd₁; positivity)
  have hd₁ := p.hd₁
  have hd₁' := p.hd₁'
  have hℓ := p.hℓ
  have hΛ : (0 : ℝ) ≤ p.Λ := by positivity
  have hGh0 : (0 : ℝ) ≤ (p.Gh (p.lev s) : ℝ) := by positivity
  have hsc0 : 0 < p.sc (p.lev s) := p.sc_pos _
  have hs := hf.hs
  have hs' := hf.hs'
  have hsc1 : p.sc (p.lev s) ≤ 1 := le_trans hs hf.hs1
  have hx0 : (0 : ℝ) ≤ 1 / (p.n * p.m₀) := by have := p.nm₀_pos; positivity
  have hΛx : 0 ≤ (p.Λ : ℝ) * (1 / (p.n * p.m₀)) := mul_nonneg hΛ hx0
  have hG1 : (p.Gh (p.lev s) : ℝ) * p.e ≤ p.sc (p.lev s) * p.Λ := by
    have := hf.hG1; rw [le_div_iff₀ he] at this; linarith
  have hG2 : p.sc (p.lev s) * p.Λ < ((p.Gh (p.lev s) : ℝ) + 1) * p.e := by
    have := hf.hG2; rw [div_lt_iff₀ he] at this; linarith
  have hF1 := hf.hF1
  have hF2 := hf.hF2
  have hσe : p.σ * p.e = p.Λ := by rw [σ_eq]; field_simp
  have hxs := p.x_step
  have heσ := p.e_le_σ
  have hℓx : 0 ≤ p.ℓ * ((p.Λ : ℝ) * (1 / (p.n * p.m₀))) := mul_nonneg hℓ.le hΛx
  have hd₁Λ : 0 ≤ p.d₁ * (p.Λ : ℝ) := mul_nonneg hd₁ hΛ
  have hℓΛ : 0 ≤ p.ℓ * (p.Λ : ℝ) := mul_nonneg hℓ.le hΛ
  constructor
  · have k1 : (p.e₁ : ℝ) * p.Gh (p.lev s) ≤ (p.d₁ * p.e + 1) * p.Gh (p.lev s) :=
      mul_le_mul_of_nonneg_right he₁b.le hGh0
    have k2 : p.d₁ * (p.Gh (p.lev s) * p.e) ≤ p.d₁ * (p.sc (p.lev s) * p.Λ) :=
      mul_le_mul_of_nonneg_left hG1 hd₁
    have k3 : (p.Gh (p.lev s) : ℝ) ≤ p.σ := by
      have : (p.Gh (p.lev s) : ℝ) * p.e ≤ p.σ * p.e := by
        rw [hσe]; nlinarith
      exact le_of_mul_le_mul_right this he
    have k4 : p.d₁ * p.Λ * p.sc (p.lev s) ≤ p.d₁ * p.Λ * s := mul_le_mul_of_nonneg_left hs hd₁Λ
    have k5 : p.ℓ * p.Λ * p.sc (p.lev s) ≤ p.ℓ * p.Λ * s := mul_le_mul_of_nonneg_left hs hℓΛ
    nlinarith
  · have k1 : p.d₁ * p.e * p.Gh (p.lev s) ≤ p.e₁ * p.Gh (p.lev s) :=
      mul_le_mul_of_nonneg_right he₁a hGh0
    have k2 : p.d₁ * (p.sc (p.lev s) * p.Λ) ≤ p.d₁ * (((p.Gh (p.lev s) : ℝ) + 1) * p.e) :=
      mul_le_mul_of_nonneg_left hG2.le hd₁
    have k3 : p.d₁ * p.Λ * s ≤ p.d₁ * p.Λ * (p.sc (p.lev s) + 1 / (p.n * p.m₀)) :=
      mul_le_mul_of_nonneg_left hs' hd₁Λ
    have k4 : p.ℓ * p.Λ * s ≤ p.ℓ * p.Λ * (p.sc (p.lev s) + 1 / (p.n * p.m₀)) :=
      mul_le_mul_of_nonneg_left hs' hℓΛ
    have k5 : p.d₁ * p.e ≤ p.e := by nlinarith
    have k6 : p.d₁ * (p.Λ * (1 / (p.n * p.m₀))) ≤ p.Λ * (1 / (p.n * p.m₀)) := by nlinarith
    nlinarith

/-- Transverse cells, in exponents. -/
theorem x2_exp {s : ℝ} (hf : p.LevFacts s) :
    p.Λ * p.ℓ * s ≤ ⌊p.ℓ * p.sc (p.lev s) * p.Λ⌋₊ + p.σ := by
  have hF2 := hf.hF2
  have hs' := hf.hs'
  have hℓ := p.hℓ
  have hΛ : (0 : ℝ) ≤ p.Λ := by positivity
  have hxs := p.x_step
  have heσ := p.e_le_σ
  have he0 : (0 : ℝ) ≤ p.e := by positivity
  have hx0 : (0 : ℝ) ≤ 1 / (p.n * p.m₀) := by have := p.nm₀_pos; positivity
  have hΛx : 0 ≤ (p.Λ : ℝ) * (1 / (p.n * p.m₀)) := mul_nonneg hΛ hx0
  have hℓΛ : 0 ≤ p.ℓ * (p.Λ : ℝ) := mul_nonneg hℓ.le hΛ
  have k : p.ℓ * p.Λ * s ≤ p.ℓ * p.Λ * (p.sc (p.lev s) + 1 / (p.n * p.m₀)) :=
    mul_le_mul_of_nonneg_left hs' hℓΛ
  nlinarith

/-- Hidden cells, in exponents. -/
theorem hid_exp {s : ℝ} (hf : p.LevFacts s) :
    p.Λ * s ≤ p.e * p.Gh (p.lev s) + p.σ := by
  have he : (0 : ℝ) < p.e := by rw [e_cast]; linarith [p.n_pos]
  have hG2 : p.sc (p.lev s) * p.Λ < ((p.Gh (p.lev s) : ℝ) + 1) * p.e := by
    have := hf.hG2; rw [div_lt_iff₀ he] at this; linarith
  have hs' := hf.hs'
  have hΛ : (0 : ℝ) ≤ p.Λ := by positivity
  have hxs := p.x_step
  have heσ := p.e_le_σ
  have hℓ := p.hℓ
  have hx0 : (0 : ℝ) ≤ 1 / (p.n * p.m₀) := by have := p.nm₀_pos; positivity
  have hΛx : 0 ≤ (p.Λ : ℝ) * (1 / (p.n * p.m₀)) := mul_nonneg hΛ hx0
  have hℓx : 0 ≤ p.ℓ * ((p.Λ : ℝ) * (1 / (p.n * p.m₀))) := mul_nonneg hℓ.le hΛx
  have k : p.Λ * s ≤ p.Λ * (p.sc (p.lev s) + 1 / (p.n * p.m₀)) :=
    mul_le_mul_of_nonneg_left hs' hΛ
  nlinarith

end Par

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
