import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Contract

/-!
# Eventual inequalities for subpower sequences
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Filter

/-- Fixed polynomials of a subpower sequence are eventually below every fixed
positive power of `N`. -/
theorem eventually_mul_pow_le {N H : ℕ → ℝ} (hN2 : ∀ k, 2 ≤ N k)
    (hN : Tendsto N atTop atTop)
    (hH : (∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    (c : ℝ) (a : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ k in atTop, c * H k ^ a ≤ N k ^ γ := by
  have hε : 0 < γ / (2 * ((a : ℝ) + 1)) := by positivity
  have hc : ∀ᶠ k in atTop, c ≤ N k ^ (γ / 2) :=
    ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < γ / 2)).comp hN).eventually_ge_atTop c
  filter_upwards [hH.2 _ hε, hc] with k hk hck
  have hN1 : 1 ≤ N k := by linarith [hN2 k]
  have hN0 : 0 ≤ N k := by linarith
  have hHa : H k ^ a ≤ N k ^ (γ / 2) := by
    calc
      H k ^ a ≤ (N k ^ (γ / (2 * ((a : ℝ) + 1)))) ^ a :=
        pow_le_pow_left₀ (by linarith [hH.1 k]) hk a
      _ = N k ^ (γ / (2 * ((a : ℝ) + 1)) * a) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
      _ ≤ N k ^ (γ / 2) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1
        have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
        have hid : γ / (2 * ((a : ℝ) + 1)) * a = (γ / 2) * (a / (a + 1)) := by
          field_simp
        rw [hid]
        apply mul_le_of_le_one_right (by positivity)
        rw [div_le_one (by positivity)]
        linarith
  by_cases hc0 : c ≤ 0
  · have : c * H k ^ a ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc0 (pow_nonneg (by linarith [hH.1 k]) a)
    exact this.trans (Real.rpow_nonneg hN0 _)
  · push Not at hc0
    calc
      c * H k ^ a ≤ N k ^ (γ / 2) * N k ^ (γ / 2) :=
        mul_le_mul hck hHa (pow_nonneg (by linarith [hH.1 k]) a) (Real.rpow_nonneg hN0 _)
      _ = N k ^ γ := by
        rw [← Real.rpow_add (by linarith)]
        ring_nf

/-- Products of subpower sequences with fixed constants are subpower. -/
theorem subpower_const_mul_pow {N H : ℕ → ℝ} (hN2 : ∀ k, 2 ≤ N k)
    (hN : Tendsto N atTop atTop)
    (hH : (∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    (C : ℝ) (hC : 1 ≤ C) (m : ℕ) :
    (∀ k, 1 ≤ C * H k ^ m) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, C * H k ^ m ≤ N k ^ ε := by
  refine ⟨fun k => ?_, fun ε hε => eventually_mul_pow_le hN2 hN hH C m hε⟩
  have : 1 ≤ H k ^ m := one_le_pow₀ (hH.1 k)
  nlinarith

/-- The field certificate at a larger compact radius gives it at a smaller one. -/
theorem FieldAt.mono {Nk Hk d κ S Z B R R' : ℝ} {D : ℕ} {νg : MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))}
    {πg : MeasureTheory.Measure ℝ} {ρg : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {Ag : Set (ℕ × (Fin 5 → ℝ))} {Tk : ℕ} {jj : Fin (2 ^ Tk)}
    {μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)} {z₀ : Fin 2 → ℝ}
    {𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ}
    (h : FieldAt Nk Hk d κ S Z B R' D νg πg ρg Ag Tk jj μ z₀ 𝒯) (hR : 0 < R) (hRR' : R ≤ R') :
    FieldAt Nk Hk d κ S Z B R D νg πg ρg Ag Tk jj μ z₀ 𝒯 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, ?_,
    h20, h21, h22⟩
  intro r hr1 hr2
  exact h19 r ((inv_anti₀ hR hRR').trans hr1) (hr2.trans hRR')

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
