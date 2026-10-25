import Submission.Lib.K4ModelReduction.Diagonal
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_scalar_capped_heavy_potential

open Filter

noncomputable section

/-- A growing compact-range diagonal can retain polynomially strong
palette breadth at a slowly vanishing exponent. Its inverse radius is
still subpower, and the same diagonal retains every earlier requirement. -/
theorem exists_slow_palette_scale (N H : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : ∀ k, 1 ≤ H k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    (S A δ : ℝ) (hS : 0 < S) (hA : 0 ≤ A) (hδ : 0 < δ) (p : ℕ)
    (P : ℕ → ℕ → Prop) (hP : ∀ j, ∀ᶠ k in atTop, P j k) :
    ∃ J : ℕ → ℕ, Monotone J ∧ Tendsto J atTop atTop ∧
      ((∀ k, 1 ≤ N k ^ (1 / ((J k : ℝ) + 2))) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, N k ^ (1 / ((J k : ℝ) + 2)) ≤ N k ^ ε) ∧
      ∀ᶠ k in atTop, (∀ j ≤ J k, P j k) ∧
        A * H k ^ p * N k ^ (-S / ((J k : ℝ) + 2)) ≤ δ := by
  let Good : ℕ → ℕ → Prop := fun j k => P j k ∧
    A * H k ^ p * N k ^ (-S / ((j : ℝ) + 2)) ≤ δ
  have hGood (j : ℕ) : ∀ᶠ k in atTop, Good j k := by
    have ha : -S / ((j : ℝ) + 2) < 0 := by
      have hh := div_pos hS (show 0 < (j : ℝ) + 2 by positivity)
      rw [neg_div]
      linarith
    have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN hNt hH hsub p ha (A := A / δ) (by positivity)
    filter_upwards [hP j, hsmall] with k hk hs
    refine ⟨hk, ?_⟩
    simp only [Real.rpow_zero] at hs
    have hh : (A * H k ^ p * N k ^ (-S / ((j : ℝ) + 2))) / δ < 1 := by
      convert hs using 1 <;> ring
    simpa only [one_mul] using ((div_lt_iff₀ hδ).mp hh).le
  obtain ⟨J, hJmono, hJ, _, hgood⟩ :=
    Submission.Lib.K4ModelReduction.exists_slow_diagonal Good hGood
  refine ⟨J, hJmono, hJ, ⟨?_, ?_⟩, ?_⟩
  · intro k
    exact Real.one_le_rpow (hN k) (by positivity)
  · intro ε hε
    filter_upwards [hJ.eventually (eventually_ge_atTop ⌈1 / ε⌉₊)] with k hk
    apply Real.rpow_le_rpow_of_exponent_le (hN k)
    have hJε : 1 / ε ≤ (J k : ℝ) :=
      (Nat.le_ceil (1 / ε)).trans (by exact_mod_cast hk)
    apply (div_le_iff₀ (by positivity : 0 < (J k : ℝ) + 2)).2
    have hmul := (div_le_iff₀ hε).mp hJε
    nlinarith
  · filter_upwards [hgood] with k hk
    exact ⟨fun j hj => (hk j hj).1, (hk (J k) le_rfl).2⟩

end
end Submission.Obl.k4_scalar_capped_heavy_potential
