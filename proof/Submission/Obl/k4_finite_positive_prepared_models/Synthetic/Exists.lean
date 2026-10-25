import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.ModelEH3

/-!
# A data-free prepared stage model

For all rates `0 ≤ d₁ < 1`, `0 < κ₁ ≤ 1`, `0 < ℓ`, every `S ≤ 1` and every stage `n` there is
a model index with `StageGood d₁ κ₁ ℓ S n`: the synthetic model of stage `max n 2`. Written by
x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set

noncomputable section

namespace Par

variable (p : Par)

theorem n_add_two_le_sN : (p.n : ℝ) + 2 ≤ p.sN := by
  have h1 : (p.n : ℝ) + 2 ≤ p.Λ := by
    have := p.Λ_ge2
    have : (0 : ℝ) ≤ p.B := by positivity
    have : (0 : ℝ) ≤ p.n := by positivity
    nlinarith
  have h2 : (p.Λ : ℝ) ≤ p.sN := by
    unfold sN
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self (n := p.Λ)).le
  linarith

theorem one_le_sN : 1 ≤ p.sN := by
  have := p.n_add_two_le_sN
  have : (0 : ℝ) ≤ p.n := by positivity
  linarith

end Par

/-- **A data-free `StageGood` model.** -/
theorem exists_stageGood (d₁ κ₁ ℓ S : ℝ) (n : ℕ) (hd₁ : 0 ≤ d₁) (hd₁' : d₁ < 1)
    (hκ : 0 < κ₁) (hκ' : κ₁ ≤ 1) (hℓ : 0 < ℓ) (hS : S ≤ 1) :
    ∃ st : EStage (ℕ × (Fin 6 → ℝ)), StageGood d₁ κ₁ ℓ S n st := by
  by_cases hn : 2 ≤ n
  · let p : Par := ⟨n, d₁, κ₁, ℓ, hn, hd₁, hd₁', hκ, hκ', hℓ⟩
    exact ⟨p.stage, p.n_add_two_le_sN, ⟨p.one_le_sK, le_rfl⟩, p.eh1,
      fun R hR hRn => ⟨p.eh2 S hS R hR hRn, p.eh3 R hR hRn, p.eh4 R⟩⟩
  · let p : Par := ⟨2, d₁, κ₁, ℓ, le_rfl, hd₁, hd₁', hκ, hκ', hℓ⟩
    have hn1 : (n : ℝ) ≤ 1 := by exact_mod_cast (by omega : n ≤ 1)
    have hn0 : (0 : ℝ) ≤ n := by positivity
    refine ⟨p.stage, ?_, ⟨p.one_le_sK, ?_⟩, p.eh1, fun R hR hRn => ?_⟩
    · have := p.n_add_two_le_sN
      show (n : ℝ) + 2 ≤ p.sN
      have h2 : (p.n : ℝ) = 2 := by norm_num [p]
      linarith
    · show p.sN ^ (1 / ((p.n : ℝ) + 1)) ≤ p.sN ^ (1 / ((n : ℝ) + 1))
      apply Real.rpow_le_rpow_of_exponent_le p.one_le_sN
      have h2 : (p.n : ℝ) = 2 := by norm_num [p]
      rw [h2]
      apply one_div_le_one_div_of_le (by linarith)
      linarith
    · exfalso
      linarith

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
