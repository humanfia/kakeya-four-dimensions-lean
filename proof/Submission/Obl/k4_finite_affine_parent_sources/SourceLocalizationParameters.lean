import Submission.Obl.k4_finite_affine_parent_sources.SourceSampleNumerics

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- One hundredth of the tangent interval pays the row-localization tail. -/
theorem selection_budget_fraction {n : ℕ} {ρ unit L : ℝ}
    (hρ : 0 ≤ ρ) (huL : 0 ≤ unit * L) :
    selectionBudget n ρ unit L ≤ ρ * (unit * L) / 100 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ groupsC := Nat.cast_nonneg _
  have hθ : stagePower n ρ ≤ ρ := by
    unfold stagePower
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hb : stagePower n ρ / (100 * ((groupsC : ℝ) + 2)) ≤ ρ / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hb huL
  change unit * L * stagePower n ρ / (100 * ((groupsC : ℝ) + 2)) ≤ _
  calc unit * L * stagePower n ρ / (100 * ((groupsC : ℝ) + 2))
      = unit * L * (stagePower n ρ / (100 * ((groupsC : ℝ) + 2))) := by ring
    _ ≤ unit * L * (ρ / 100) := hh
    _ = _ := by ring

/-- A row bound just above the tangent reciprocal scale is still below the
native scale, and its exceptional labels cost at most one inverse budget power. -/
theorem sample_localization_constants {Nk b len ρ ε κ A : ℝ}
    (hNk : 1 < Nk) (hlen : 0 ≤ len) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hε : 0 ≤ ε)
    (hκ : 0 ≤ κ) (hA1 : 1 ≤ A) (hκA : 12 * κ ≤ A) (hAeq : A = Nk ^ b)
    (hb : b ≤ ρ * len / 100) :
    1 ≤ A * Nk ^ (len / 100) ∧ 6 * κ ≤ A * Nk ^ (len / 100) ∧
      A * Nk ^ (len / 100) ≤ Nk ^ len ∧
      12 * κ / (Nk ^ (ρ * (len / 100) + ε) * Nk ^ (-(len / 100))) ≤
        A * Nk ^ (len / 100) ∧
      Nk ^ (-ρ * (len / 100) - ε) ≤ A⁻¹ := by
  have hNk0 : 0 < Nk := by linarith
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hpow : 1 ≤ Nk ^ (len / 100) := Real.one_le_rpow hNk.le (by positivity)
  have hAH : A ≤ A * Nk ^ (len / 100) := le_mul_of_one_le_right hA0 hpow
  refine ⟨hA1.trans hAH, (by linarith : 6 * κ ≤ A).trans hAH, ?_, ?_, ?_⟩
  · rw [hAeq, ← Real.rpow_add hNk0]
    apply Real.rpow_le_rpow_of_exponent_le hNk.le
    have hrl : ρ * len ≤ len := by nlinarith
    linarith
  · rw [div_le_iff₀ (by positivity)]
    have hfirst : 12 * κ ≤ A * Nk ^ (ρ * (len / 100) + ε) :=
      hκA.trans (le_mul_of_one_le_right hA0
        (Real.one_le_rpow hNk.le (by positivity)))
    convert hfirst using 1
    have hcancel : Nk ^ (len / 100) * Nk ^ (-(len / 100)) = 1 := by
      rw [← Real.rpow_add hNk0]
      simp
    calc (A * Nk ^ (len / 100)) * (Nk ^ (ρ * (len / 100) + ε) * Nk ^ (-(len / 100)))
        = (A * Nk ^ (ρ * (len / 100) + ε)) *
          (Nk ^ (len / 100) * Nk ^ (-(len / 100))) := by ring
      _ = _ := by rw [hcancel, mul_one]
  · rw [hAeq, ← Real.rpow_neg hNk0.le]
    apply Real.rpow_le_rpow_of_exponent_le hNk.le
    linarith

end

end Submission.Obl.k4_finite_affine_parent_sources
