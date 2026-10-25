import Mathlib

namespace Submission.Obl.k4_finite_width_path_realization

/-- Terminal width and complementary segment bounds control every node. -/
theorem squeeze_width {ell zeta z w ε q lam : ℝ} {m : ℕ} {r s nw : ℕ → ℝ}
    (hell : 0 ≤ ell) (hζ : 0 < zeta) (hz : z ≤ zeta / 4)
    (hw : 0 ≤ w ∧ w ≤ ell ∧ ell - w ≤ z)
    (hε : ell * ε ≤ zeta / 4) (hlam : lam ≤ zeta / 4)
    (herr : (m : ℝ) * (q + 2 * lam) ≤ zeta / 4)
    (hrlast : r (m - 1) = 1)
    (hlast : nw (m - 1) < ell + zeta + lam)
    (i : ℕ) (hr : 0 ≤ r i ∧ r i ≤ 1) (hclose : |r i - s i| ≤ ε)
    (hlower : w * r i - (m : ℝ) * (q + 2 * lam) ≤ nw i)
    (hcomp : nw i + w * (r (m - 1) - r i) - (m : ℝ) * (q + 2 * lam) ≤ nw (m - 1)) :
    |nw i - ell * s i| ≤ 4 * zeta := by
  have hc := abs_le.mp hclose
  have hc₁ := mul_le_mul_of_nonneg_left hc.1 hell
  have hc₂ := mul_le_mul_of_nonneg_left hc.2 hell
  have hdiff : 0 ≤ ell - w := sub_nonneg.mpr hw.2.1
  have hroot := mul_le_mul_of_nonneg_left hr.2 hdiff
  have htail := mul_nonneg hdiff hr.1
  rw [hrlast] at hcomp
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Error budgets are chosen without dividing by ell or by any grid gap. -/
theorem path_error_budgets {ell zeta e a : ℝ} {m : ℕ}
    (hell : 0 ≤ ell) (hζ : 0 < zeta) (he : 0 < e) (ha : 0 < a) :
    ∃ ε q lam : ℝ, 0 < ε ∧ ε ≤ e ∧ ε ≤ 1 ∧ ε ≤ a / 2 ∧
      ell * ε ≤ zeta / 4 ∧ 0 < q ∧ 0 < lam ∧ lam ≤ e ∧ lam ≤ zeta / 4 ∧
      (m : ℝ) * (q + 2 * lam) ≤ zeta / 4 := by
  let ε := min (min e (min 1 (a / 2))) (zeta / (4 * (ell + 1)))
  let q := zeta / (8 * ((m : ℝ) + 1))
  let lam := min (e / 2) (zeta / (16 * ((m : ℝ) + 1)))
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hε : 0 < ε := lt_min (lt_min he (lt_min zero_lt_one (by positivity))) (by positivity)
  have hlam : 0 < lam := lt_min (by positivity) (by positivity)
  have hεcap : ε ≤ zeta / (4 * (ell + 1)) := min_le_right _ _
  have hεmul : ε * (4 * (ell + 1)) ≤ zeta := (le_div_iff₀ (by positivity)).mp hεcap
  have hlamcap : lam ≤ zeta / (16 * ((m : ℝ) + 1)) := min_le_right _ _
  have hlammul : lam * (16 * ((m : ℝ) + 1)) ≤ zeta := (le_div_iff₀ (by positivity)).mp hlamcap
  have hqmul : q * (8 * ((m : ℝ) + 1)) = zeta := by dsimp [q]; field_simp
  refine ⟨ε, q, lam, hε, (min_le_left _ _).trans (min_le_left _ _),
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)), ?_,
    by dsimp [q]; positivity, hlam, (min_le_left _ _).trans (by linarith), ?_, ?_⟩
  · nlinarith
  · nlinarith [mul_nonneg hlam.le (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  · nlinarith [hlam.le]

end Submission.Obl.k4_finite_width_path_realization
