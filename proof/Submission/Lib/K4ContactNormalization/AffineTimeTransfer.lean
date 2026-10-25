import Submission.Lib.K4GoodTimes
import Submission.Lib.K4ContactNormalization.ResidualNormalization

/-! Adapted from: here:o200 (session x0696). -/

/-! Extrapolation from stored long-time witnesses. The witness set may be
an arbitrary measurable or nonmeasurable subset of the original time block. -/

namespace Submission.Lib.K4ContactNormalization

open MeasureTheory Set MvPolynomial

noncomputable section

/-- An affine error controlled on a positive fraction of the original time
block is controlled throughout that block, including when the error is zero. -/
theorem affine_bound_of_long_times (a b s q K E : ℝ)
    (hq : 0 < q) (hK : 1 ≤ K) (hE : 0 ≤ E) (A : Set ℝ)
    (hA : A ⊆ Icc s (s + q)) (hmass : ENNReal.ofReal (q / K) ≤ volume A)
    (hbound : ∀ t ∈ A, |a * t + b| ≤ E) :
    ∀ t ∈ Icc s (s + q), |a * t + b| ≤ 8 * K * E := by
  have hK0 : 0 < K := by linarith
  intro t ht
  by_contra h
  have hlarge : 8 * K * E < |a * t + b| := lt_of_not_ge h
  set M := |a * t + b|
  have hM : 0 < M := lt_of_le_of_lt (by positivity) hlarge
  set epsilon := M / (8 * K)
  have hepsilon : E < epsilon := (lt_div_iff₀ (by positivity)).mpr (by nlinarith [hlarge])
  have hepsilonM : epsilon ≤ M / 2 := by
    apply div_le_div_of_nonneg_left hM.le (by norm_num)
    linarith
  have hcover : A ⊆ {u : ℝ | u ∈ Icc s (s + q) ∧ |a * u + b| < epsilon} := by
    intro u hu
    exact ⟨hA hu, (hbound u hu).trans_lt hepsilon⟩
  have hsmall := Submission.Lib.K4GoodTimes.volume_affine_sublevel_on_interval
    a b s q M epsilon hq hM (by positivity) hepsilonM ⟨t, ht, le_rfl⟩
  have hcancel : 4 * epsilon * q / M = q / (2 * K) := by
    dsimp only [epsilon]
    field_simp
    ring
  rw [hcancel] at hsmall
  have hle := hmass.trans ((measure_mono hcover).trans hsmall)
  have hreal : q / K ≤ q / (2 * K) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have hstrict : q / (2 * K) < q / K :=
    div_lt_div_of_pos_left hq hK0 (by linarith)
  exact (not_lt_of_ge hreal) hstrict

theorem affine_hidden_residual (L : Fin 4 → ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point b t) (affineBase L) - point b t 3 =
      (L 1 + L 2 * b 3 + L 3 * b 4 - b 5) * t +
        (L 0 + L 2 * b 0 + L 3 * b 1 - b 2) := by
  simp [point, affineBase]
  ring

/-- Stored long witnesses give the affine predictor on the full original
block, without a bound on any affine coefficient. -/
theorem affine_predictor_full_time (L : Fin 4 → ℝ) (b : Fin 6 → ℝ)
    (s q K E : ℝ) (hq : 0 < q) (hK : 1 ≤ K) (hE : 0 ≤ E)
    (A : Set ℝ) (hA : A ⊆ Icc s (s + q))
    (hmass : ENNReal.ofReal (q / K) ≤ volume A)
    (hbound : ∀ t ∈ A, |eval (point b t) (affineBase L) - point b t 3| ≤ E) :
    ∀ t ∈ Icc s (s + q), |eval (point b t) (affineBase L) - point b t 3| ≤ 8 * K * E := by
  simp only [affine_hidden_residual] at hbound ⊢
  exact affine_bound_of_long_times _ _ s q K E hq hK hE A hA hmass hbound

end
end Submission.Lib.K4ContactNormalization
