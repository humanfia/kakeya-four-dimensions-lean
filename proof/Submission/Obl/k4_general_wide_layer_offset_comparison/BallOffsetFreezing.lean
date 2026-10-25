import Submission.Obl.k4_scalar_initial_true_horizon.InitialAsymptotic
import Submission.Obl.k4_stable_native_signal_oscillation.PolynomialBounds

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/BallOffsetFreezing.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Filter MvPolynomial

noncomputable section

/-- A discrepancy controlled on the real matching ball freezes on every
short subset of the unit ball. This uses the original polynomial difference,
so its value at the chosen reference point is one literal constant. -/
theorem eventually_freeze_ball_offset {N H : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : ∀ k, 1 ≤ H k)
    (hHs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    {s u C : ℝ} (hu : 0 < u) :
    ∀ᶠ k in atTop, ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ 2 →
      (∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 2 →
        |eval (fun i => z i) P| ≤ H k * N k ^ (-s + C * u)) →
      ∀ z z₀ : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 → ‖z₀‖ ≤ 1 →
      ‖z - z₀‖ ≤ H k * N k ^ (-(C + 3) * u) →
      |eval (fun i => z i) P - eval (fun i => z₀ i) P| ≤ N k ^ (-s - u) := by
  obtain ⟨L, hL, hlip⟩ :=
    Submission.Obl.k4_stable_native_signal_oscillation.exists_polynomial_lipschitz_of_ball_bound 2
  filter_upwards [hHs (u / 2) (by positivity),
    Submission.Obl.k4_scalar_initial_true_horizon.eventually_const_le_rpow hNt hu L]
    with k hHk hLk
  intro P hP hbound z z₀ hz hz₀ hdiam
  have hNp : 0 < N k := by linarith [hN k]
  have hH0 : 0 ≤ H k := by linarith [hH k]
  have hcost : L * H k ^ 2 ≤ N k ^ (2 * u) := by
    calc
      _ ≤ N k ^ u * (N k ^ (u / 2)) ^ 2 := by gcongr
      _ = N k ^ (2 * u) := by
        rw [← Real.rpow_mul_natCast hNp.le, ← Real.rpow_add hNp]
        congr 1
        ring
  have hshort (y : EuclideanSpace ℝ (Fin 3)) (hy : ‖y‖ ≤ 1 / 8) :
      |eval (fun i => y i) P| ≤ H k * N k ^ (-s + C * u) :=
    hbound y (by linarith)
  calc
    _ ≤ L * (H k * N k ^ (-s + C * u)) * ‖z - z₀‖ :=
      hlip P hP _ (by positivity) hshort z z₀ hz hz₀
    _ ≤ L * (H k * N k ^ (-s + C * u)) *
        (H k * N k ^ (-(C + 3) * u)) := by gcongr
    _ = (L * H k ^ 2) * N k ^ (-s - 3 * u) := by
      rw [show L * (H k * N k ^ (-s + C * u)) *
          (H k * N k ^ (-(C + 3) * u)) =
          (L * H k ^ 2) * (N k ^ (-s + C * u) * N k ^ (-(C + 3) * u)) by ring]
      rw [← Real.rpow_add hNp]
      congr 2
      ring
    _ ≤ N k ^ (2 * u) * N k ^ (-s - 3 * u) := by gcongr
    _ = N k ^ (-s - u) := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
