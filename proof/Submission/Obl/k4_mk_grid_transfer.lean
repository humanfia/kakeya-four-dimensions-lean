import Mathlib
import ChallengeDeps
import Submission.Obl.k4_mk_grid_transfer.Grid
set_option linter.unusedVariables false

/-!
# `Submission.k4_mk_grid_transfer`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_mk_grid_transfer`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_mk_grid_transfer/`
belong to this obligation.
-/

theorem Submission.k4_mk_grid_transfer : ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∀ C : ℝ, 0 < C → (∀ (m : ℕ) (z : Fin m → Fin n → ℤ), Function.Injective z → ∀ (N : Fin n → ℕ) (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n)) (w : (i : Fin n) → Fin (N i) → ℝ), (∀ (i : Fin n) (k : Fin (N i)), ‖e i k‖ = 1) → (∀ (i : Fin n) (k : Fin (N i)), 0 ≤ w i k) → (∑ q : Fin m, (∑ T : ((i : Fin n) → Fin (N i)), |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, (w i (T i) * (Metric.thickening (3 : ℝ) (Set.range fun t : ℝ => a i (T i) + t • e i (T i))).indicator (fun _ => (1 : ℝ)) (WithLp.toLp 2 (fun j : Fin n => (z q j : ℝ))))) ^ ((1 : ℝ) / ((n : ℝ) - 1))) ≤ C * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1))) → ∀ (N : Fin n → ℕ) (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n)) (w : (i : Fin n) → Fin (N i) → ℝ), (∀ (i : Fin n) (k : Fin (N i)), ‖e i k‖ = 1) → (∀ (i : Fin n) (k : Fin (N i)), 0 ≤ w i k) → MeasureTheory.lintegral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal ((∑ T : ((i : Fin n) → Fin (N i)), |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, (w i (T i) * (Metric.thickening 1 (Set.range fun t : ℝ => a i (T i) + t • e i (T i))).indicator (fun _ => (1 : ℝ)) x)) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤ ENNReal.ofReal (C * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1))) := by
  intro n hn hn4 C hC hgrid N a e w he hw
  exact Submission.Obl.k4_mk_grid_transfer.unit_integral_le_grid
    hn hn4 hgrid N a e w he hw
