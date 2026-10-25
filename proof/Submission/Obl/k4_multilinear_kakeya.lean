import Mathlib
import ChallengeDeps
import Submission.Obl.k4_multilinear_kakeya.Scaling
import Submission.Obl.k4_mk_visibility
import Submission.Obl.k4_mk_finite_duality
import Submission.Obl.k4_mk_grid_transfer

set_option linter.unusedVariables false

/-!
The planar case uses the two-strip estimate.  In dimensions three and four,
visibility supplies the determinant maps in finite duality; the resulting
lattice estimate is transferred to Euclidean Lebesgue measure and scaled.
-/

theorem Submission.k4_multilinear_kakeya : ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ (N : Fin n → ℕ) (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n)) (w : (i : Fin n) → Fin (N i) → ℝ), (∀ (i : Fin n) (k : Fin (N i)), ‖e i k‖ = 1) → (∀ (i : Fin n) (k : Fin (N i)), 0 ≤ w i k) → MeasureTheory.lintegral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal ((∑ T : ((i : Fin n) → Fin (N i)), |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, (w i (T i) * (Metric.thickening r (Set.range fun t : ℝ => a i (T i) + t • e i (T i))).indicator (fun _ => (1 : ℝ)) x)) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤ ENNReal.ofReal (C * r ^ n * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1))) := by
  intro n hn hn4
  by_cases hn2 : n = 2
  · subst n
    exact Submission.Obl.k4_multilinear_kakeya.planar_kakeya
  have hn3 : 3 ≤ n := by omega
  obtain ⟨K, hK, hvisibility⟩ := Submission.k4_mk_visibility n hn3 hn4
  refine ⟨K ^ ((n : ℝ) / ((n : ℝ) - 1)), Real.rpow_pos_of_pos hK _, ?_⟩
  intro r hr N a e w he hw
  apply Submission.Obl.k4_multilinear_kakeya.kakeya_scaling
    (C := K ^ ((n : ℝ) / ((n : ℝ) - 1))) ?_ hr N a e w he hw
  apply Submission.k4_mk_grid_transfer n hn hn4 _ (Real.rpow_pos_of_pos hK _)
  intro m z hz N a e w he hw
  let b : Fin m → (i : Fin n) → Fin (N i) → ℝ := fun q i k =>
    (Metric.thickening (3 : ℝ) (Set.range fun t : ℝ => a i k + t • e i k)).indicator
      (fun _ => (1 : ℝ)) (WithLp.toLp 2 (fun j : Fin n => (z q j : ℝ)))
  have hb : ∀ (q : Fin m) (i : Fin n) (k : Fin (N i)), 0 ≤ b q i k := by
    intro q i k
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hmaps : ∀ M : Fin m → ℝ, (∀ q : Fin m, 0 ≤ M q) →
      (∑ q : Fin m, M q) = 1 →
      ∃ A : Fin m → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)),
        (∀ q : Fin m, M q ≤ |LinearMap.det (A q)|) ∧
        ∀ (i : Fin n) (k : Fin (N i)),
          (∑ q : Fin m, b q i k * ‖A q (e i k)‖) ≤ K := by
    intro M hM hsum
    obtain ⟨A, hdet, hbudget⟩ := hvisibility m z hz M hM hsum
    exact ⟨A, hdet, fun i k => hbudget (a i k) (e i k) (he i k)⟩
  exact Submission.k4_mk_finite_duality n hn K hK m N e b hb hmaps w hw
