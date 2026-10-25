import Submission.Obl.k4_adapted_affine_cube_cover.Finish
import Submission.Obl.k4_adapted_affine_cube_cover.Tiling
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.k4_adapted_affine_cube_cover`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_adapted_affine_cube_cover`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_adapted_affine_cube_cover/`
belong to this obligation.
-/

theorem Submission.k4_adapted_affine_cube_cover : ∀ n : ℕ, 1 ≤ n → ∃ d : ℝ, 0 < d ∧ ∀ η : ℝ, 0 < η → (n : ℝ) * η ≤ (1 / 8 : ℝ) → ∃ C : ℝ, 0 < C ∧ ∀ V : Seminorm ℝ (EuclideanSpace ℝ (Fin n)), Continuous V → (∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ V v) → ∀ c : EuclideanSpace ℝ (Fin n), ∃ (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (k : ℕ) (Q : Fin k → Set (EuclideanSpace ℝ (Fin n))), (∀ i : Fin n, V (b i) ≤ 1) ∧ (k : ℝ) ≤ C * (MeasureTheory.volume {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1}).toReal⁻¹ ∧ (∀ h : Fin k, ∃ a : EuclideanSpace ℝ (Fin n), Q h = (fun t : Fin n → ℝ => a + η • (∑ i : Fin n, t i • b i)) '' Set.Icc (0 : Fin n → ℝ) 1) ∧ (∀ h : Fin k, IsCompact (Q h) ∧ 0 < MeasureTheory.volume (Q h) ∧ Q h ⊆ Metric.ball c 1) ∧ d ≤ ∑ h : Fin k, (MeasureTheory.volume (Q h)).toReal ∧ (∑ h : Fin k, MeasureTheory.volume.restrict (Q h)) ≤ MeasureTheory.volume.restrict (Metric.ball c 1) := by
  intro n hn
  exact Submission.Obl.k4_adapted_affine_cube_cover.cover_of_cube_packing n
    Submission.Obl.k4_adapted_affine_cube_cover.affCube (fun _ _ _ => rfl)
    Submission.Obl.k4_adapted_affine_cube_cover.isCompact_affCube
    (fun b a s hs => Submission.Obl.k4_adapted_affine_cube_cover.volume_affCube b a hs)
    (fun b hb η hη hnη c =>
      Submission.Obl.k4_adapted_affine_cube_cover.exists_tiling b hb hη hnη c)
