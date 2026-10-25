import Mathlib
import ChallengeDeps
import Submission.Lib.KakeyaCovering.GraphReduction
import Submission.Obl.k4_lower_of_discrete.Localization
set_option linter.unusedVariables false

/-!
# `Submission.k4_lower_of_discrete`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_lower_of_discrete`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_lower_of_discrete/`
belong to this obligation.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal
open Submission.Obl.k4_lower_of_discrete

theorem Submission.k4_lower_of_discrete : (∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ c : ℝ, 0 < c → ∀ R : ℝ, 1 ≤ R → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (n : ℕ) (x v : Fin n → EuclideanSpace ℝ (Fin 4)), c * (2 : ℝ) ^ (3 * k) / ((k : ℝ) + 1) ^ 2 ≤ (n : ℝ) → (∀ i : Fin n, x i 0 = 0 ∧ v i 0 = 1 ∧ ‖v i‖ ≤ 2) → (∀ i j : Fin n, i ≠ j → (2 : ℝ) ^ (-(k : ℤ)) ≤ ‖v i - v j‖) → (∀ i : Fin n, ‖x i‖ ≤ R) → ∀ (m : ℕ) (z : Fin m → EuclideanSpace ℝ (Fin 4)) (ρ : Fin m → ℝ), (m : ℝ) ≤ (2 : ℝ) ^ (((k : ℝ) + 1) * (4 - σ)) → (∀ j : Fin m, (2 : ℝ) ^ (-((k : ℤ) + 1)) < ρ j ∧ ρ j ≤ (2 : ℝ) ^ (-(k : ℤ))) → ¬ (∀ i : Fin n, ENNReal.ofReal (c / ((k : ℝ) + 1) ^ 2) ≤ MeasureTheory.volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ x i + t • v i ∈ ⋃ j : Fin m, Metric.ball (z j) (ρ j)})) → ∀ K : Set (EuclideanSpace ℝ (Fin 4)), (∀ e ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, ∃ a : EuclideanSpace ℝ (Fin 4), segment ℝ a (a + e) ⊆ K) → (4 : ENNReal) ≤ dimH K := by
  classical
  intro hDiscrete K hK
  obtain ⟨S, x, w, hS, hS0, hx⟩ := exists_graph_localization hK
  let E : Set E4 := (fun y : E4 => (2 : ℝ) • y - w) '' K
  have hfour : (4 : ENNReal) ≤ dimH E := by
    apply Submission.Lib.KakeyaCovering.four_le_dimH_of_bounded_graph_family
      hDiscrete E S (isBounded_closedBall.subset hS) hS0 x slopeVec 2 (by norm_num)
    · intro u hu
      refine ⟨(hx u hu).1, slopeVec_apply_zero u, ?_⟩
      have hu' : ‖u‖ ≤ 1 / 2 := by
        simpa only [mem_closedBall, dist_zero_right] using hS hu
      exact (norm_slopeVec_le hu').trans (by norm_num)
    · intro u hu
      exact (hx u hu).2.1
    · intro u hu v hv
      rw [norm_slopeVec_sub, dist_eq_norm]
    · intro u hu t ht
      exact (hx u hu).2.2 t ht
  have hLip : LipschitzWith 2 (fun y : E4 => (2 : ℝ) • y - w) := by
    apply LipschitzWith.of_dist_le_mul
    intro y y'
    have heq : (2 : ℝ) • y - w - ((2 : ℝ) • y' - w) = (2 : ℝ) • (y - y') := by module
    rw [dist_eq_norm, heq, norm_smul, dist_eq_norm]
    norm_num
  exact hfour.trans (hLip.dimH_image_le K)
