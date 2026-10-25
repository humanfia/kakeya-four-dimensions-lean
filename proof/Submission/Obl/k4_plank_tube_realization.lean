import Submission.Obl.k4_plank_tube_realization.Clustering
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.k4_plank_tube_realization`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_plank_tube_realization`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_plank_tube_realization/`
belong to this obligation.
-/

theorem Submission.k4_plank_tube_realization : ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ) (b u : Fin n → EuclideanSpace ℝ (Fin 2)) (ω : Fin n → ℝ) (A : ℝ) (J : Fin n → Finset (Fin D)), (∀ i : Fin n, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i : Fin n, 0 < ω i) → 0 < A → (∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ), ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → 1 ≤ a → a ≤ β → β ≤ (D : ℝ) → ∀ S : Finset (Fin n), (∀ i ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1, |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a / (D : ℝ) ∧ |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ)) → ∑ i ∈ S, ω i ≤ A * a * β) → ∃ (x v : Fin n → EuclideanSpace ℝ (Fin 3)) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))), (∀ i : Fin n, ‖v i‖ = 1) ∧ (∀ i : Fin n, Metric.thickening (1 / (100 * (D : ℝ))) (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧ (∀ i : Fin n, MeasurableSet (Y i)) ∧ (∀ i : Fin n, Y i ⊆ Metric.thickening (1 / (100 * (D : ℝ))) (segment ℝ (x i) (x i + v i))) ∧ (∀ i : Fin n, c * ((J i).card : ℝ) / (D : ℝ) ^ 3 ≤ (MeasureTheory.volume (Y i)).toReal) ∧ (∀ W : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → ∀ S : Finset (Fin n), (∀ i ∈ S, Metric.thickening (1 / (100 * (D : ℝ))) (segment ℝ (x i) (x i + v i)) ⊆ W) → ENNReal.ofReal ((∑ i ∈ S, ω i) / (D : ℝ) ^ 2) ≤ ENNReal.ofReal (K * A) * MeasureTheory.volume W) ∧ (MeasureTheory.volume (⋃ i : Fin n, Y i)).toReal ≤ K * ((((Finset.univ : Finset (Fin n)).sigma J).image (fun p => ((p.2 : ℕ), fun k : Fin 2 => ⌊(D : ℝ) * (b p.1 + (((((p.2 : ℕ) : ℝ) + 1 / 2) / (D : ℝ)) • u p.1)) k⌋))).card : ℝ) / (D : ℝ) ^ 3 := by
  refine ⟨Real.pi / 6000000, 27000000000, by positivity, by norm_num, ?_⟩
  intro D hD n b u ω A J hbu hω hA hcap
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  refine ⟨(fun i => Submission.Lib.K4PlankGeometry.tubeBase (b i) (u i)),
    (fun i => Submission.Lib.K4PlankGeometry.unitDirection (u i)),
    (fun i => Submission.Lib.K4PlankGeometry.markedShading D (b i) (u i) (J i)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Submission.Lib.K4PlankGeometry.unitDirection_norm (u i)
  · intro i
    exact Submission.Lib.K4PlankGeometry.unitTube_subset_ball hD (hbu i).1 (hbu i).2
  · intro i
    exact Submission.Lib.K4PlankGeometry.markedShading_measurable D (b i) (u i) (J i)
  · intro i
    exact Submission.Lib.K4PlankGeometry.markedShading_subset_tube hD (hbu i).2 (J i)
  · intro i
    rw [Submission.Lib.K4PlankGeometry.markedShading_volume_eq hD,
      ENNReal.toReal_ofReal (by positivity)]
  · intro W hW S hSW
    exact Submission.Obl.k4_plank_tube_realization.ConvexGeometry.weighted_convex_clustering
      hD b u ω hA hbu hcap W hW S hSW
  · have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top)
      (Submission.Lib.K4PlankGeometry.markedShading_union_volume_le hD b u J)
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    apply h.trans
    change (Real.pi * 4 / 3) *
      ((Submission.Lib.K4PlankGeometry.visitedCells b u J).card : ℝ) / (D : ℝ)^3 ≤
      27000000000 * ((Submission.Lib.K4PlankGeometry.visitedCells b u J).card : ℝ) /
        (D : ℝ)^3
    gcongr
    nlinarith [Real.pi_lt_four]

