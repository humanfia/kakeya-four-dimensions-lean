import Mathlib
import ChallengeDeps
import Submission.Obl.k4_algebraic_real_jet_comparison.DirectionalComparison
import Submission.Obl.k4_algebraic_real_jet_comparison.DirectionalContinuity
set_option linter.unusedVariables false

/-!
# `Submission.k4_algebraic_real_jet_comparison`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_algebraic_real_jet_comparison`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_algebraic_real_jet_comparison/`
belong to this obligation.
-/

open Submission.Obl.k4_algebraic_real_jet_comparison in
theorem Submission.k4_algebraic_real_jet_comparison : ∀ D : ℕ, ∃ K : ℕ, 1 ≤ K ∧ ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), (∀ v ∈ V, ‖v‖ = 1) ∧ ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ → ℝ, (∀ m : ℕ, 0 < B m) ∧ ∀ (f g : EuclideanSpace ℂ (Fin 3) → ℂ) (P Q : MvPolynomial (Fin 4) ℂ), P ≠ 0 → Q ≠ 0 → P.totalDegree ≤ D → Q.totalDegree ≤ D → DifferentiableOn ℂ f (Metric.ball 0 4) → DifferentiableOn ℂ g (Metric.ball 0 4) → (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4, MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => z i) (f z)) P = 0) → (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4, MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => z i) (g z)) Q = 0) → (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f ((fun x : EuclideanSpace ℝ (Fin 3) => WithLp.toLp 2 (fun i => (x i : ℂ))) x)).im = 0 ∧ (g ((fun x : EuclideanSpace ℝ (Fin 3) => WithLp.toLp 2 (fun i => (x i : ℂ))) x)).im = 0) → (fun F : EuclideanSpace ℝ (Fin 3) → ℝ => (∀ v ∈ V, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (3 : ℝ) / 4 → ContDiffOn ℝ ⊤ (fun t : ℝ => F (x + t • v)) (Set.Ioo (-1 : ℝ) 1)) ∧ (∀ v ∈ V, ∀ m : ℕ, ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => iteratedDeriv m (fun t : ℝ => F (x + t • v)) 0) (Metric.ball 0 1)) ∧ (∀ A : ℝ, 0 < A → (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → ‖f ((fun x : EuclideanSpace ℝ (Fin 3) => WithLp.toLp 2 (fun i => (x i : ℂ))) x) - g ((fun x : EuclideanSpace ℝ (Fin 3) => WithLp.toLp 2 (fun i => (x i : ℂ))) x)‖ ≤ A) → ∀ v ∈ V, ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin 3)), ‖x‖ ≤ (3 : ℝ) / 4 → |iteratedDeriv m (fun t : ℝ => F (x + t • v)) 0| ≤ B m * A) ∧ ∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1 : ℝ) / 2 → ‖y‖ ≤ (1 : ℝ) / 2 → c * ‖f ((fun x : EuclideanSpace ℝ (Fin 3) => WithLp.toLp 2 (fun i => (x i : ℂ))) y) - g ((fun x : EuclideanSpace ℝ (Fin 3) => WithLp.toLp 2 (fun i => (x i : ℂ))) y)‖ ≤ ∑ v ∈ V, ∑ j ∈ Finset.range (K + 1), |iteratedDeriv j (fun t : ℝ => F (x + t • v)) 0|) (fun x => (f ((fun x : EuclideanSpace ℝ (Fin 3) => WithLp.toLp 2 (fun i => (x i : ℂ))) x) - g ((fun x : EuclideanSpace ℝ (Fin 3) => WithLp.toLp 2 (fun i => (x i : ℂ))) x)).re) := by
  classical
  intro D
  obtain ⟨E, hE⟩ := exists_sheet_difference_degree 3 D
  obtain ⟨q, hq, c, hc, V, hVne, hV, B, hB, hcompare⟩ :=
    exists_sheet_directional_comparison E
  refine ⟨q, hq, V, hV, c, hc, B, hB, ?_⟩
  intro f g P Q hP hQ hPD hQD hf hg hProot hQroot hreal
  let h : EuclideanSpace ℂ (Fin 3) → ℂ := fun z => f z - g z
  have hrel := hE f g ⟨P, hP, hPD, hProot⟩ ⟨Q, hQ, hQD, hQroot⟩
  have hdiff : DifferentiableOn ℂ h (Metric.ball 0 4) := hf.sub hg
  have hreal' : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 →
      (h (realEmbedding 3 x)).im = 0 := by
    intro x hx
    obtain ⟨hfreal, hgreal⟩ := hreal x hx
    exact sub_eq_zero.mpr (hfreal.trans hgreal.symm)
  obtain ⟨hupper, hlower⟩ := hcompare h hrel hdiff hreal'
  have hline (x v : EuclideanSpace ℝ (Fin 3)) :
      (fun t : ℝ => (f (WithLp.toLp 2 (fun i => ((x + t • v) i : ℂ))) -
        g (WithLp.toLp 2 (fun i => ((x + t • v) i : ℂ)))).re) =
      (fun t : ℝ => (h
        (realEmbedding 3 x +
          (t : ℂ) • realEmbedding 3 v)).re) := by
    funext t
    change (h (realEmbedding 3 (x + t • v))).re = _
    rw [realEmbedding_line]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv x hx
    rw [hline]
    apply contDiffOn_real_line hdiff
    · simpa only [LinearIsometry.norm_map] using hx
    · simpa only [LinearIsometry.norm_map] using (hV v hv).le
  · intro v hv m
    simp_rw [hline]
    exact continuousOn_real_slice_jet_of_holomorphic
      hdiff v (hV v hv).le m
  · intro A hA hbase v hv m x hx
    rw [hline]
    exact hupper A hA (fun y hy => hbase y (by linarith)) x v hx (hV v hv).le m
  · intro x y hx hy
    obtain ⟨v, hv, j, hj, hlarge⟩ := hlower x y hx hy
    simp_rw [hline]
    apply hlarge.trans
    calc
      _ ≤ ∑ i ∈ Finset.range (q + 1),
          |iteratedDeriv i (fun t : ℝ =>
            (h (realEmbedding 3 x + (t : ℂ) • realEmbedding 3 v)).re) 0| :=
        Finset.single_le_sum (fun i hi => abs_nonneg _)
          (Finset.mem_range.mpr (by omega : j < q + 1))
      _ ≤ _ := Finset.single_le_sum (f := fun w : EuclideanSpace ℝ (Fin 3) =>
        ∑ i ∈ Finset.range (q + 1), |iteratedDeriv i (fun t : ℝ =>
          (h (realEmbedding 3 x + (t : ℂ) • realEmbedding 3 w)).re) 0|)
        (fun w hw => Finset.sum_nonneg (fun i hi => abs_nonneg _)) hv
