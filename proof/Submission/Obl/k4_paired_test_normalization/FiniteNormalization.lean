-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/FiniteNormalization.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.CurvatureCut
import Submission.Obl.k4_paired_test_normalization.NormalizedPairDeletion

namespace Submission.Obl.k4_paired_test_normalization

open MvPolynomial Set Metric MeasureTheory
open Submission.Obl.k4_quadratic_atlas_normalization

/-- The finite analytic normalization step. All equations and both pair roles
are treated together; the geometric data and original measure are parameters. -/
theorem finite_test_normalization :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
        (μ : Measure Ω) (H : ι → ι → Set Ω) (P : ι → MvPolynomial (Fin 4) ℝ)
        (z : ι → Ω → EuclideanSpace ℝ (Fin 3)) (w : ι → Ω → ℝ) (β : ι → ℝ)
        (c V ρ U B b₀ η θ : ℝ),
      (∀ i j, MeasurableSet (H i j)) →
      (∀ j, Pairwise fun i k => Disjoint (H i j) (H k j)) →
      (∀ i, (P i).totalDegree ≤ 2) → (∀ i m, |(P i).coeff m| ≤ V) →
      (∀ i, Measurable (z i)) → (∀ i, 0 ≤ β i) →
      (∀ i p, p ∈ (⋃ j, H i j) ∪ (⋃ j, H j i) →
        ‖z i p‖ ≤ 1 / 8 ∧
        |eval (Fin.snoc (fun k => z i p k) (w i p)) (P i)| ≤ ρ ∧
        B ≤ |eval (Fin.snoc (fun k => z i p k) (w i p)) (pderiv (3 : Fin 4) (P i))| ∧
        |eval (Fin.snoc (fun k => z i p k) (w i p)) (pderiv (3 : Fin 4) (P i))| ≤ U) →
      (∀ i (A : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet A →
        μ ((⋃ j, H i j) ∩ (z i ⁻¹' A)) ≤ ENNReal.ofReal (β i) * volume A) →
      (∀ i (A : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet A →
        μ ((⋃ j, H j i) ∩ (z i ⁻¹' A)) ≤ ENNReal.ofReal (β i) * volume A) →
      0 < c → 0 ≤ V → 0 ≤ ρ → 0 ≤ U → 0 ≤ B →
      0 < b₀ → b₀ ≤ min (B ^ 2 / 2) 1 → 0 < η → 0 < θ → θ ≤ 1 →
      2 * c * ρ ≤ B ^ 2 / 2 → 2 * c * ρ ≤ η / 2 →
      1152 * C * η < min b₀ 1 * θ ^ 2 →
      ∃ (R : ι → MvPolynomial (Fin 4) ℝ) (H' : ι → ι → Set Ω),
        (∀ i, (R i).totalDegree ≤ 2 ∧ |curvature (R i) (3 : Fin 4)| ≤ c ∧
          (∀ m, |(R i).coeff m| ≤ max V (2 * V / c)) ∧
          (disc (R i)).totalDegree ≤ 2 ∧ (∀ m, |(disc (R i)).coeff m| ≤ 1)) ∧
        (∀ i (y : Fin 4 → ℝ), |eval y (P i)| ≤ ρ →
          |eval y (pderiv (3 : Fin 4) (P i))| ≤ U →
          |eval y (R i)| ≤ max ρ (U / c) ∧
          |eval y (pderiv (3 : Fin 4) (R i))| ≤ max U 1 ∧
          2 * |curvature (R i) (3 : Fin 4) * eval y (R i)| ≤ 2 * c * ρ) ∧
        (∀ i j, MeasurableSet (H' i j) ∧ H' i j ⊆ H i j) ∧
        (∀ i j p, p ∈ H' i j →
          η < eval (fun k => z i p k) (disc (R i)) ∧
          η < eval (fun k => z j p k) (disc (R j)) ∧
          η / 2 ≤ (eval (Fin.snoc (fun k => z i p k) (w i p))
            (pderiv (3 : Fin 4) (R i))) ^ 2 ∧
          η / 2 ≤ (eval (Fin.snoc (fun k => z j p k) (w j p))
            (pderiv (3 : Fin 4) (R j))) ^ 2) ∧
        (∑ i, μ (⋃ j, H i j)) ≤ (∑ i, μ (⋃ j, H' i j)) +
          2 * ∑ i, ENNReal.ofReal (β i) *
            (ENNReal.ofReal (128 * θ) *
              volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 8))) := by
  classical
  obtain ⟨C, hC, hdelete⟩ := normalized_pair_deletion
  refine ⟨C, hC, ?_⟩
  intro Ω ι _ _ μ H P z w β c V ρ U B b₀ η θ hH hdisj hP hcoeff hz hβ
    hpoint hsource hwitness hc hV hρ hU hB hb₀ hb₀floor hη hθ hθ1 hraw hcross hsmall
  let Q (i : ι) := curvatureCut (P i) c
  have hcut (i : ι) := curvatureCut_bounds (P i) (hP i) hc hV (hcoeff i)
  have hQ (i : ι) : (Q i).totalDegree ≤ 2 := (hcut i).1
  have hD (i : ι) (p : Ω) (hp : p ∈ (⋃ j, H i j) ∪ (⋃ j, H j i)) :
      b₀ ≤ eval (fun k => z i p k) (disc (Q i)) :=
    hb₀floor.trans (curvatureCut_disc_floor (P i) (hP i) _ _ hc hB
      (hpoint i p hp).2.2.1 (hpoint i p hp).2.1 hraw)
  have hanchor (i : ι) (hi : ((⋃ j, H i j) ∪ (⋃ j, H j i)).Nonempty) :
      b₀ ≤ coefficientSize (disc (Q i)) := by
    obtain ⟨p, hp⟩ := hi
    exact (hD i p hp).trans ((le_abs_self _).trans
      (abs_eval_le_coefficientSize _ (fun k => z i p k) (fun k =>
        (PiLp.norm_apply_le (z i p) k).trans (by linarith [(hpoint i p hp).1]))))
  obtain ⟨t, H', ht, hdisccoef, hH', hfloor, hloss⟩ :=
    hdelete μ H Q z β b₀ η θ hH hdisj hQ hz hβ hanchor
      (fun i p hp => (hpoint i p hp).1)
      (fun i p hp => hb₀.le.trans (hD i p hp)) hsource hwitness
      hb₀ hη.le hθ hθ1 hsmall
  let R (i : ι) := MvPolynomial.C (t i) * Q i
  have hR (i : ι) : (R i).totalDegree ≤ 2 :=
    (totalDegree_C_mul_le _ _).trans (hQ i)
  have htests (i : ι) (y : Fin 4 → ℝ) (hv : |eval y (P i)| ≤ ρ)
      (hd : |eval y (pderiv (3 : Fin 4) (P i))| ≤ U) :
      |eval y (R i)| ≤ max ρ (U / c) ∧
      |eval y (pderiv (3 : Fin 4) (R i))| ≤ max U 1 ∧
      2 * |curvature (R i) (3 : Fin 4) * eval y (R i)| ≤ 2 * c * ρ := by
    obtain ⟨hv', hd', hcross'⟩ := (hcut i).2.2.2 y ρ U hρ hU hv hd
    refine ⟨(abs_eval_C_mul_le _ (ht i).1.le (ht i).2 y).trans hv', ?_, ?_⟩
    · dsimp [R]
      rw [pderiv_C_mul]
      exact (abs_eval_C_mul_le _ (ht i).1.le (ht i).2 y).trans hd'
    · exact curvature_value_ceiling_C_mul _ (ht i).1.le (ht i).2 y hcross'
  refine ⟨R, H', ?_, htests, hH', ?_, hloss⟩
  · intro i
    refine ⟨hR i, ?_, ?_, disc_totalDegree_le _ (hR i), hdisccoef i⟩
    · dsimp [R]
      rw [curvature_C_mul, abs_mul, abs_of_nonneg (ht i).1.le]
      exact (mul_le_of_le_one_left (abs_nonneg _) (ht i).2).trans (hcut i).2.1
    · intro m
      exact (abs_coeff_C_mul_le _ (ht i).1.le (ht i).2 m).trans ((hcut i).2.2.1 m)
  · intro i j p hp
    have hpair : p ∈ H i j := (hH' i j).2 hp
    have hi : p ∈ (⋃ k, H i k) ∪ (⋃ k, H k i) :=
      Or.inl (mem_iUnion.mpr ⟨j, hpair⟩)
    have hj : p ∈ (⋃ k, H j k) ∪ (⋃ k, H k j) :=
      Or.inr (mem_iUnion.mpr ⟨i, hpair⟩)
    obtain ⟨hDi, hDj⟩ := hfloor i j p hp
    have hderivative (s : ι) (hs : p ∈ (⋃ k, H s k) ∪ (⋃ k, H k s))
        (hDs : η < eval (fun k => z s p k) (disc (R s))) :
        η / 2 ≤ (eval (Fin.snoc (fun k => z s p k) (w s p))
          (pderiv (3 : Fin 4) (R s))) ^ 2 := by
      have hcr := (htests s _ (hpoint s p hs).2.1 (hpoint s p hs).2.2.2).2.2
      have hdisc : η ≤ |(eval (Fin.snoc (fun k => z s p k) (w s p))
          (pderiv (3 : Fin 4) (R s))) ^ 2 -
          2 * curvature (R s) (3 : Fin 4) *
            eval (Fin.snoc (fun k => z s p k) (w s p)) (R s)| := by
        rw [← eval_real_disc_at (R s) (hR s)]
        exact hDs.le.trans (le_abs_self _)
      exact (low_curvature_derivative_floor hη hdisc (hcr.trans hcross)).2
    exact ⟨hDi, hDj, hderivative i hi hDi, hderivative j hj hDj⟩

end Submission.Obl.k4_paired_test_normalization
