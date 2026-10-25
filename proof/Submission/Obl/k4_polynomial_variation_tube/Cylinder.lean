import Submission.Obl.k4_polynomial_variation_tube.Coordinates
import Submission.Obl.k4_polynomial_variation_tube.Overlap

open MeasureTheory Set

namespace Submission.Obl.k4_polynomial_variation_tube

open scoped Classical

lemma coordinate_near_axis {n : ℕ}
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (a u : EuclideanSpace ℝ (Fin (n+1))) (t s : ℝ) (y : Fin n → ℝ)
    (hRe : R (WithLp.toLp 2 (Fin.cons 1 (fun _ : Fin n => 0))) = u)
    (hd : dist (a + R (WithLp.toLp 2 (Fin.cons t y))) (a + s • u) < 4) :
    y ∈ transverseBox n := by
  have heq : a + s • u = a + R (WithLp.toLp 2 (Fin.cons s (fun _ : Fin n => 0))) := by
    rw [← hRe, ← R.map_smul]
    congr 2
    ext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  rw [heq, dist_add_left, R.dist_map, dist_eq_norm] at hd
  constructor <;> intro j
  all_goals
    have hcoord := PiLp.norm_apply_le
      ((WithLp.toLp 2 (Fin.cons t y) : EuclideanSpace ℝ (Fin (n+1))) -
        WithLp.toLp 2 (Fin.cons s (fun _ : Fin n => (0 : ℝ)))) j.succ
    simp only [PiLp.sub_apply, Fin.cons_succ, sub_zero, Real.norm_eq_abs] at hcoord
    have hy := abs_le.mp (hcoord.trans hd.le)
    linarith [hy.1, hy.2]

lemma ball_preimage_subset_rectangle {n : ℕ}
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (a e c : EuclideanSpace ℝ (Fin (n+1))) (hR : R (axis n) = e)
    (hc : c ∈ Metric.thickening 3 (Set.range fun t : ℝ => a + t • e))
    {T : ℝ} (hcT : ‖c-a‖ + 1 ≤ T) :
    (lineCoordinates a R) ⁻¹' Metric.ball c 1 ⊆ Set.Icc (-T) T ×ˢ transverseBox n := by
  rintro ⟨t,y⟩ hx
  change lineCoordinates a R (t,y) ∈ Metric.ball c 1 at hx
  have hd : ‖lineCoordinates a R (t,y) - c‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hcoord : |t| ≤ ‖lineCoordinates a R (t,y) - a‖ := by
    have h := PiLp.norm_apply_le
      (WithLp.toLp 2 (Fin.cons t y) : EuclideanSpace ℝ (Fin (n+1))) 0
    simpa [lineCoordinates_apply] using h
  have htriangle : ‖lineCoordinates a R (t,y) - a‖ ≤
      ‖lineCoordinates a R (t,y) - c‖ + ‖c-a‖ := by
    simpa only [sub_add_sub_cancel] using
      norm_add_le (lineCoordinates a R (t,y) - c) (c-a)
  have ht : |t| ≤ T := by linarith
  refine ⟨abs_le.mp ht, ?_⟩
  obtain ⟨w, ⟨s,rfl⟩, hs⟩ := Metric.mem_thickening_iff.mp hc
  have hnear : dist (lineCoordinates a R (t,y)) (a + s • e) < 4 := by
    have htri := dist_triangle (lineCoordinates a R (t,y)) c (a+s • e)
    have hball := Metric.mem_ball.mp hx
    linarith
  exact coordinate_near_axis R a e t s y hR (by simpa only [lineCoordinates_apply] using hnear)

lemma sum_ball_indicator_le {n m N : ℕ} (c : Fin m → EuclideanSpace ℝ (Fin n))
    (hc : ∀ x, (Finset.univ.filter (fun q => x ∈ Metric.ball (c q) 1)).card ≤ N)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (s : Finset (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ q ∈ s, (Metric.ball (c q) 1).indicator f x) ≤ (N : ℝ) * f x := by
  calc
    (∑ q ∈ s, (Metric.ball (c q) 1).indicator f x)
        ≤ ∑ q : Fin m, (Metric.ball (c q) 1).indicator f x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun q _ _ => Set.indicator_nonneg (fun y _ => hf y) x)
    _ = ((Finset.univ.filter (fun q => x ∈ Metric.ball (c q) 1)).card : ℝ) * f x := by
      rw [← Finset.sum_boole, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      by_cases h : x ∈ Metric.ball (c q) 1 <;> simp [h]
    _ ≤ (N : ℝ) * f x := mul_le_mul_of_nonneg_right (by exact_mod_cast hc x) (hf x)

lemma exists_axis_isometry {n : ℕ} (e : EuclideanSpace ℝ (Fin (n+1))) (he : ‖e‖ = 1) :
    ∃ R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)),
      R (axis n) = e := by
  refine ⟨(ℝ ∙ (axis n - e))ᗮ.reflection, ?_⟩
  exact Submodule.reflection_sub ((norm_axis n).trans he.symm)

set_option maxHeartbeats 800000 in
/-- A uniform line-integral bound controls the sum over separated unit balls in a tube. -/
lemma exists_continuous_tube_bound (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℕ) (c : Fin m → EuclideanSpace ℝ (Fin (n+1))),
      (∀ q r, q ≠ r → 1 ≤ dist (c q) (c r)) →
      ∀ (a e : EuclideanSpace ℝ (Fin (n+1))), ‖e‖ = 1 →
      ∀ (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ), Continuous f → (∀ x, 0 ≤ f x) →
      ∀ B : ℝ,
      (∀ (b : EuclideanSpace ℝ (Fin (n+1))) (s t : ℝ), s ≤ t →
        (∫ u in Set.Icc s t, f (b + u • e)) ≤ B) →
      (∑ q : Fin m,
        (Metric.thickening 3 (Set.range fun t : ℝ => a + t • e)).indicator (fun _ => (1 : ℝ))
          (c q) * (∫ x in Metric.ball (c q) 1, f x)) ≤ C * B := by
  classical
  obtain ⟨N, hNpos, hN⟩ := exists_overlap_bound (n+1)
  refine ⟨(N : ℝ) * 8^n, by positivity, ?_⟩
  intro m c hc a e he f hf hnonneg B hline
  obtain ⟨R, hR⟩ := exists_axis_isometry e he
  let S : Finset (Fin m) := Finset.univ.filter
    (fun q => c q ∈ Metric.thickening 3 (Set.range fun t : ℝ => a + t • e))
  let T : ℝ := 2 + ∑ q : Fin m, ‖c q - a‖
  have hT : 0 < T := by
    change 0 < 2 + ∑ q : Fin m, ‖c q - a‖
    exact add_pos_of_pos_of_nonneg (by norm_num)
      (Finset.sum_nonneg (fun q _ => norm_nonneg (c q-a)))
  let K : Set (ℝ × (Fin n → ℝ)) := Set.Icc (-T) T ×ˢ transverseBox n
  let H : (ℝ × (Fin n → ℝ)) → ℝ :=
    fun u => ∑ q ∈ S, (Metric.ball (c q) 1).indicator f (lineCoordinates a R u)
  have hsupport : ∀ q ∈ S, (lineCoordinates a R) ⁻¹' Metric.ball (c q) 1 ⊆ K := by
    intro q hq
    apply ball_preimage_subset_rectangle R a e (c q) hR (Finset.mem_filter.mp hq).2
    have hsum := Finset.single_le_sum (fun r _ => norm_nonneg (c r-a)) (Finset.mem_univ q)
    change ‖c q-a‖ + 1 ≤ 2 + ∑ r : Fin m, ‖c r-a‖
    linarith
  have hint : IntegrableOn (fun u => f (lineCoordinates a R u)) K volume :=
    (hf.comp (continuous_lineCoordinates a R)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (show IsCompact (transverseBox n) from isCompact_Icc))
  have hintH : IntegrableOn H K volume := by
    apply integrable_finsetSum S
    intro q hq
    have hmeas : MeasurableSet ((lineCoordinates a R) ⁻¹' Metric.ball (c q) 1) :=
      Metric.isOpen_ball.measurableSet.preimage (lineCoordinates a R).measurable
    have hm := hint.indicator hmeas
    exact hm.congr (ae_of_all _ (fun u => by
      by_cases h : lineCoordinates a R u ∈ Metric.ball (c q) 1 <;> simp [h]))
  have hsupp : ∀ u ∉ K, H u = 0 := by
    intro u hu
    apply Finset.sum_eq_zero
    intro q hq
    have hnot : lineCoordinates a R u ∉ Metric.ball (c q) 1 := fun h => hu (hsupport q hq h)
    exact Set.indicator_of_notMem hnot f
  have hballs : ∀ q, IntegrableOn f (Metric.ball (c q) 1) volume := by
    intro q
    exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall (c q) 1)).mono_set
      Metric.ball_subset_closedBall
  have htotal : (∫ u, H u) = ∑ q ∈ S, ∫ x in Metric.ball (c q) 1, f x := by
    calc
      _ = ∫ x, ∑ q ∈ S, (Metric.ball (c q) 1).indicator f x :=
        (measurePreserving_lineCoordinates a R).integral_comp'
          (fun x => ∑ q ∈ S, (Metric.ball (c q) 1).indicator f x)
      _ = ∑ q ∈ S, ∫ x, (Metric.ball (c q) 1).indicator f x :=
        integral_finsetSum S
          (fun q _ => (hballs q).integrable_indicator Metric.isOpen_ball.measurableSet)
      _ = _ := by simp only [integral_indicator Metric.isOpen_ball.measurableSet]
  calc
    (∑ q : Fin m,
        (Metric.thickening 3 (Set.range fun t : ℝ => a + t • e)).indicator (fun _ => (1 : ℝ))
          (c q) * (∫ x in Metric.ball (c q) 1, f x))
        = ∑ q ∈ S, ∫ x in Metric.ball (c q) 1, f x := by
      simp only [S, Finset.sum_filter, Set.indicator_apply, ite_mul, one_mul, zero_mul]
    _ = ∫ u, H u := htotal.symm
    _ = ∫ u in K, H u := (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
    _ ≤ ∫ u in K, (N : ℝ) * f (lineCoordinates a R u) :=
      integral_mono hintH (hint.const_mul _) (fun u => sum_ball_indicator_le c (hN m c hc)
        f hnonneg S (lineCoordinates a R u))
    _ = (N : ℝ) * (∫ u in K, f (lineCoordinates a R u)) := integral_const_mul _ _
    _ ≤ (N : ℝ) * (8^n * B) := mul_le_mul_of_nonneg_left
      (rectangle_integral_le a R e hR f hf B hline (-T) T (by linarith)) (Nat.cast_nonneg _)
    _ = ((N : ℝ) * 8^n) * B := (mul_assoc _ _ _).symm

end Submission.Obl.k4_polynomial_variation_tube
