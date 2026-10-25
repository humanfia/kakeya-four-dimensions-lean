import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.RealJets

/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/HolomorphicBounds.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison

open Set Metric

lemma norm_affine_line_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a v : E) (w t : ℂ) :
    ‖a + w • v‖ ≤ ‖a + t • v‖ + ‖w - t‖ * ‖v‖ := by
  have he : a + w • v = (a + t • v) + (w - t) • v := by module
  rw [he]
  simpa only [norm_smul] using norm_add_le (a + t • v) ((w - t) • v)

/-- Directional real jets on an inner ball satisfy the same Cauchy estimates. -/
theorem directional_real_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : DifferentiableOn ℂ f (ball 0 4)) {C : ℝ}
    (hbound : ∀ z : E, ‖z‖ ≤ 2 → ‖f z‖ ≤ C)
    (a v : E) (hv : ‖v‖ ≤ 1) (t : ℝ) {R : ℝ} (hR : 0 < R)
    (hin : ‖a + (t : ℂ) • v‖ + R ≤ 2)
    (n : ℕ) :
    |iteratedDeriv n (fun x : ℝ => (f (a + (x : ℂ) • v)).re) t| ≤
      (n.factorial : ℝ) * C / R ^ n := by
  apply abs_iteratedDeriv_real_le (g := fun w : ℂ => f (a + w • v)) (t := t) (R := R) ?_ hR ?_ n
  · have hlinear : Differentiable ℂ (fun w : ℂ => a + w • v) := by fun_prop
    apply hf.comp hlinear.differentiableOn
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    have ht := norm_affine_line_le a v w (t : ℂ)
    have hmul : ‖w - (t : ℂ)‖ * ‖v‖ ≤ ‖w - (t : ℂ)‖ := by
      exact mul_le_of_le_one_right (norm_nonneg _) hv
    linarith
  · intro w hw
    apply hbound
    have hw' : ‖w - (t : ℂ)‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hw
    have ht := norm_affine_line_le a v w (t : ℂ)
    rw [hw'] at ht
    have hmul : R * ‖v‖ ≤ R := mul_le_of_le_one_right hR.le hv
    linarith

/-- A uniform holomorphic bound gives a uniform Lipschitz estimate on an inner complex ball. -/
theorem holomorphic_inner_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : DifferentiableOn ℂ f (ball 0 4)) {C : ℝ}
    (hbound : ∀ z : E, ‖z‖ ≤ 2 → ‖f z‖ ≤ C)
    {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖f y - f x‖ ≤ 4 * C * ‖y - x‖ := by
  have hd (z : E) (hz : ‖z‖ ≤ 1) : ‖fderiv ℂ f z‖ ≤ 4 * C := by
    have hsub : ball z (1 / 2) ⊆ ball (0 : E) 4 := by
      intro w hw
      rw [mem_ball, dist_eq_norm] at hw
      rw [mem_ball, dist_zero_right]
      have he : w = (w - z) + z := by abel
      have ht := norm_add_le (w - z) z
      rw [← he] at ht
      linarith
    have hsmall : ∀ w ∈ ball z (1 / 2), ‖w‖ ≤ 2 := by
      intro w hw
      rw [mem_ball, dist_eq_norm] at hw
      have he : w = (w - z) + z := by abel
      have ht := norm_add_le (w - z) z
      rw [← he] at ht
      linarith
    have hmap : MapsTo f (ball z (1 / 2)) (closedBall (f z) (2 * C)) := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hbound w (hsmall w hw), hbound z (by linarith)])
    have hh := Complex.norm_fderiv_le_div_of_mapsTo_ball (hf.mono hsub) hmap
      (by norm_num : (0 : ℝ) < 1 / 2)
    convert hh using 1 <;> ring
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (s := closedBall (0 : E) 1) ?_ ?_ (convex_closedBall _ _) ?_ ?_
  · intro z hz
    apply (hf z ?_).differentiableAt
    · exact isOpen_ball.mem_nhds (by simpa only [mem_ball, dist_zero_right] using
        (show ‖z‖ < (4 : ℝ) by have := mem_closedBall_zero_iff.mp hz; linarith))
    · simpa only [mem_ball, dist_zero_right] using
        (show ‖z‖ < (4 : ℝ) by have := mem_closedBall_zero_iff.mp hz; linarith)
  · intro z hz
    exact hd z (mem_closedBall_zero_iff.mp hz)
  · exact mem_closedBall_zero_iff.mpr hx
  · exact mem_closedBall_zero_iff.mpr hy


/-- Schwarz estimates also give a Lipschitz bound on every smaller concentric ball. -/
theorem holomorphic_ball_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : DifferentiableOn ℂ f (ball 0 4)) {C : ℝ}
    (hbound : ∀ z : E, ‖z‖ ≤ 2 → ‖f z‖ ≤ C)
    {L r : ℝ} (hr : 0 < r) (hLr : L + r ≤ 2)
    {x y : E} (hx : ‖x‖ ≤ L) (hy : ‖y‖ ≤ L) :
    ‖f y - f x‖ ≤ (2 * C / r) * ‖y - x‖ := by
  have hL : L ≤ 2 := by linarith
  have hd (z : E) (hz : ‖z‖ ≤ L) : ‖fderiv ℂ f z‖ ≤ 2 * C / r := by
    have hsmall : ∀ w ∈ ball z r, ‖w‖ ≤ 2 := by
      intro w hw
      rw [mem_ball, dist_eq_norm] at hw
      have ht : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
      linarith
    have hsub : ball z r ⊆ ball (0 : E) 4 := by
      intro w hw
      rw [mem_ball, dist_zero_right]
      linarith [hsmall w hw]
    have hmap : MapsTo f (ball z r) (closedBall (f z) (2 * C)) := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hbound w (hsmall w hw), hbound z (hz.trans hL)])
    exact Complex.norm_fderiv_le_div_of_mapsTo_ball (hf.mono hsub) hmap hr
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (s := closedBall (0 : E) L) ?_ ?_ (convex_closedBall _ _)
    (mem_closedBall_zero_iff.mpr hx) (mem_closedBall_zero_iff.mpr hy)
  · intro z hz
    have hz' := mem_closedBall_zero_iff.mp hz
    have hz4 : z ∈ ball (0 : E) 4 := by rw [mem_ball, dist_zero_right]; linarith
    exact (hf z hz4).differentiableAt (isOpen_ball.mem_nhds hz4)
  · intro z hz
    exact hd z (mem_closedBall_zero_iff.mp hz)

/-- The real restriction along every unit-sized complex direction is smooth. -/
theorem contDiffOn_real_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : DifferentiableOn ℂ f (ball 0 4))
    (a v : E) (ha : ‖a‖ ≤ (3 : ℝ) / 4) (hv : ‖v‖ ≤ 1) (m : WithTop ℕ∞) :
    ContDiffOn ℝ m (fun t : ℝ => (f (a + (t : ℂ) • v)).re) (Ioo (-1 : ℝ) 1) := by
  have hlinear : Differentiable ℂ (fun t : ℂ => a + t • v) := by fun_prop
  have hd : DifferentiableOn ℂ (fun t : ℂ => f (a + t • v)) (ball 0 3) := by
    apply hf.comp hlinear.differentiableOn
    intro t ht
    rw [mem_ball, dist_zero_right] at ht ⊢
    calc
      _ ≤ ‖a‖ + ‖t‖ * ‖v‖ := by simpa only [norm_smul] using norm_add_le a (t • v)
      _ ≤ 3 / 4 + ‖t‖ := add_le_add ha (mul_le_of_le_one_right (norm_nonneg _) hv)
      _ < 4 := by linarith
  apply contDiffOn_real_restriction isOpen_ball hd
  intro t ht
  rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  exact (abs_lt.mpr ht).trans (by norm_num : (1 : ℝ) < 3)

end Submission.Obl.k4_algebraic_real_jet_comparison
