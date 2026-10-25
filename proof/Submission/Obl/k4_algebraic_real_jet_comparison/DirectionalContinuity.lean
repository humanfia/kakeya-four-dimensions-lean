import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.HolomorphicBounds
import Submission.Obl.k4_algebraic_real_jet_comparison.RealGeometry

/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/DirectionalContinuity.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison

open Set Metric

/-- Directional real jets vary in a Lipschitz way with the complex base point.
This uses one-variable Cauchy estimates for the difference of two parallel slices. -/
theorem real_directional_jet_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : DifferentiableOn ℂ f (ball 0 4)) {C : ℝ}
    (hbound : ∀ z : E, ‖z‖ ≤ 2 → ‖f z‖ ≤ C)
    (v : E) (hv : ‖v‖ ≤ 1) (n : ℕ) {x y : E}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |iteratedDeriv n (fun t : ℝ => (f (x + (t : ℂ) • v)).re) 0 -
      iteratedDeriv n (fun t : ℝ => (f (y + (t : ℂ) • v)).re) 0| ≤
      ((n.factorial : ℝ) * (8 * C) / (1 / 8 : ℝ) ^ n) * ‖x - y‖ := by
  have hmaps (a : E) (ha : ‖a‖ ≤ (1 : ℝ)) :
      MapsTo (fun t : ℂ => a + t • v) (ball 0 (1 / 8 + 1)) (ball 0 4) := by
    intro t ht
    rw [mem_ball, dist_zero_right] at ht ⊢
    calc
      _ ≤ ‖a‖ + ‖t‖ * ‖v‖ := by simpa only [norm_smul] using norm_add_le a (t • v)
      _ ≤ 1 + ‖t‖ := by gcongr; exact mul_le_of_le_one_right (norm_nonneg _) hv
      _ < 4 := by linarith
  have hlinear (a : E) : Differentiable ℂ (fun t : ℂ => a + t • v) := by fun_prop
  have hdx := hf.comp (hlinear x).differentiableOn (hmaps x hx)
  have hdy := hf.comp (hlinear y).differentiableOn (hmaps y hy)
  have hsphere (a : E) (ha : ‖a‖ ≤ (1 : ℝ))
      (t : ℂ) (ht : t ∈ sphere (0 : ℂ) (1 / 8)) : ‖a + t • v‖ ≤ (3 : ℝ) / 2 := by
    have ht' : ‖t‖ = (1 : ℝ) / 8 := by simpa only [mem_sphere, dist_zero_right] using ht
    calc
      _ ≤ ‖a‖ + ‖t‖ * ‖v‖ := by simpa only [norm_smul] using norm_add_le a (t • v)
      _ ≤ 1 + 1 / 8 := by
        rw [ht']
        exact add_le_add ha (mul_le_of_le_one_right (by norm_num) hv)
      _ ≤ 3 / 2 := by norm_num
  have hh := abs_iteratedDeriv_real_le (hdx.sub hdy) (by norm_num : (0 : ℝ) < 1 / 8)
    (C := 8 * C * ‖x - y‖) (by
      intro t ht
      have h := holomorphic_ball_lipschitz hf hbound (L := 3 / 2) (r := 1 / 4)
        (by norm_num) (by norm_num) (x := y + t • v) (y := x + t • v)
        (hsphere y hy t ht) (hsphere x hx t ht)
      convert h using 1 <;> simp only [Function.comp_apply, Pi.sub_apply, add_sub_add_right_eq_sub] <;> ring) n
  have hxr : ContDiffAt ℝ n (fun t : ℝ => (f (x + (t : ℂ) • v)).re) 0 := by
    exact ((hdx.contDiffOn isOpen_ball).contDiffAt
      (isOpen_ball.mem_nhds (by simp; norm_num))).real_of_complex
  have hyr : ContDiffAt ℝ n (fun t : ℝ => (f (y + (t : ℂ) • v)).re) 0 := by
    exact ((hdy.contDiffOn isOpen_ball).contDiffAt
      (isOpen_ball.mem_nhds (by simp; norm_num))).real_of_complex
  change |iteratedDeriv n ((fun t : ℝ => (f (x + (t : ℂ) • v)).re) -
    (fun t : ℝ => (f (y + (t : ℂ) • v)).re)) 0| ≤ _ at hh
  rw [iteratedDeriv_sub hxr hyr] at hh
  convert hh using 1 <;> ring


/-- Continuity of directional jets uses no multivariate higher differentiability API. -/
theorem continuousOn_real_directional_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : DifferentiableOn ℂ f (ball 0 4)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z : E, ‖z‖ ≤ 2 → ‖f z‖ ≤ C)
    (v : E) (hv : ‖v‖ ≤ 1) (n : ℕ) :
    ContinuousOn (fun x : E => iteratedDeriv n (fun t : ℝ => (f (x + (t : ℂ) • v)).re) 0)
      (closedBall 0 1) := by
  let K : NNReal := ⟨(n.factorial : ℝ) * (8 * C) / (1 / 8 : ℝ) ^ n, by positivity⟩
  apply (LipschitzOnWith.of_dist_le_mul (K := K) ?_).continuousOn
  intro x hx y hy
  change dist (iteratedDeriv n (fun t : ℝ => (f (x + (t : ℂ) • v)).re) 0)
    (iteratedDeriv n (fun t : ℝ => (f (y + (t : ℂ) • v)).re) 0) ≤
    ((n.factorial : ℝ) * (8 * C) / (1 / 8 : ℝ) ^ n) * dist x y
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    real_directional_jet_lipschitz hf hbound v hv n
      (mem_closedBall_zero_iff.mp hx) (mem_closedBall_zero_iff.mp hy)

/-- Restrict the continuous jet field to the real base slice. -/
theorem continuousOn_real_slice_jet {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 4)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, ‖z‖ ≤ 2 → ‖f z‖ ≤ C)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ ≤ 1) (m : ℕ) :
    ContinuousOn (fun x : EuclideanSpace ℝ (Fin n) =>
      iteratedDeriv m (fun t : ℝ => (f (realEmbedding n x +
        (t : ℂ) • realEmbedding n v)).re) 0) (ball 0 1) := by
  apply (continuousOn_real_directional_jet hf hC hbound (realEmbedding n v)
    (by simpa only [LinearIsometry.norm_map] using hv) m).comp
    (realEmbedding n).continuous.continuousOn
  intro x hx
  rw [mem_closedBall, dist_zero_right, LinearIsometry.norm_map]
  exact (mem_ball_zero_iff.mp hx).le


/-- On finite-dimensional base space the required bound follows from compactness. -/
theorem continuousOn_real_slice_jet_of_holomorphic {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hf : DifferentiableOn ℂ f (ball 0 4))
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ ≤ 1) (m : ℕ) :
    ContinuousOn (fun x : EuclideanSpace ℝ (Fin n) =>
      iteratedDeriv m (fun t : ℝ => (f (realEmbedding n x +
        (t : ℂ) • realEmbedding n v)).re) 0) (ball 0 1) := by
  have hcf : ContinuousOn (fun z : EuclideanSpace ℂ (Fin n) => ‖f z‖) (closedBall 0 2) :=
    (hf.continuousOn.mono (closedBall_subset_ball (by norm_num))).norm
  obtain ⟨w, hw, hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) 2).exists_isMaxOn
    (by exact ⟨0, by simp⟩) hcf
  have hbound : ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ 2 → ‖f z‖ ≤ ‖f w‖ + 1 := by
    intro z hz
    exact (hmax (mem_closedBall_zero_iff.mpr hz)).trans (by linarith)
  exact continuousOn_real_slice_jet hf (by positivity) hbound v hv m

end Submission.Obl.k4_algebraic_real_jet_comparison
