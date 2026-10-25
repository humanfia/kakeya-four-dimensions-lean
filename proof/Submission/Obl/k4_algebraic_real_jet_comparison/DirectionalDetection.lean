import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.HolomorphicBounds
import Submission.Obl.k4_algebraic_real_jet_comparison.FiniteJets
import Submission.Obl.k4_algebraic_real_jet_comparison.RealGeometry

/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/DirectionalDetection.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison

open Set Metric

set_option maxHeartbeats 600000 in
/-- A finite list of unit real directions detects every normalized holomorphic comparison. -/
theorem exists_finite_directional_detection (C : ℝ) (hC : 0 < C) :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ c : ℝ, 0 < c ∧
      ∃ V : Finset (EuclideanSpace ℝ (Fin 3)),
        V.Nonempty ∧ (∀ v ∈ V, ‖v‖ = 1) ∧
        ∀ (f : EuclideanSpace ℂ (Fin 3) → ℂ),
          DifferentiableOn ℂ f (ball 0 4) →
          (∀ z, ‖z‖ ≤ 2 → ‖f z‖ ≤ C) →
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 →
            (f (realEmbedding 3 x)).im = 0) →
          (∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ (1 : ℝ) / 2 ∧
            1 ≤ ‖f (realEmbedding 3 y)‖) →
          ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1 : ℝ) / 2 →
          ∃ v ∈ V, ∃ j : ℕ, j < q ∧ c ≤
            |iteratedDeriv j (fun s : ℝ => (f (realEmbedding 3 x +
              (s : ℂ) • realEmbedding 3 v)).re) 0| := by
  classical
  let δ := min (1 / 4 : ℝ) (1 / (16 * C))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδsmall : δ ≤ (1 : ℝ) / 4 := min_le_left _ _
  have hδC : 4 * C * δ ≤ (1 : ℝ) / 4 := by
    have hh := min_le_right (1 / 4 : ℝ) (1 / (16 * C))
    have hden : 0 < 16 * C := by positivity
    have hh' : δ * (16 * C) ≤ 1 := (le_div_iff₀ hden).mp hh
    nlinarith
  obtain ⟨W, hWsub, hWfinite, hWcover⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).finite_cover_balls hδ
  let V := hWfinite.toFinset
  have hV (v) (hv : v ∈ V) : ‖v‖ = 1 := by
    have hh := hWsub (hWfinite.mem_toFinset.mp hv)
    simpa only [mem_sphere, dist_zero_right] using hh
  have hcover (w : EuclideanSpace ℝ (Fin 3)) (hw : ‖w‖ = 1) :
      ∃ v ∈ V, ‖v - w‖ < δ := by
    have hh := hWcover (by simpa only [mem_sphere, dist_zero_right] using hw)
    obtain ⟨v, hv, hdist⟩ := Set.mem_iUnion₂.mp hh
    refine ⟨v, hWfinite.mem_toFinset.mpr hv, ?_⟩
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hdist
  obtain ⟨q, hq, c, hc, hjet⟩ := exists_finite_real_jet C hC
  have hVne : V.Nonempty := by
    obtain ⟨t, w, ht, hw, he⟩ := exists_real_unit_displacement
      (0 : EuclideanSpace ℝ (Fin 3)) 0 (by simp) (by simp)
    obtain ⟨v, hv, hdist⟩ := hcover w hw
    exact ⟨v, hv⟩
  refine ⟨q, hq, c, hc, V, hVne, hV, ?_⟩
  intro f hf hbound hreal ⟨y, hy, hyf⟩ x hx
  obtain ⟨t, w, ht, hw, hxy⟩ := exists_real_unit_displacement x y hx hy
  obtain ⟨v, hv, hvw⟩ := hcover w hw
  have hvnorm : ‖v‖ = 1 := hV v hv
  let z := x + t • v
  have hclose : ‖z - y‖ ≤ δ := by
    have he : z - y = t • (v - w) := by rw [hxy]; dsimp [z]; module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left hvw.le ht.1).trans
      (mul_le_of_le_one_left hδ.le ht.2)
  have hz : ‖z‖ ≤ (3 : ℝ) / 4 := by
    have hh : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - y) y
    linarith
  have herror : ‖f (realEmbedding 3 z) - f (realEmbedding 3 y)‖ ≤ (1 : ℝ) / 4 := by
    have hh := holomorphic_inner_lipschitz hf hbound
      (x := realEmbedding 3 y) (y := realEmbedding 3 z)
      (by simpa only [LinearIsometry.norm_map] using (show ‖y‖ ≤ (1 : ℝ) by linarith))
      (by simpa only [LinearIsometry.norm_map] using (show ‖z‖ ≤ (1 : ℝ) by linarith))
    rw [← map_sub, LinearIsometry.norm_map] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hclose (by positivity)).trans hδC)
  have hzvalue : (1 : ℝ) / 2 ≤ ‖f (realEmbedding 3 z)‖ := by
    have hh : ‖f (realEmbedding 3 y)‖ ≤
        ‖f (realEmbedding 3 z)‖ + ‖f (realEmbedding 3 z) - f (realEmbedding 3 y)‖ := by
      calc
        _ = ‖f (realEmbedding 3 z) -
            (f (realEmbedding 3 z) - f (realEmbedding 3 y))‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  let g : ℝ → ℝ := fun s => (f (realEmbedding 3 x + (s : ℂ) • realEmbedding 3 v)).re
  have hgcomplex : DifferentiableOn ℂ
      (fun s : ℂ => f (realEmbedding 3 x + s • realEmbedding 3 v)) (ball 0 3) := by
    have hlinear : Differentiable ℂ
        (fun s : ℂ => realEmbedding 3 x + s • realEmbedding 3 v) := by fun_prop
    apply hf.comp hlinear.differentiableOn
    intro s hs
    rw [mem_ball, dist_zero_right] at hs ⊢
    calc
      _ ≤ ‖realEmbedding 3 x‖ + ‖s‖ * ‖realEmbedding 3 v‖ := by
        simpa only [norm_smul] using norm_add_le (realEmbedding 3 x) (s • realEmbedding 3 v)
      _ < 4 := by rw [LinearIsometry.norm_map, LinearIsometry.norm_map, hvnorm, mul_one]; linarith
  have hg : ContDiffOn ℝ q g (Ioo (-2 : ℝ) 2) := by
    apply contDiffOn_real_restriction isOpen_ball hgcomplex
    intro s hs
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_lt.mpr hs).trans (by norm_num : (2 : ℝ) < 3)
  have hgt : (1 : ℝ) / 2 ≤ |g t| := by
    have him := hreal z (by linarith)
    have he : f (realEmbedding 3 z) = ((f (realEmbedding 3 z)).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hnorm : ‖f (realEmbedding 3 z)‖ = |(f (realEmbedding 3 z)).re| := by
      calc
        _ = ‖((f (realEmbedding 3 z)).re : ℂ)‖ := congrArg norm he
        _ = _ := by simp
    rw [hnorm] at hzvalue
    simpa only [z, realEmbedding_line, g] using hzvalue
  have htop : ∀ s ∈ Icc (0 : ℝ) t,
      |iteratedDeriv q g s| ≤ (q.factorial : ℝ) * C * (4 / 5 : ℝ) ^ q := by
    intro s hs
    have hpos : ‖x + s • v‖ ≤ (3 : ℝ) / 4 :=
      norm_line_le_of_endpoints x v ht.1 hs (by linarith) hz
    have hin : ‖realEmbedding 3 x + (s : ℂ) • realEmbedding 3 v‖ + (5 : ℝ) / 4 ≤ 2 := by
      rw [← realEmbedding_line, LinearIsometry.norm_map]
      linarith
    have hh := directional_real_jet_bound hf hbound (realEmbedding 3 x) (realEmbedding 3 v)
      (by rw [LinearIsometry.norm_map, hvnorm]) s (by norm_num : (0 : ℝ) < 5 / 4) hin q
    convert hh using 1
    rw [div_eq_mul_inv ((q.factorial : ℝ) * C) ((5 / 4 : ℝ) ^ q), ← inv_pow]
    norm_num
  obtain ⟨j, hj, hjlarge⟩ := hjet g hg t ht hgt htop
  exact ⟨v, hv, j, hj, hjlarge⟩

end Submission.Obl.k4_algebraic_real_jet_comparison
