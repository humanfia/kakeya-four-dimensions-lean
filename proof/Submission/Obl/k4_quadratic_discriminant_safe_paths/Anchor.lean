import Submission.Obl.k4_quadratic_discriminant_safe_paths.Measurability
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices
import Submission.Lib.K4PolynomialRemez

/-!
# Real anchors avoid small values of a quadratic

A real quadratic in three variables that is at least `m` at a source `z₀` of the
radius-`1/8` ball is at most `η` only on a small part of that ball. Average the
dilations `x ↦ z₀ + t (x - z₀)` over `t ∈ [1/2, 1]`: each scales volume by `t⁻³ ≥ 1`,
and by Tonelli the average is bounded by the one-dimensional Remez estimate
(lib's `polynomial_remez_unit`) on the lines through `z₀`, where the restriction is
at least `m` at the parameter `0`.
-/

namespace Submission.Obl.k4_quadratic_discriminant_safe_paths

open Set Metric MeasureTheory

/-- The restriction of a real polynomial to the real line through `a` and `y`. -/
noncomputable def realLinePolynomial (P : MvPolynomial (Fin 3) ℝ) (a y : RealSpace) :
    Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (y i - a i) * Polynomial.X) P

theorem realLinePolynomial_degree (P : MvPolynomial (Fin 3) ℝ) (a y : RealSpace)
    (hP : P.totalDegree ≤ 2) : (realLinePolynomial P a y).natDegree ≤ 2 := by
  apply (Submission.Obl.k4_quadratic_slope_volume.natDegree_eval₂_affine_le P _ ?_).trans hP
  intro i
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

theorem realLinePolynomial_eval (P : MvPolynomial (Fin 3) ℝ) (a y : RealSpace) (t : ℝ) :
    (realLinePolynomial P a y).eval t =
      MvPolynomial.eval (fun i => (a + t • (y - a)) i) P := by
  rw [realLinePolynomial,
    Submission.Obl.k4_quadratic_slope_volume.eval_polynomial_substitution]
  apply congrArg (fun g : Fin 3 → ℝ => MvPolynomial.eval g P)
  funext i
  simp [mul_comm]

theorem continuous_realEval (P : MvPolynomial (Fin 3) ℝ) :
    Continuous (fun x : RealSpace => MvPolynomial.eval (fun i => x i) P) :=
  (MvPolynomial.continuous_eval P).comp (by fun_prop)

/-- On a line through the source, where the restriction is at least `m`, the
`η`-sublevel set of the unit parameter interval has measure less than `θ`. -/
theorem volume_line_sublevel_lt (P : MvPolynomial (Fin 3) ℝ) (hP : P.totalDegree ≤ 2)
    (a y : RealSpace) {m η θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hη : 0 ≤ η)
    (hm : m ≤ |MvPolynomial.eval (fun i => a i) P|) (hηθ : 576 * η < m * θ ^ 2) :
    volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ |(realLinePolynomial P a y).eval t| ≤ η} <
      ENNReal.ofReal θ := by
  by_contra hcon
  push Not at hcon
  have h := Submission.Lib.K4PolynomialRemez.polynomial_remez_unit
    (realLinePolynomial P a y) 2 (realLinePolynomial_degree P a y hP)
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ |(realLinePolynomial P a y).eval t| ≤ η}
    hθ hθ1 hη (fun t ht => ht.1) hcon (fun t ht => ht.2) 0 ⟨le_rfl, zero_le_one⟩
  rw [realLinePolynomial_eval] at h
  simp only [zero_smul, add_zero] at h
  have hsq : (8 * (((2 : ℕ) : ℝ) + 1) / θ) ^ 2 * η * θ ^ 2 = 576 * η := by
    push_cast
    field_simp
    ring
  have h2 := mul_le_mul_of_nonneg_right (hm.trans h) (sq_nonneg θ)
  linarith

/-- The anchor sublevel estimate: a real quadratic that is at least `m` at a
source point of the radius-`1/8` ball is at most `η` on at most a `128 θ` part
of that ball, whenever `576 η < m θ²`. -/
theorem volume_anchor_sublevel_le (P : MvPolynomial (Fin 3) ℝ) (hP : P.totalDegree ≤ 2)
    (z₀ : RealSpace) (hz₀ : ‖z₀‖ ≤ 1 / 8) {m η θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hη : 0 ≤ η) (hm : m ≤ |MvPolynomial.eval (fun i => z₀ i) P|)
    (hηθ : 576 * η < m * θ ^ 2) :
    volume {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
        |MvPolynomial.eval (fun i => x i) P| ≤ η} ≤
      ENNReal.ofReal (128 * θ) * volume (closedBall (0 : RealSpace) (1 / 8)) := by
  set S := {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
        |MvPolynomial.eval (fun i => x i) P| ≤ η} with hS
  have hSc : IsClosed S := isClosed_closedBall.inter
    (isClosed_le (continuous_abs.comp (continuous_realEval P)) continuous_const)
  set B' : Set RealSpace := closedBall z₀ (1 / 2) with hB'
  let G : RealSpace × ℝ → RealSpace := fun p => z₀ + p.2 • (p.1 - z₀)
  have hG : Continuous G := by fun_prop
  set F : Set (RealSpace × ℝ) :=
    {p | p.1 ∈ B' ∧ p.2 ∈ Icc (1 / 2 : ℝ) 1 ∧ G p ∈ S} with hF
  have hFm : MeasurableSet F :=
    ((isClosed_closedBall.preimage continuous_fst).inter
      ((isClosed_Icc.preimage continuous_snd).inter (hSc.preimage hG))).measurableSet
  have hupper : (volume.prod volume) F ≤ ENNReal.ofReal θ * volume B' := by
    rw [Measure.prod_apply hFm]
    calc
      ∫⁻ y, volume (Prod.mk y ⁻¹' F) ≤
          ∫⁻ y, B'.indicator (fun _ => ENNReal.ofReal θ) y := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ B'
        · rw [indicator_of_mem hy]
          refine le_trans (measure_mono ?_)
            (volume_line_sublevel_lt P hP z₀ y hθ hθ1 hη hm hηθ).le
          intro t ht
          refine ⟨⟨by linarith [ht.2.1.1], ht.2.1.2⟩, ?_⟩
          rw [realLinePolynomial_eval]
          exact ht.2.2.2
        · rw [indicator_of_notMem hy]
          have hempty : Prod.mk y ⁻¹' F = ∅ := by
            ext t
            simp only [mem_preimage, mem_empty_iff_false, iff_false]
            exact fun ht => hy ht.1
          simp [hempty]
      _ = ENNReal.ofReal θ * volume B' :=
        lintegral_indicator_const measurableSet_closedBall _
  have hslice : ∀ t ∈ Icc (1 / 2 : ℝ) 1,
      volume S ≤ volume ((fun x => (x, t)) ⁻¹' F) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hsub : (fun y : RealSpace => t • y) ⁻¹'
        ((fun u => u + (1 - t) • z₀) ⁻¹' S) ⊆ (fun x => (x, t)) ⁻¹' F := by
      intro y hy
      simp only [mem_preimage] at hy
      have hGy : G (y, t) = t • y + (1 - t) • z₀ := by
        simp only [G]
        module
      have hyS : G (y, t) ∈ S := by rw [hGy]; exact hy
      refine ⟨?_, ht, hyS⟩
      have hnorm : ‖G (y, t)‖ ≤ 1 / 8 := mem_closedBall_zero_iff.mp hyS.1
      have hsm : ‖t • (y - z₀)‖ ≤ 1 / 4 := by
        have : t • (y - z₀) = G (y, t) - z₀ := by simp only [G]; abel
        rw [this]
        exact (norm_sub_le _ _).trans (by linarith)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hsm
      rw [hB', mem_closedBall, dist_eq_norm]
      nlinarith [ht.1, norm_nonneg (y - z₀)]
    calc
      volume S = volume ((fun u => u + (1 - t) • z₀) ⁻¹' S) :=
        (measure_preimage_add_right volume _ S).symm
      _ ≤ ENNReal.ofReal |(t ^ Module.finrank ℝ RealSpace)⁻¹| *
          volume ((fun u => u + (1 - t) • z₀) ⁻¹' S) := by
        apply le_mul_of_one_le_left (by positivity)
        rw [finrank_euclideanSpace_fin]
        apply ENNReal.one_le_ofReal.mpr
        rw [abs_of_pos (by positivity)]
        exact one_le_inv₀ (by positivity) |>.mpr (pow_le_one₀ ht0.le ht.2)
      _ = volume ((fun y : RealSpace => t • y) ⁻¹'
          ((fun u => u + (1 - t) • z₀) ⁻¹' S)) :=
        (Measure.addHaar_preimage_smul volume ht0.ne' _).symm
      _ ≤ volume ((fun x => (x, t)) ⁻¹' F) := measure_mono hsub
  have hlower : volume S * ENNReal.ofReal (1 / 2) ≤ (volume.prod volume) F := by
    rw [Measure.prod_apply_symm hFm]
    calc
      volume S * ENNReal.ofReal (1 / 2) = ∫⁻ _t in Icc (1 / 2 : ℝ) 1, volume S := by
        rw [setLIntegral_const, Real.volume_Icc]
        norm_num
      _ ≤ ∫⁻ t in Icc (1 / 2 : ℝ) 1, volume ((fun x => (x, t)) ⁻¹' F) :=
        setLIntegral_mono' measurableSet_Icc hslice
      _ ≤ ∫⁻ t, volume ((fun x => (x, t)) ⁻¹' F) := setLIntegral_le_lintegral _ _
  have hball : volume B' = ENNReal.ofReal 64 * volume (closedBall (0 : RealSpace) (1 / 8)) := by
    rw [hB', Measure.addHaar_closedBall volume z₀ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      Measure.addHaar_closedBall volume (0 : RealSpace) (by norm_num : (0 : ℝ) ≤ 1 / 8),
      finrank_euclideanSpace_fin, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hhalf : ENNReal.ofReal (1 / 2) * ENNReal.ofReal 2 = 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc
    volume S = volume S * ENNReal.ofReal (1 / 2) * ENNReal.ofReal 2 := by
      rw [mul_assoc, hhalf, mul_one]
    _ ≤ ENNReal.ofReal θ * volume B' * ENNReal.ofReal 2 := by
      exact mul_le_mul_left (hlower.trans hupper) _
    _ = ENNReal.ofReal (128 * θ) * volume (closedBall (0 : RealSpace) (1 / 8)) := by
      rw [hball, show (128 * θ) = 2 * 64 * θ by ring,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
      ring

end Submission.Obl.k4_quadratic_discriminant_safe_paths
