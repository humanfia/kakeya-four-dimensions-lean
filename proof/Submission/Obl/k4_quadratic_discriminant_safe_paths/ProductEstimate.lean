import Submission.Obl.k4_quadratic_discriminant_safe_paths.Measurability

namespace Submission.Obl.k4_quadratic_discriminant_safe_paths

open Set Metric MeasureTheory

def anchorBad (P P' : MvPolynomial (Fin 3) ℝ) (κ : ℝ) : Set RealSpace :=
  {x | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
    (|MvPolynomial.eval (fun i => x i) P| < κ ∨
      |MvPolynomial.eval (fun i => x i) P'| < κ)}

theorem measurableSet_anchorBad (P P' : MvPolynomial (Fin 3) ℝ) (κ : ℝ) :
    MeasurableSet (anchorBad P P' κ) := by
  have hP : Continuous (fun x : RealSpace => |MvPolynomial.eval (fun i => x i) P|) := by
    exact (P.continuous_eval.comp (by fun_prop)).abs
  have hP' : Continuous (fun x : RealSpace => |MvPolynomial.eval (fun i => x i) P'|) := by
    exact (P'.continuous_eval.comp (by fun_prop)).abs
  exact isClosed_closedBall.measurableSet.inter
    ((isOpen_lt hP continuous_const).union (isOpen_lt hP' continuous_const)).measurableSet

theorem anchorBad_volume_le_of_single (P P' : MvPolynomial (Fin 3) ℝ)
    (κ η : ℝ) (hη : 0 ≤ η)
    (hP : volume {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
      |MvPolynomial.eval (fun i => x i) P| < κ} ≤
      ENNReal.ofReal (η / 4) * volume (closedBall (0 : RealSpace) (1 / 8)))
    (hP' : volume {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
      |MvPolynomial.eval (fun i => x i) P'| < κ} ≤
      ENNReal.ofReal (η / 4) * volume (closedBall (0 : RealSpace) (1 / 8))) :
    volume (anchorBad P P' κ) ≤
      ENNReal.ofReal (η / 2) * volume (closedBall (0 : RealSpace) (1 / 8)) := by
  have heq : anchorBad P P' κ =
      {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
        |MvPolynomial.eval (fun i => x i) P| < κ} ∪
      {x : RealSpace | x ∈ closedBall (0 : RealSpace) (1 / 8) ∧
        |MvPolynomial.eval (fun i => x i) P'| < κ} := by
    ext x
    exact and_or_left
  rw [heq]
  apply (measure_union_le _ _).trans
  apply (add_le_add hP hP').trans_eq
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 2
  ring

/-- Integrate the good-anchor estimate against the original volume measure. -/
theorem product_badSet_le (a : RealSpace) (P P' : MvPolynomial (Fin 3) ℝ)
    (r κ b : ℝ)
    (hfiber : ∀ x ∈ closedBall (0 : RealSpace) (1 / 8),
      x ∉ anchorBad P P' κ →
      volume (Prod.mk x ⁻¹' badSet a P P' r) ≤ ENNReal.ofReal b) :
    (volume.prod volume) (badSet a P P' r) ≤
      volume (closedBall (1 / 2 : ℂ) (1 / 4)) * volume (anchorBad P P' κ) +
      ENNReal.ofReal b * volume (closedBall (0 : RealSpace) (1 / 8)) := by
  let B : Set RealSpace := closedBall 0 (1 / 8)
  let D : Set ℂ := closedBall (1 / 2) (1 / 4)
  have hB : MeasurableSet B := isClosed_closedBall.measurableSet
  have hE := measurableSet_anchorBad P P' κ
  have hpoint (x : RealSpace) : volume (Prod.mk x ⁻¹' badSet a P P' r) ≤
      (anchorBad P P' κ).indicator (fun _ => volume D) x +
        B.indicator (fun _ => ENNReal.ofReal b) x := by
    have hD : volume (Prod.mk x ⁻¹' badSet a P P' r) ≤ volume D :=
      measure_mono (fun τ hτ => hτ.2.1)
    by_cases hx : x ∈ B
    · by_cases hbad : x ∈ anchorBad P P' κ
      · rw [indicator_of_mem hbad, indicator_of_mem hx]
        exact hD.trans (le_add_right le_rfl)
      · rw [indicator_of_notMem hbad, indicator_of_mem hx, zero_add]
        exact hfiber x hx hbad
    · have hempty : Prod.mk x ⁻¹' badSet a P P' r = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro τ hτ
        exact hx hτ.1
      rw [hempty, measure_empty]
      exact bot_le
  calc
    _ = ∫⁻ x, volume (Prod.mk x ⁻¹' badSet a P P' r) :=
      Measure.prod_apply (measurableSet_badSet a P P' r)
    _ ≤ ∫⁻ x, (anchorBad P P' κ).indicator (fun _ => volume D) x +
        B.indicator (fun _ => ENNReal.ofReal b) x := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left (measurable_const.indicator hE),
        lintegral_indicator hE, lintegral_indicator hB]
      simp only [lintegral_const, Measure.restrict_apply_univ]
      rfl

theorem product_badSet_le_relative (a : RealSpace) (P P' : MvPolynomial (Fin 3) ℝ)
    (r κ b η : ℝ) (hη : 0 ≤ η)
    (hfiber : ∀ x ∈ closedBall (0 : RealSpace) (1 / 8),
      x ∉ anchorBad P P' κ →
      volume (Prod.mk x ⁻¹' badSet a P P' r) ≤ ENNReal.ofReal b)
    (hanchor : volume (anchorBad P P' κ) ≤
      ENNReal.ofReal (η / 2) * volume (closedBall (0 : RealSpace) (1 / 8)))
    (hdetour : ENNReal.ofReal b ≤ ENNReal.ofReal (η / 2) *
      volume (closedBall (1 / 2 : ℂ) (1 / 4))) :
    (volume.prod volume) (badSet a P P' r) ≤
      ENNReal.ofReal η * (volume.prod volume)
        (closedBall (0 : RealSpace) (1 / 8) ×ˢ closedBall (1 / 2 : ℂ) (1 / 4)) := by
  have hsplit : ENNReal.ofReal η =
      ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc
    _ ≤ volume (closedBall (1 / 2 : ℂ) (1 / 4)) * volume (anchorBad P P' κ) +
        ENNReal.ofReal b * volume (closedBall (0 : RealSpace) (1 / 8)) :=
      product_badSet_le a P P' r κ b hfiber
    _ ≤ volume (closedBall (1 / 2 : ℂ) (1 / 4)) *
          (ENNReal.ofReal (η / 2) * volume (closedBall (0 : RealSpace) (1 / 8))) +
        (ENNReal.ofReal (η / 2) * volume (closedBall (1 / 2 : ℂ) (1 / 4))) *
          volume (closedBall (0 : RealSpace) (1 / 8)) := by
      gcongr
    _ = _ := by
      rw [Measure.prod_prod, hsplit]
      ring

end Submission.Obl.k4_quadratic_discriminant_safe_paths
