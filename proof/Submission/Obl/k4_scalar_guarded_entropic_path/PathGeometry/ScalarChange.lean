/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/ScalarChange.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ScalarComposition

/-! Canonical original coordinates for any finite chain of scalar normalizations. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MvPolynomial

/-- A scalar change of coordinates on the entire trajectory space. -/
structure ScalarChange where
  start : ℝ
  duration : ℝ
  center : ℝ
  speed : ℝ
  width : ℝ
  scale : ℝ
  polynomial : MvPolynomial (Fin 2) ℝ
  duration_pos : 0 < duration
  width_pos : 0 < width
  scale_pos : 0 < scale
  polynomial_degree : polynomial.totalDegree ≤ 2

namespace ScalarChange

noncomputable section

def trajectory (a : ScalarChange) : (ℕ × ScalarCoeff) ≃ᵐ (ℕ × ScalarCoeff) :=
  scalarTrajectoryEquiv a.polynomial a.polynomial_degree a.start a.duration a.center a.speed
    a.width a.scale a.duration_pos.ne' a.width_pos.ne' a.scale_pos.ne'

def incidence (a : ScalarChange) :
    ((ℕ × ScalarCoeff) × ℝ) ≃ᵐ ((ℕ × ScalarCoeff) × ℝ) :=
  scalarIncidenceEquiv a.polynomial a.polynomial_degree a.start a.duration a.center a.speed
    a.width a.scale a.duration_pos.ne' a.width_pos.ne' a.scale_pos.ne'

def refl : ScalarChange where
  start := 0
  duration := 1
  center := 0
  speed := 0
  width := 1
  scale := 1
  polynomial := 0
  duration_pos := zero_lt_one
  width_pos := zero_lt_one
  scale_pos := zero_lt_one
  polynomial_degree := by simp

theorem trajectory_refl : refl.trajectory = MeasurableEquiv.refl _ := by
  apply MeasurableEquiv.ext
  funext l
  apply Prod.ext
  · rfl
  · change normalizeScalarCoeff 0 0 1 0 0 1 1 l.2 = l.2
    funext e
    fin_cases e <;> simp [normalizeScalarCoeff, normalizedSignal, scalarX] <;> ring

theorem incidence_refl : refl.incidence = MeasurableEquiv.refl _ := by
  apply MeasurableEquiv.ext
  funext z
  apply Prod.ext
  · exact congrArg (fun e : (ℕ × ScalarCoeff) ≃ᵐ (ℕ × ScalarCoeff) => e z.1) trajectory_refl
  · change (z.2 - 0) / 1 = z.2
    simp

/-- Parent coordinates followed by child coordinates, with all parameters
expressed in the original frame. -/
def comp (a b : ScalarChange) : ScalarChange where
  start := a.start + a.duration * b.start
  duration := a.duration * b.duration
  center := a.center + a.width * b.center - a.width * b.speed * a.start / a.duration
  speed := a.speed + a.width * b.speed / a.duration
  width := a.width * b.width
  scale := a.scale * b.scale
  polynomial := liftScalarPolynomial a.polynomial b.polynomial
    a.start a.duration a.center a.speed a.width a.scale
  duration_pos := mul_pos a.duration_pos b.duration_pos
  width_pos := mul_pos a.width_pos b.width_pos
  scale_pos := mul_pos a.scale_pos b.scale_pos
  polynomial_degree := liftScalarPolynomial_degree _ _ a.polynomial_degree b.polynomial_degree
    _ _ _ _ _ _

theorem trajectory_comp (a b : ScalarChange) :
    (a.comp b).trajectory = a.trajectory.trans b.trajectory :=
  (scalarTrajectoryEquiv_comp _ _ a.polynomial_degree b.polynomial_degree
    _ _ _ _ _ _ _ _ _ _ _ _ a.duration_pos.ne' b.duration_pos.ne'
    a.width_pos.ne' b.width_pos.ne' a.scale_pos.ne' b.scale_pos.ne').symm

theorem incidence_comp (a b : ScalarChange) :
    (a.comp b).incidence = a.incidence.trans b.incidence :=
  (scalarIncidenceEquiv_comp _ _ a.polynomial_degree b.polynomial_degree
    _ _ _ _ _ _ _ _ _ _ _ _ a.duration_pos.ne' b.duration_pos.ne'
    a.width_pos.ne' b.width_pos.ne' a.scale_pos.ne' b.scale_pos.ne').symm

theorem base_identity (a : ScalarChange) (l : ℕ × ScalarCoeff) (t : ℝ) :
    scalarY (a.trajectory l).2 ((t - a.start) / a.duration) =
      (scalarY l.2 t - a.center - t * a.speed) / a.width := by
  change scalarY (normalizeScalarCoeff _ _ _ _ _ _ _ l.2) _ = _
  rw [scalarY_normalize]
  have ht : a.start + a.duration * ((t - a.start) / a.duration) = t := by
    field_simp [a.duration_pos.ne']
    ring
  rw [ht]

theorem hidden_identity (a : ScalarChange) (l : ℕ × ScalarCoeff) (t : ℝ) :
    scalarX (a.trajectory l).2 ((t - a.start) / a.duration) =
      (scalarX l.2 t - eval ![t, scalarY l.2 t] a.polynomial) / a.scale := by
  change scalarX (normalizeScalarCoeff _ _ _ _ _ _ _ l.2) _ = _
  rw [scalarX_normalize _ a.polynomial_degree]
  unfold normalizedSignal
  have ht : a.start + a.duration * ((t - a.start) / a.duration) = t := by
    field_simp [a.duration_pos.ne']
    ring
  rw [ht]

/-- Undo a candidate polynomial in these actual original coordinates. -/
def liftPolynomial (a : ScalarChange) (Q : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  liftScalarPolynomial a.polynomial Q a.start a.duration a.center a.speed a.width a.scale

theorem liftPolynomial_degree (a : ScalarChange) (Q : MvPolynomial (Fin 2) ℝ)
    (hQ : Q.totalDegree ≤ 2) : (a.liftPolynomial Q).totalDegree ≤ 2 :=
  liftScalarPolynomial_degree _ _ a.polynomial_degree hQ _ _ _ _ _ _

/-- The residual identity holds for every trajectory and every time,
before imposing any later incidence mask. -/
theorem residual_lift (a : ScalarChange) (Q : MvPolynomial (Fin 2) ℝ)
    (l : ℕ × ScalarCoeff) (t : ℝ) :
    scalarX l.2 t - eval ![t, scalarY l.2 t] (a.liftPolynomial Q) =
      a.scale * (scalarX (a.trajectory l).2 ((t - a.start) / a.duration) -
        eval ![(t - a.start) / a.duration,
          scalarY (a.trajectory l).2 ((t - a.start) / a.duration)] Q) := by
  rw [a.hidden_identity, a.base_identity]
  unfold liftPolynomial
  rw [eval_liftScalarPolynomial]
  field_simp [a.scale_pos.ne']
  ring

theorem abs_residual_lift (a : ScalarChange) (Q : MvPolynomial (Fin 2) ℝ)
    (l : ℕ × ScalarCoeff) (t : ℝ) :
    |scalarX l.2 t - eval ![t, scalarY l.2 t] (a.liftPolynomial Q)| =
      a.scale * |scalarX (a.trajectory l).2 ((t - a.start) / a.duration) -
        eval ![(t - a.start) / a.duration,
          scalarY (a.trajectory l).2 ((t - a.start) / a.duration)] Q| := by
  rw [a.residual_lift, abs_mul, abs_of_pos a.scale_pos]

end

end ScalarChange

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
