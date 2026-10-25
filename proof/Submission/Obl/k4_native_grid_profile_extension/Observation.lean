/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/Observation.lean. Earlier source attributions are retained below.
-/

/-
Adapted from this LOT tree, o006, session x0006, commit 551f63e,
Submission/Obl/k4_core/Framework/Observation.lean.
These are unaccepted same-tree helper proofs, audited for this obligation.
-/

import Mathlib

/-!
# Coordinate and observation maps for the terminal-chart interface

The coefficient convention matches x0079's `TerminalChartAssertion` on o018:
three intercepts followed by three slopes, with an unobserved natural index.
The coordinate convention is adapted from LOT session x0079, o018, commit e3a28eb,
Submission/Obl/k4_framework_from_matching_clustering_conic/TerminalInterface.lean.
The continuity and measurability proofs below are original Mathlib proofs.
-/

namespace Submission.Obl.k4_native_grid_profile_extension

abbrev Coefficients := ℕ × (Fin 6 → ℝ)
abbrev ObservationSpace := EuclideanSpace ℝ (Fin 3) × ℤ
abbrev AngularObservationSpace := ObservationSpace × (Fin 2 → ℤ)

def trajectoryPoint (l : Coefficients) (t : ℝ) : Fin 4 → ℝ :=
  ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]

def planarLine (l : Coefficients) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![trajectoryPoint l t 1, trajectoryPoint l t 2]

def planarVelocity (l : Coefficients) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![l.2 3, l.2 4]

def baseObservation (p : Coefficients × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![p.2, trajectoryPoint p.1 p.2 1, trajectoryPoint p.1 p.2 2]

noncomputable def pureObservation (B a : ℝ) (p : Coefficients × ℝ) : ObservationSpace :=
  (baseObservation p, ⌊B * trajectoryPoint p.1 p.2 3 / a⌋)

noncomputable def angularObservation (B a b : ℝ) (p : Coefficients × ℝ) :
    AngularObservationSpace :=
  (pureObservation B a p, fun j => ⌊planarVelocity p.1 j / b⌋)

theorem continuous_trajectoryPoint :
    Continuous (fun p : Coefficients × ℝ => trajectoryPoint p.1 p.2) := by
  unfold trajectoryPoint
  fun_prop

theorem continuous_planarLine :
    Continuous (fun p : Coefficients × ℝ => planarLine p.1 p.2) := by
  unfold planarLine trajectoryPoint
  fun_prop

theorem continuous_planarVelocity : Continuous planarVelocity := by
  unfold planarVelocity
  fun_prop

theorem continuous_baseObservation : Continuous baseObservation := by
  unfold baseObservation trajectoryPoint
  fun_prop

theorem continuous_signal (P : MvPolynomial (Fin 4) ℝ) :
    Continuous (fun p : Coefficients × ℝ => MvPolynomial.eval (trajectoryPoint p.1 p.2) P) :=
  (MvPolynomial.continuous_eval P).comp continuous_trajectoryPoint

theorem measurable_pureObservation (B a : ℝ) : Measurable (pureObservation B a) := by
  unfold pureObservation baseObservation trajectoryPoint
  fun_prop

theorem measurable_angularObservation (B a b : ℝ) :
    Measurable (angularObservation B a b) := by
  unfold angularObservation pureObservation baseObservation trajectoryPoint planarVelocity
  fun_prop

end Submission.Obl.k4_native_grid_profile_extension
