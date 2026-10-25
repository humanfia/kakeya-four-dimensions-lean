-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/ChartVelocity.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Mathlib
import Submission.Obl.k4_polynomial_variation_tube.LineVariation
import Submission.Obl.k4_scalar_grid_parameter_preparation.PacketGradient
import Submission.Lib.K4CubicTests.PolynomialTaylor

/-!
# The velocity graph read off a chart test

A chart of the frozen path keeps every assigned trajectory inside the sublevel set
`|R(x l t)| ≤ κ δ` of its quadratic test for the whole time block.  Along a trajectory
`t ↦ R(x l t)` is a polynomial of degree at most two, so Markov's inequality on the block
bounds its derivative, which is the directional derivative of `R` along the lifted velocity
`(1, l₃, l₄, l₅)`.  On counted incidences, where `|∂₃ R| ≥ B/κ`, this solves for the hidden
velocity `l₅` as an affine function of the base velocity `(l₃, l₄)` with an explicit error.

This replaces, at every scale that the path covers, the multilinear-Kakeya construction of
the physical velocity graph in the paper (Proposition `a05:velocity-graph`).
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MvPolynomial

noncomputable section

/-- The point of trajectory `l` at time `t`, exactly as in the frozen statement. -/
def trajPoint (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : Fin 4 → ℝ :=
  ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]

/-- The lifted velocity `(1, l₃, l₄, l₅)` of trajectory `l`. -/
def liftedVelocity (l : ℕ × (Fin 6 → ℝ)) : Fin 4 → ℝ :=
  ![1, l.2 3, l.2 4, l.2 5]

/-- The base point of trajectory `l` at time zero, as a point of `EuclideanSpace`. -/
def trajBase (l : ℕ × (Fin 6 → ℝ)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![0, l.2 0, l.2 1, l.2 2]

/-- The lifted velocity as a point of `EuclideanSpace`. -/
def trajDir (l : ℕ × (Fin 6 → ℝ)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (liftedVelocity l)

lemma trajPoint_eq_line (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    (fun j => (trajBase l + t • trajDir l) j) = trajPoint l t := by
  funext j
  fin_cases j <;> simp [trajBase, trajDir, liftedVelocity, trajPoint]

/-- The directional derivative of a polynomial along the lifted velocity. -/
def liftedDerivative (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : ℝ :=
  ∑ i, MvPolynomial.eval (trajPoint l t) (pderiv i R) * liftedVelocity l i

/-- Along a trajectory, a polynomial has derivative equal to its directional derivative
along the lifted velocity. -/
theorem hasDerivAt_eval_trajPoint (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ))
    (t : ℝ) :
    HasDerivAt (fun s => MvPolynomial.eval (trajPoint l s) R) (liftedDerivative R l t) t := by
  have hz : ∀ i, HasDerivAt (fun s => trajPoint l s i) (liftedVelocity l i) t := by
    intro i
    fin_cases i
    · simpa [trajPoint, liftedVelocity] using hasDerivAt_id' t
    · simpa [trajPoint, liftedVelocity] using
        ((hasDerivAt_id t).mul_const (l.2 3)).const_add (l.2 0)
    · simpa [trajPoint, liftedVelocity] using
        ((hasDerivAt_id t).mul_const (l.2 4)).const_add (l.2 1)
    · simpa [trajPoint, liftedVelocity] using
        ((hasDerivAt_id t).mul_const (l.2 5)).const_add (l.2 2)
  exact Submission.Lib.K4CubicTests.hasDerivAt_eval_finite_polynomial_curve R
    (fun s => trajPoint l s) (liftedVelocity l) t hz

/-- The restriction of `R` to trajectory `l`, as a univariate polynomial. -/
def trajRestrict (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) : Polynomial ℝ :=
  Submission.Obl.k4_polynomial_variation_tube.lineRestrict R (trajBase l) (trajDir l)

lemma eval_trajRestrict (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    (trajRestrict R l).eval t = MvPolynomial.eval (trajPoint l t) R := by
  rw [trajRestrict, Submission.Obl.k4_polynomial_variation_tube.eval_lineRestrict,
    trajPoint_eq_line]

lemma natDegree_trajRestrict_le (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) :
    (trajRestrict R l).natDegree ≤ R.totalDegree :=
  Submission.Obl.k4_polynomial_variation_tube.natDegree_lineRestrict_le R _ _

lemma derivative_trajRestrict_eval (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ))
    (t : ℝ) : (trajRestrict R l).derivative.eval t = liftedDerivative R l t := by
  have h1 := (trajRestrict R l).hasDerivAt t
  have h2 := hasDerivAt_eval_trajPoint R l t
  have heq : (fun s => (trajRestrict R l).eval s) =
      fun s => MvPolynomial.eval (trajPoint l s) R := by
    funext s
    exact eval_trajRestrict R l s
  rw [heq] at h1
  exact h1.unique h2

/-- **Chart velocity graph.**  There is a universal constant `C` such that, whenever a
polynomial of total degree at most two is bounded by `M` along a trajectory on a time
interval of length `h`, its directional derivative along the lifted velocity is bounded by
`C M / h` on the whole interval. -/
theorem exists_chart_velocity_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (a h M : ℝ),
      R.totalDegree ≤ 2 → 0 < h → 0 ≤ M →
      (∀ t ∈ Set.Icc a (a + h), |MvPolynomial.eval (trajPoint l t) R| ≤ M) →
      ∀ t ∈ Set.Icc a (a + h), |liftedDerivative R l t| ≤ C * M / h := by
  obtain ⟨C, hC, hbound⟩ :=
    Submission.Obl.k4_scalar_grid_parameter_preparation.exists_polynomial_interval_derivative_bound 2
  refine ⟨C, hC, ?_⟩
  intro R l a h M hR hh hM hsmall t ht
  have hdeg : (trajRestrict R l).natDegree ≤ 2 := (natDegree_trajRestrict_le R l).trans hR
  have hsmall' : ∀ s ∈ Set.Icc a (a + h), |(trajRestrict R l).eval s| ≤ M := by
    intro s hs
    rw [eval_trajRestrict]
    exact hsmall s hs
  have := hbound (trajRestrict R l) a h M hdeg hh hM hsmall' t ht
  rwa [derivative_trajRestrict_eval] at this

/-- The base part `∂ₜR + ∂₁R l₃ + ∂₂R l₄` of the lifted directional derivative. -/
def baseDerivative (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : ℝ :=
  MvPolynomial.eval (trajPoint l t) (pderiv 0 R) +
    MvPolynomial.eval (trajPoint l t) (pderiv 1 R) * l.2 3 +
    MvPolynomial.eval (trajPoint l t) (pderiv 2 R) * l.2 4

lemma liftedDerivative_eq (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    liftedDerivative R l t =
      baseDerivative R l t + MvPolynomial.eval (trajPoint l t) (pderiv 3 R) * l.2 5 := by
  simp [liftedDerivative, baseDerivative, Fin.sum_univ_four, liftedVelocity]

/-- **Hidden velocity on counted incidences.**  If the lifted directional derivative is at
most `E` and the hidden derivative is at least `b > 0` in absolute value, then the hidden
velocity `l₅` is the graph value `-(∂ₜR + ∂₁R l₃ + ∂₂R l₄)/∂₃R` up to `E / b`. -/
theorem hidden_velocity_graph (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t E b : ℝ)
    (hb : 0 < b) (hE : |liftedDerivative R l t| ≤ E)
    (hder : b ≤ |MvPolynomial.eval (trajPoint l t) (pderiv 3 R)|) :
    |l.2 5 + baseDerivative R l t / MvPolynomial.eval (trajPoint l t) (pderiv 3 R)| ≤ E / b := by
  set D := MvPolynomial.eval (trajPoint l t) (pderiv 3 R) with hD
  have hDpos : 0 < |D| := lt_of_lt_of_le hb hder
  have hD0 : D ≠ 0 := abs_pos.mp hDpos
  have hkey : l.2 5 + baseDerivative R l t / D = liftedDerivative R l t / D := by
    rw [liftedDerivative_eq]
    field_simp
    ring
  rw [hkey, abs_div]
  calc |liftedDerivative R l t| / |D| ≤ E / |D| :=
        div_le_div_of_nonneg_right hE hDpos.le
    _ ≤ E / b := by
        have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
        exact div_le_div_of_nonneg_left hE0 hb hder

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
