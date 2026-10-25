/-
Adapted from this LOT tree, o064, session x0214, commit 1213d02,
Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/Basic.lean.
Earlier provenance is preserved below.
-/
import Mathlib

/-!
# Basic objects of the version-2 terminal-chart assertion

Trajectories, graph points, dyadic time blocks, the Boolean sign format and
finite chart systems, laid out exactly as in the frozen conclusion of o064.

The definitions `graphPoint`, `planarPoint`, `timeBlock`, `PolynomialFormat`,
`ChartSystem` and `ChartSystem.Valid` are adapted from this tree's obligation
o049 (`k4_cap_class_terminal_charts`), branch x0147, file
`Submission/Obl/k4_cap_class_terminal_charts/Charts.lean` (that session's own
code), so that systems built here and there can be exchanged.
-/

namespace Submission.Obl.k4_local_remainder_horizon_transfer.Normalization

open MeasureTheory Set
open scoped BigOperators

/-- An indexed trajectory: an internal index and six real coefficients
`(b₁, b₂, b₃, s₁, s₂, s₃)`. -/
abbrev Trajectory := ℕ × (Fin 6 → ℝ)

/-- A trajectory--time incidence. -/
abbrev Incidence := Trajectory × ℝ

/-- The plane of the base coordinates. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The graph point `(t, b₁ + t s₁, b₂ + t s₂, b₃ + t s₃)` of a trajectory. -/
def graphPoint (l : Trajectory) (t : ℝ) : Fin 4 → ℝ :=
  ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]

/-- The base (planar) part of the graph point. -/
def planarPoint (l : Trajectory) (t : ℝ) : Plane :=
  WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4]

/-- The closed dyadic time block `[j / 2^T, (j + 1) / 2^T]`. -/
def timeBlock (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

/-- The Boolean sign format of the frozen statement: at most `N ^ M` polynomial
sign tests of degree at most `D`, combined by an arbitrary Boolean function. -/
def PolynomialFormat {n : ℕ} (N : ℝ) (M D : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ N ^ M ∧
    ∃ p : Fin m → MvPolynomial (Fin n) ℝ,
      (∀ i, (p i).totalDegree ≤ D) ∧ ∃ b : (Fin m → Bool) → Bool,
        ∀ x, x ∈ S ↔ b (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) = true

/-- All the finite geometric and assignment data of a chart system with a
common dyadic time partition of size `2 ^ T`. -/
structure ChartSystem (W T : ℕ) where
  count : ℕ
  world : Fin count → Fin W
  block : Fin count → Fin (2 ^ T)
  center : Fin count → Plane
  speed : Fin count → Plane
  frame : Fin count → Matrix (Fin 2) (Fin 2) ℝ
  test : Fin count → MvPolynomial (Fin 4) ℝ
  assignment : Fin count → Set Trajectory
  event : Fin count → Set Incidence

/-- Every condition of the frozen conclusion at one sample, for thickness `δ`,
slack `κ`, terminal density exponent `fL` and format bounds `M, D`. -/
def ChartSystem.Valid {W T : ℕ} (s : ChartSystem W T)
    (N κ fL δ : ℝ) (M D : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Trajectory) (E : Fin W → Set Incidence) (B : Fin W → ℝ) : Prop :=
  (s.count : ℝ) ≤ N ^ M ∧
  (∀ b b', b ≠ b' → s.world b = s.world b' → s.block b = s.block b' →
    Disjoint (s.assignment b) (s.assignment b')) ∧
  (∀ b,
    Matrix.det (s.frame b) ≠ 0 ∧
    ‖s.center b‖ + ‖s.speed b‖ ≤ N ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2,
      (|s.frame b e e'| + |(s.frame b)⁻¹ e e'|)) ≤ N ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame b e e'|) ≤ κ / (2 : ℝ) ^ T ∧
    (s.test b).totalDegree ≤ 2 ∧
    (∀ e, |(s.test b).coeff e| ≤ N ^ M) ∧
    MeasurableSet (s.assignment b) ∧ MeasurableSet (s.event b) ∧
    (∀ i,
      PolynomialFormat N M D {x | (i, x) ∈ s.assignment b} ∧
      PolynomialFormat N M D {x : Fin 7 → ℝ |
        ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ s.event b}) ∧
    (∀ l ∈ s.assignment b,
      (l.1 : ℝ) ≤ N ^ M ∧ (∀ e, |l.2 e| ≤ N ^ M) ∧
      ∀ t ∈ timeBlock T (s.block b),
        ‖Matrix.toEuclideanLin ((s.frame b)⁻¹)
          (planarPoint l t - s.center b - t • s.speed b)‖ ≤ κ ∧
        |MvPolynomial.eval (graphPoint l t) (s.test b)| ≤ κ * δ ∧
        |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4) (s.test b))| ≤
          κ * B (s.world b) ∧
        |MvPolynomial.eval (graphPoint l t)
          (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (s.test b)))| ≤
          κ * B (s.world b) ^ 2 / δ) ∧
    (∀ p ∈ s.event b,
      p ∈ E (s.world b) ∧ p.1 ∈ s.assignment b ∧ p.2 ∈ timeBlock T (s.block b) ∧
      B (s.world b) / κ ≤
        |MvPolynomial.eval (graphPoint p.1 p.2)
          (MvPolynomial.pderiv (3 : Fin 4) (s.test b))|) ∧
    ENNReal.ofReal (N ^ (-fL) * |Matrix.det (s.frame b)| / ((2 : ℝ) ^ T * κ)) ≤
      ((ν (s.world b)).prod volume) (s.event b)) ∧
  ENNReal.ofReal (κ⁻¹) ≤
    ∑ b, ENNReal.ofReal (ω (s.world b)) * ((ν (s.world b)).prod volume) (s.event b)

end Submission.Obl.k4_local_remainder_horizon_transfer.Normalization
