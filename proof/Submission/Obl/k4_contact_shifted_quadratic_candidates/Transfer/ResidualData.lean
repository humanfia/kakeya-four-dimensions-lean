/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/ResidualData.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.Frame

/-!
# The residual horizontal model

Given a frame at the indices where one has been prepared, the residual model
uses, at such an index,

* trajectory coefficients `Frame.coeff`: the parent contact chart followed by
  the residual of the parent's affine entry, divided by the parent width;
* the trajectory prior conditioned on the parent's successful history set;
* the original incidence and residual laws restricted to the frame core, with
  time rescaled to the parent block and mass divided by the parent reference
  `q₀ * ν(parent history)`;
* the original velocity palette and the native test `X 3`;
* the grid label levels of the frame.

At other indices it is a trivial model (prior times uniform time, zero
coefficients), which only has to satisfy the per-index basic hypotheses.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

namespace Frame

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable (fr : Frame D k s₀ U')

/-- The parent's successful history set. -/
def parentSet : Set α := fr.hist 0 fr.i₀ fr.u₀

/-- Time in units of the parent block. -/
def toChart (p : α × ℝ) : α × ℝ := (p.1, (p.2 - fr.t₀) / fr.q₀)

/-- The parent reference mass `q₀ * ν(parent history)`. -/
def scale : ENNReal := ENNReal.ofReal fr.q₀ * D.ν k fr.parentSet

/-- The residual incidence law. -/
def resμ : Measure (α × ℝ) := fr.scale⁻¹ • ((D.μ k).restrict fr.core).map fr.toChart

/-- The residual residual law. -/
def resρ : Measure (α × ℝ) := fr.scale⁻¹ • ((D.ρ k).restrict fr.core).map fr.toChart

end Frame

variable {α : Type} [MeasurableSpace α]

/-- The residual model, before its label levels are installed. -/
def residualBase (D : Data α) (s₀ U' e₀' : ℝ) (K' : ℕ → ℝ)
    (fr : (k : ℕ) → Option (Frame D k s₀ U')) : Data α where
  N := D.N
  K := K'
  d := D.d
  κ := D.κ
  ℓ := D.κ
  S := D.S
  U := U'
  e₀ := e₀'
  ν := fun k => match fr k with
    | some f => cond (D.ν k) f.parentSet
    | none => D.ν k
  μ := fun k => match fr k with
    | some f => f.resμ
    | none => (D.ν k).prod (volume.restrict (Icc (0 : ℝ) 1))
  ρ := fun k => match fr k with
    | some f => f.resρ
    | none => (D.ν k).prod (volume.restrict (Icc (0 : ℝ) 1))
  π := D.π
  b := fun k l => match fr k with
    | some f => f.coeff l
    | none => 0
  P := fun _ => X 3
  T := D.T
  n := D.n
  j := D.j
  A := D.A
  B := D.B
  c := D.c
  F := D.F

/-- The residual label levels; an index without a frame has no labels. -/
def residualLevels (D : Data α) (s₀ U' : ℝ)
    (fr : (k : ℕ) → Option (Frame D k s₀ U')) (k h : ℕ) : LabelLevel α :=
  match fr k with
  | some f => f.level h
  | none => ⟨0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩

/-- The number of grid steps; one at an index without a frame. -/
def residualSteps (D : Data α) (s₀ U' : ℝ)
    (fr : (k : ℕ) → Option (Frame D k s₀ U')) (k : ℕ) : ℕ :=
  match fr k with
  | some f => f.m
  | none => 1

/-- The residual horizontal model. -/
def residualData (D : Data α) (s₀ U' e₀' : ℝ) (K' : ℕ → ℝ)
    (fr : (k : ℕ) → Option (Frame D k s₀ U')) : Data α :=
  withLevels (residualBase D s₀ U' e₀' K' fr) (residualLevels D s₀ U' fr)
    (fun k => U' / residualSteps D s₀ U' fr k) (residualSteps D s₀ U' fr)

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
