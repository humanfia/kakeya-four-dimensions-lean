/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/Shifted/Statement.lean. Original attribution comments are retained below. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Model
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.MeshCalibration

/-!
# The shifted-candidate statement in field-named form

`ShiftedCandidates cfg` is the conclusion of o260 for the data `cfg`:
original-label shifted quadratic candidates or velocity candidates below every
positive depth horizon `V ≤ U`. `ShiftedTransfer` is the whole obligation in the
field-named model of `Transfer.Model`; `raw_statement_of_shifted_transfer`
turns it into the frozen statement.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_affine_residual_candidate_transfer

noncomputable section

/-- The trajectory point with its hidden coordinate shifted by an affine
function of the base. -/
def shiftedPoint {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ)
    (L : Fin 4 → ℝ) (l : α) (t : ℝ) : Fin 4 → ℝ :=
  ![t, (cfg.x k l t) 1, (cfg.x k l t) 2,
    (cfg.x k l t) 3 - (L 0 + L 1 * t + L 2 * (cfg.x k l t) 1 + L 3 * (cfg.x k l t) 2)]

/-- The polynomial alternative of a shifted candidate at index `k`, label `i`
of depth `s`, improvement `v` and loss `ε`. -/
def ShiftedPoly {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ) (R ε s v : ℝ)
    (i : Fin (cfg.n k s)) : Prop :=
  ∃ (L : Fin 4 → ℝ) (G : MvPolynomial (Fin 4) ℝ), G.totalDegree ≤ 2 ∧
    (∀ e, |G.coeff e| ≤ cfg.N k ^ R) ∧
    ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i) ≤
      cfg.ρ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧
        (∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
          |(shiftedPoint cfg k L p.1 t) 3| ≤ 1 ∧
          |eval (shiftedPoint cfg k L p.1 t) G| ≤ cfg.N k ^ ε * cfg.N k ^ (-s - v) ∧
          |eval (shiftedPoint cfg k L p.1 t) (pderiv (3 : Fin 4) G)| ≤ cfg.N k ^ ε ∧
          |eval (shiftedPoint cfg k L p.1 t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤
            cfg.N k ^ ε / cfg.N k ^ (-s - v)) ∧
        cfg.N k ^ (-ε) ≤ |eval (shiftedPoint cfg k L p.1 p.2) (pderiv (3 : Fin 4) G)|}

/-- The velocity alternative, exactly as in the original candidate. -/
def ShiftedVelocity {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ) (R ε s v : ℝ)
    (i : Fin (cfg.n k s)) : Prop :=
  ∃ z : Fin 2 → ℝ, (∀ e, |z e| ≤ cfg.N k ^ R) ∧
    ENNReal.ofReal (cfg.N k ^ (-ε) / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i) ≤
      cfg.ρ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧
        |cfg.b k p.1 4 - z 0 - z 1 * cfg.b k p.1 3| ≤ cfg.N k ^ ε * cfg.N k ^ (-cfg.ℓ * s - v)}

/-- The conclusion of o260 for the data `cfg`. -/
def ShiftedCandidates {α : Type} [MeasurableSpace α] (cfg : Data α) : Prop :=
  ∀ V : ℝ, 0 < V → V ≤ cfg.U → ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε →
    ∃ᶠ k in atTop, ∃ (s v : ℝ) (i : Fin (cfg.n k s)), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧
      s + v ≤ V ∧ (ShiftedPoly cfg k R ε s v i ∨ ShiftedVelocity cfg k R ε s v i)

/-- The whole obligation in the field-named model. -/
def ShiftedTransfer : Prop :=
  MeshCalibration → HorizontalPrinciple → ∀ (α : Type) [MeasurableSpace α] (cfg : Data α),
    ContactProblem cfg → ShiftedCandidates cfg

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
