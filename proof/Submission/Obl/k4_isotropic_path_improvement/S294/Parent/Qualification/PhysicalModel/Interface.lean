-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.Interface, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/Interface.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open MeasureTheory Set Polynomial

noncomputable section

/-- A quadratic signal and two affine base coordinates on the original
indexed trajectories. The signal is an independent physical observable;
no chart test or hidden-coordinate substitution is part of this model. -/
structure PhysicalModel where
  scalarCoefficients : Ln → Fin 7 → ℝ
  measurable_scalarCoefficients : Measurable scalarCoefficients
  assigned : Set Ln
  measurable_assigned : MeasurableSet assigned
  slack : ℝ
  scalar_coefficients_bound : ∀ l ∈ assigned, ∀ i, |scalarCoefficients l i| ≤ 17 * slack
  event : Set Ev
  measurable_event : MeasurableSet event
  event_assignment : ∀ z ∈ event, z.1 ∈ assigned
  event_time : ∀ z ∈ event, z.2 ∈ Icc (0 : ℝ) 1

namespace PhysicalModel

def signal (p : PhysicalModel) (l : Ln) : Polynomial ℝ :=
  C (p.scalarCoefficients l 0) + C (p.scalarCoefficients l 1) * X +
    C (p.scalarCoefficients l 2) * X ^ 2

def signalValue (p : PhysicalModel) (l : Ln) (t : ℝ) : ℝ :=
  Jets2.zx (p.scalarCoefficients l) t

def position (p : PhysicalModel) (l : Ln) : Fin 3 → ℝ :=
  ![0, p.scalarCoefficients l 3, p.scalarCoefficients l 5]

def velocity (p : PhysicalModel) (l : Ln) : Fin 3 → ℝ :=
  ![1, p.scalarCoefficients l 4, p.scalarCoefficients l 6]

def prior (p : PhysicalModel) (ν : Measure Ln) : Measure Ln :=
  (ν p.assigned)⁻¹ • ν.restrict p.assigned

theorem eval_signal (p : PhysicalModel) (l : Ln) (t : ℝ) :
    (p.signal l).eval t = p.signalValue l t := by
  simp [signal, signalValue, Jets2.zx]

theorem scalar_x (p : PhysicalModel) (l : Ln) (t : ℝ) :
    Jets2.zx (p.scalarCoefficients l) t = p.signalValue l t := rfl

theorem scalar_x_derivative (p : PhysicalModel) (l : Ln) (t : ℝ) :
    p.scalarCoefficients l 1 + 2 * p.scalarCoefficients l 2 * t =
      (p.signal l).derivative.eval t := by
  simp [signal]
  ring

theorem signal_degree (p : PhysicalModel) (l : Ln) : (p.signal l).natDegree ≤ 2 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

theorem velocity_time (p : PhysicalModel) (l : Ln) : p.velocity l 0 = 1 := rfl

theorem prior_eq (p : PhysicalModel) (ν : Measure Ln) :
    p.prior ν = (ν p.assigned)⁻¹ • ν.restrict p.assigned := rfl

theorem event_unit_time (p : PhysicalModel) : p.event ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
  fun z hz => ⟨mem_univ _, p.event_time z hz⟩

end PhysicalModel

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
