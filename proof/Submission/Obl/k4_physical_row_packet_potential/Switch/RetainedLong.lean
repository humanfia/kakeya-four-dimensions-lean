-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/RetainedLong.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Retained six-switch paths start in the weighted set and only
use long lines; from `causal_retained_trajectory_ae_decisions`
(`Submission.Lib.K4PolynomialNorming`, session x0001).
-/
import Submission.Lib.K4PolynomialNorming.RetainedTrajectorySupport
import Submission.Lib.K4PolynomialNorming.HistoryBasisPencils

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4PolynomialNorming

theorem ae_retained_long {X C : Type*} [MeasurableSpace X]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (μ : Measure (ℕ → X)) (w₀ : X → ENNReal) (hw₀ : Measurable w₀)
    (control : X → C) (hcontrol : Measurable control)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (Long : Set X) (hLong : MeasurableSet Long) :
    ∀ᵐ x ∂μ.withDensity (fun x => causalRetentionWeights w₀
        (basisPencilRetention control v r Long) 6 (Preorder.frestrictLe 6 x)),
      ∀ k < 6, x (k + 1) ∈ Long := by
  filter_upwards [causal_retained_trajectory_ae_decisions μ w₀ hw₀
    (basisPencilRetention control v r Long)
    (basisPencilRetention_measurable control hcontrol v r Long hLong) 6] with x hx k hk
  have h := hx.2 k hk
  unfold basisPencilRetention at h
  by_contra hn
  apply h
  rw [Set.indicator_of_notMem]
  intro hmem
  exact hn hmem.1

end Submission.Obl.k4_physical_row_packet_potential.Switch
