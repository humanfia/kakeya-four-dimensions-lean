/-
Adapted from this LOT tree, obligation o168, session x0569, branch x0569,
Submission/Obl/k4_scalar_guarded_tangent_preparation/Construction.lean.
The original source is work of this tree; its provenance comments are retained.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.RawGeometry

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

/-- The geometric construction owns the genuine measured paths, all
potential-parent masks and the low-information window. The original sample
guard is already imposed on each chosen exact parent. -/
def EntropicPathConstruction : Prop :=
  Split.Initial → Split.Calculus → Split.Critical →
  ∃ (p : ℕ → Code) (sample : ℕ → ℕ) (scale H buffer B : ℕ → ℝ)
    (M count : ℕ → ℕ) (node : (k : ℕ) → ℝ → Fin (count k))
    (depth time : (k : ℕ) → Fin (count k) → ℝ)
    (layers : (k : ℕ) → Fin (count k) → Layer ((p k).W (sample k)))
    (σ : (k : ℕ) → Fin ((p k).W (sample k)) → MeasureTheory.Measure Incidence)
    (d κ S : ℝ),
    RawGeometry p sample scale H buffer B M count node depth time layers σ d κ S ∧
    ReferenceLaws (fun k => (p k).N (sample k) ^ scale k) B d S
      (fun k => (p k).W (sample k)) (fun k => (p k).weight (sample k)) σ


end

end Submission.Obl.k4_scalar_guarded_entropic_path
