-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentSignalFacts, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentSignalFacts.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentSignalFacts.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Problem

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory

/-- The physical parent quadratic's original full-prior bounds and
counted derivative floor, directly from the frozen source problem. -/
theorem ProblemData.Valid.parent_signal_data
    {d : ProblemData} (hd : d.Valid) (k : ℕ) (w : Fin (d.W k)) :
    0 < d.B k w ∧ (d.P k w).totalDegree ≤ 2 ∧
      (∀ᵐ l ∂d.ν k w, ∀ t∈Icc (0:ℝ) 1,
        ‖y l t‖+‖v l‖ ≤ d.K k ∧
        |MvPolynomial.eval (x l t) (d.P k w)| ≤ d.K k ∧
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv 3 (d.P k w))| ≤ d.K k*d.B k w ∧
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (d.P k w)))| ≤
          d.K k*(d.B k w)^2) ∧
      (∀ᵐ z ∂d.μ k w,
        d.B k w/d.K k ≤ |MvPolynomial.eval (x z.1 z.2) (MvPolynomial.pderiv 3 (d.P k w))|) := by
  rcases hd with ⟨_,_,_,_,_,_,_,_,hformat,_⟩
  obtain ⟨M,D,hformat⟩ := hformat
  rcases (hformat k).2.2.2.1 w with ⟨_,hB,_,_,hP,_,_,_,_,_,_,hwhole,hlower⟩
  exact ⟨hB,hP,hwhole,hlower⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
