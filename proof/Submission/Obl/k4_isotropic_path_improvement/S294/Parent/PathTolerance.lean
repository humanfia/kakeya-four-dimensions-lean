-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.PathTolerance, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/PathTolerance.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SourceBridge

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.PathTolerance

open MeasureTheory
open ParentSource ParentSource.Native

/-- A path with a smaller actual slack exponent satisfies any larger
slack exponent with all its assignments and tests unchanged. -/
theorem mono {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ σ' : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hN : 1 ≤ N) (hσ : σ ≤ σ') :
    p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ' :=
  ⟨hp.1,hp.2.1.trans (Real.rpow_le_rpow_of_exponent_le hN hσ),hp.2.2⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.PathTolerance
