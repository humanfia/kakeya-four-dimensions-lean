-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.PathBridge, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/PathBridge.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/PathBridge.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path
import Submission.Obl.k4_finite_positive_mixed_cover_realization.Path

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

/-- Read the accepted frozen-path interface from the unchanged native data. -/
abbrev Native.PathData.toOriginal {W : ℕ} (p : Native.PathData W) :
    Submission.Obl.k4_finite_positive_mixed_cover_realization.PathData W where
  r := p.r
  T := p.T
  nw := p.nw
  κ := p.κ
  C := p.C
  lev := p.lev
  par := p.par
  world := p.γ
  bin := p.j
  center := p.c
  velocity := p.u
  frame := p.Q
  test := p.R
  assigned := p.A
  counted := p.F
  lists := p.lst

theorem Native.PathData.Valid.toOriginal {W : ℕ} {p : Native.PathData W}
    {Nk L κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → MeasureTheory.Measure Ln}
    {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) :
    p.toOriginal.Valid 0 Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ := hp

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
