import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StagePath
import Submission.Obl.k4_scalar_guarded_entropic_path.ViewNodes

/-! Every possible window parent has enough of the same dense grid to
round the full compact tangent range with the prescribed error. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

theorem exists_candidate_node (s : StagePath ctx source k R δ) (hR : 1 < R)
    (a : Fin s.layout.L) :
    ∃ node : ℝ → Fin (s.candidate a).count, ∀ r : ℝ, R⁻¹ ≤ r → r ≤ R →
      |(s.candidate a).depth (node r) / s.layout.scale - r| ≤ δ := by
  have hscale := s.layout.scale_pos
  have hδ : 0 < δ := hscale.trans_le s.layout.scale_error
  have hgrid : TrueGridPath.GridControl (s.candidate a) ctx.κ
      (s.layout.scale * s.layout.mesh) 1 (s.layout.scale * δ / 10000) := s.grids (a.val + 1)
  obtain ⟨node, hn⟩ := (s.candidate a).exists_layout_node s.layout hR (s.candidate_count a)
    (by positivity : 0 ≤ s.layout.scale * δ / 10000) hgrid
  refine ⟨node, fun r hr₁ hr₂ => (hn r hr₁ hr₂).trans ?_⟩
  have heq : (s.layout.scale * δ / 10000) / s.layout.scale = δ / 10000 := by field_simp
  rw [mul_div_assoc, heq]
  linarith only [s.layout.mesh_error, hδ]

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
