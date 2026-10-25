import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StagePath

/-! The zeroth finite-menu view is the literal original source view.
Its complete root geometry controls all prefix velocity normalizations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open TrueLiftChains
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem TrueGridPath.viewAt_zero_as_original {ctx : CriticalContext}
    {source : MaximizingFamily ctx} {start : ℝ} {targets : List ℝ} {root : Code}
    (path : TrueGridPath ctx source start targets) (i : ℕ) (certs : path.Certificates i)
    (hl : path.forget.AllLayers i) (before : Chain root (source.problem i)) :
    path.viewAt i certs hl before 0 = path.originalView i certs hl before := by
  cases path <;> rfl

namespace StagePath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

def rootIndex (s : StagePath ctx source k R δ) : Fin (s.layout.targets.length + 1) :=
  ⟨0, Nat.succ_pos _⟩

theorem views_rootIndex (s : StagePath ctx source k R δ) :
    s.views s.rootIndex = s.path.originalView s.outer s.certs s.laws
      (.nil _ (source.angular s.outer).1) :=
  s.path.viewAt_zero_as_original s.outer s.certs s.laws _

end StagePath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
