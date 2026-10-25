/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/SharedGuard.lean.
Its original attribution comments are retained below.
-/
import Submission.Lib.K4ScalarFiniteGuard
import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces

/-! The accepted shared guard has the literal frozen scalar chart interface. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Discard exact-sequence fields unused by the shared chart guard. -/
noncomputable def guardModel (p : Code) : Submission.Lib.K4ScalarFiniteGuard.Model where
  worlds := W p
  resolution := N p
  length := L p
  weights := ω p
  priors := ν p
  events := E p
  profile := f p

theorem guardModel_sampling (p : Code) (hp : Exact p) :
    Submission.Lib.K4ScalarFiniteGuard.Sampling (guardModel p) := ⟨hp.1.1, hp.1.2.1⟩

theorem guardModel_chart (p : Code) (B k : ℕ) (r b h ε : ℝ) (isTrue : Bool) :
    Submission.Lib.K4ScalarFiniteGuard.Chart (guardModel p) B r b h ε isTrue k ↔
      Chart p B r b h ε isTrue k := Iff.rfl

theorem guardModel_known (p : Code) (r b h : ℝ) :
    Submission.Lib.K4ScalarFiniteGuard.Known (guardModel p) r b h ↔ Known p r b h := Iff.rfl

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
