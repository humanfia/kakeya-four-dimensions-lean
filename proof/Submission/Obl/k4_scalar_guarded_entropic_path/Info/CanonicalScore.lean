import Submission.Obl.k4_scalar_guarded_entropic_path.Info.Canonical
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.MeasureScore

/-! Keep the dependent finite canonical code inside one scalar-valued
function when transporting equal original resolutions. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open MeasureTheory

noncomputable def canonicalScore (N K : ℝ) (m : ℕ) (σ : Measure Incidence) : ℝ :=
  rlScore σ (canonX N m (canonM N K m))
    (canonY m (canonM N K m)) (canonZ m (canonM N K m))

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
