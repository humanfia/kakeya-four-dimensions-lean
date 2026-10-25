import Submission.Lib.K4QuadraticSheets.QuadTest
import Submission.Lib.K4QuadraticSheets.Branch
import Submission.Lib.K4QuadraticSheets.Slit
import Submission.Lib.K4QuadraticSheets.Tube
import Submission.Lib.K4QuadraticSheets.BrokenTube
import Submission.Lib.K4QuadraticSheets.ContinuationUse
import Submission.Lib.K4QuadraticSheets.LocalBranch
import Submission.Lib.K4QuadraticSheets.Anchor
import Submission.Lib.K4QuadraticSheets.JetBins

/-!
# Quadratic sheets: branches, tubes, continuation and anchor jets

Tools for simple root sheets of quadratic tests `P(z, w)` (total degree at most two, hidden
variable last) over `ℂ³`:

* `QuadTest`: a test as `γ(z) + β(z) w + (c/2) w²`; hidden derivative; discriminant at roots.
* `Branch`: rotated principal square roots and the root branch `rootOf` built from them;
  analyticity.
* `Slit`, `Tube`, `BrokenTube`: analytic square roots of the discriminant, hence simple sheets, on
  tubes around (broken) segments from a lower bound of the discriminant on a thicker tube;
  gluing over preconnected overlaps; uniqueness of root branches.
* `ContinuationUse`: the polynomial-cost continuation input (o113, verbatim as `ContInput`) for two
  sheets (`H = f₁ - f₂`, with jets) and for one sheet in a fixed test (`H = Q(z, f(z))`).
* `LocalBranch`, `Anchor`: canonical local branches at an anchor; forward transport of an agreement
  near a source point to anchor jets (`anchor_forward`); return of a representative evaluation and
  its hidden derivative from close anchor jets (`anchor_return`, `anchor_return_deriv`).
* `JetBins`: jet coordinates on basis tuples, bins, neighbouring bins (a fixed finite number).
-/
