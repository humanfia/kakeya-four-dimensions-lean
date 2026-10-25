import Submission.Lib.K4QuadraticSheetCore.Zoom
import Submission.Lib.K4QuadraticSheetCore.SheetAlgebra
import Submission.Lib.K4QuadraticSheetCore.SheetPolynomials
import Submission.Lib.K4QuadraticSheetCore.PolyBounds
import Submission.Lib.K4QuadraticSheetCore.SheetLines
import Submission.Lib.K4QuadraticSheetCore.SheetFrame
import Submission.Lib.K4QuadraticSheetCore.SheetCore
import Submission.Lib.K4QuadraticSheetCore.SheetAffine
import Submission.Lib.K4QuadraticSheetCore.SheetBridge

/-!
# Affine hidden sheets of quadratic tests along full-time contact lines

Adapted from: here:o223 (session x0777, branch x0777).

A complex-analysis-free version of the affine-sheet step (paper Lemma 8.6) for hidden tests of
total degree at most two. For `G = γ + β w + α w²` the projected second fundamental form `M` is a
matrix of quadratic base polynomials; along any full-time line `M[V,V]` is bounded by the line's
own test values (`sff_line_bound`); Heisenberg commutator identities recover its vertical
components from the horizontal ones; polynomial Remez and coefficient bounds extend witness
estimates to the unit cube, with contact and mesh errors absorbed (`sff_frame_bound`). The tangent
plane then fits the test on the cube (`tangent_plane_bound`) and every full-time line with an
event stays near it or near the far affine branch (`line_near_affine_branches`); high curvature
uses the affine centre (`line_near_affine_centre`). `SheetBridge` reads four-variable tests along
`point b σ`, and `Zoom` is the Heisenberg chart of a true block.
-/
