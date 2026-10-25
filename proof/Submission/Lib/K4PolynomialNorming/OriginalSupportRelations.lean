/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.Probability.Kernel.Composition.MeasureComp

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- An invariant original redraw keeps every original almost-sure support.
A subsequent line-preserving refresh therefore keeps the geometric
relation certified at the actual intermediate shared state. -/
theorem stationary_redraw_refresh_ae_relation {X L Q : Type*}
    [MeasurableSpace X] [MeasurableSpace L]
    (P : Measure X) (A B : Kernel X X) (hA : A ∘ₘ P = P)
    (key : X → Q) (line : X → L) (hline : Measurable line)
    (hsame : ∀ᵐ x ∂P, ∀ᵐ y ∂A x, key y = key x)
    (hrefresh : ∀ y, ∀ᵐ z ∂B y, line z = line y)
    (R : X → L → Prop) (hR : MeasurableSet {z : X × L | R z.1 z.2})
    (Valid : X → Prop) (hValid : ∀ᵐ x ∂P, Valid x)
    (hcert : ∀ x y, key y = key x → Valid x → Valid y → R x (line y)) :
    ∀ᵐ x ∂P, ∀ᵐ z ∂(B ∘ₖ A) x, R x (line z) := by
  have hredraw : ∀ᵐ x ∂P, ∀ᵐ y ∂A x, Valid y := by
    apply Measure.ae_ae_of_ae_comp
    rw [hA]
    exact hValid
  filter_upwards [hValid,hredraw,hsame] with x hx hdraw hkey
  apply Kernel.ae_comp_of_ae_ae (hR.preimage (measurable_const.prodMk hline))
  filter_upwards [hdraw,hkey] with y hy hkeyy
  filter_upwards [hrefresh y] with z hz
  rw [hz]
  exact hcert x y hkeyy hx hy

end Submission.Lib.K4PolynomialNorming
