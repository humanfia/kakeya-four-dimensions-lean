/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/IntermediateCalibration.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_chart_normalization.Coarsening
import Submission.Obl.k4_scalar_true_terminal_lifting.TerminalTail
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RefinementWitness

/-! Intermediate calibration from the accepted terminal comparison on same-law coarsenings. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Filter Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

namespace RefinementWitness

variable {p q : Code} {r b h : ℝ}

/-- The accepted terminal comparison uses exactly these literal witnesses. -/
theorem refBody (w : RefinementWitness p q r b h) :
    Submission.Obl.k4_scalar_true_terminal_lifting.RefBody p q r b h
      w.sample w.loss w.exponent w.T w.world w.block w.assignment w.selected
      w.center w.speed w.width w.polynomial w.lists w.trajectory :=
  ⟨w.sample_strictMono, w.loss_pos, w.loss_tendsto, w.exponent_one,
    w.charts, w.maps, w.weights⟩

open Classical in
/-- Actual normalized worlds whose full parent assignments are too small
for a child true floor at the intermediate depth s. -/
noncomputable def intermediateBadMass (w : RefinementWitness p q r b h)
    (s δ : ℝ) (k : ℕ) : ENNReal :=
  ∑ i : Fin (W q k),
    if ν p (w.sample k) (w.world k i) (w.assignment k i) <
        ENNReal.ofReal (N q k ^ (f q s - f p (r + s) - δ) * w.width k i) then
      ENNReal.ofReal (ω q k i) * mu q k i univ
    else 0

/-- Coarsen both exact problems to the requested intermediate endpoints,
then reuse the ACCEPTED terminal density comparison on the SAME witness.
No prescribed true parent atlas is required. -/
theorem intermediateBadMass_powerSmall (w : RefinementWitness p q r b h)
    (hp : Exact p) (hq : Exact q) (hL : L q = L p - r)
    (hr : 0 ≤ r) (hrb : r ≤ b) (hh : 0 ≤ h)
    (s dp dq : ℝ) (hs : 0 < s) (hsL : s < L q) (hbs : b ≤ r + s)
    (hdp : 0 ≤ dp) (hdp₁ : dp < 1) (hdq : 0 ≤ dq) (hdq₁ : dq < 1)
    (hcapP : ∀ t : ℝ, 0 ≤ t → t ≤ r + s →
      f p (r + s) - f p t ≤ dp * (r + s - t))
    (hcapQ : ∀ t : ℝ, 0 ≤ t → t ≤ s → f q s - f q t ≤ dq * (s - t))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      w.intermediateBadMass s δ k ≤ ENNReal.ofReal (N q k ^ (-c)) := by
  let p' := Submission.Obl.k4_scalar_chart_normalization.coarsen p (r + s) dp
  let q' := Submission.Obl.k4_scalar_chart_normalization.coarsen q s dq
  have hp' : Exact p' :=
    Submission.Obl.k4_scalar_chart_normalization.exact_coarsen hp
      (by linarith : 0 < r + s) (by linarith : r + s < L p) hdp hdp₁ hcapP
  have hq' : Exact q' :=
    Submission.Obl.k4_scalar_chart_normalization.exact_coarsen hq hs hsL hdq hdq₁ hcapQ
  have hbody : Submission.Obl.k4_scalar_true_terminal_lifting.RefBody p' q' r b h
      w.sample w.loss w.exponent w.T w.world w.block w.assignment w.selected
      w.center w.speed w.width w.polynomial w.lists w.trajectory := w.refBody
  have hbad := Submission.Obl.k4_scalar_true_terminal_lifting.badWorldsSmall
    p' q' r b h hp' hq' hr (show r < r + s by linarith) hrb hbs hh
    (show s = (r + s) - r by ring)
    w.sample w.loss w.exponent w.T w.world w.block w.assignment w.selected
    w.center w.speed w.width w.polynomial w.lists w.trajectory hbody δ hδ
  exact hbad

end RefinementWitness

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
