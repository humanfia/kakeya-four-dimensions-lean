import Submission.Obl.k4_native_calibrated_homogeneous_remainder.TerminalCalibration
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CmpDensityCap

/-! Add the inherited density and angular caps to the calibrated pure family. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion

def CalibratedPureRemainder.finish {p q : Data} {r h w : ℝ}
    (a : CalibratedPureRemainder p q r h w) (hp : Valid p) (hr : 0 ≤ r) :
    CalibratedRemainder p q r h w := by
  have hv : Valid q := by
    have hraw := a.homogeneous.1
    obtain ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, M, D, hfmt⟩ := hraw
    have hE : ∀ k b, MeasurableSet (q.E k b) ∧ q.E k b ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
      intro k b
      rcases (hfmt k).2.2.2.1 b with ⟨-, -, -, -, -, -, -, hEm, hEt, -⟩
      exact ⟨hEm, hEt⟩
    have htyp : ∀ s τ : ℝ, 0 ≤ s → s ≤ q.L → 0 < τ → ∃ c : ℝ, 0 < c ∧
        ∀ᶠ k in atTop, (∑ b, ENNReal.ofReal (q.ω k b) *
          (((q.ν k b).prod volume).restrict (q.E k b))
            {z | q.g k b s (obs (q.B k b) (δ (q.N k) s) z) <
              ENNReal.ofReal (q.N k ^ (-q.f s - τ)) ∨
              ENNReal.ofReal (q.N k ^ (-q.f s + τ)) <
                q.g k b s (obs (q.B k b) (δ (q.N k) s) z)}) ≤
          ENNReal.ofReal (q.N k ^ (-c)) := by
      intro s τ hs hsL hτ
      obtain ⟨c, hc, hev⟩ := a.homogeneous.2.2.2.2 s hs hsL τ hτ
      refine ⟨c, hc, ?_⟩
      filter_upwards [hev] with k hk
      simpa only [familyLaw, worldLaw_apply, mem_ofPred_eq, selected, priorMass] using hk
    have hdcap := Cmp.geometry_density_cap a.toRemainderGeometry hp hr
      (fun k b => (hE k b).1) hK.2 hK.1 (fun k => (hfmt k).2.2.2.2)
      (fun k b s _ _ => a.homogeneous.2.1 k b s) htyp a.terminal_calibration
    have hang := Cmp.geometry_angular_cap a.toRemainderGeometry hp hr hE
      (fun k b u _ _ => by
        simpa only [← Cmp.jobs_eq, selected, priorMass,
          Submission.Obl.k4_remainder_angular_cap_transport.Geometry.jointRef]
          using a.homogeneous.2.2.1 k b u)
      a.terminal_calibration
    apply pure_homogeneous_valid_of_caps a.homogeneous hdcap
    intro u τ hu huL hτ
    obtain ⟨c, hc, hev⟩ := hang u τ hu huL hτ
    refine ⟨c, hc, ?_⟩
    filter_upwards [hev] with k hk
    simpa only [familyLaw, worldLaw_apply, mem_ofPred_eq, selected, priorMass,
      ← Cmp.jobs_eq] using hk
  exact {
    toRemainderGeometry := a.toRemainderGeometry
    valid := hv
    terminal_calibration := a.terminal_calibration }

theorem calibrated_remainder_construction (p q₀ : Data) (r h w : ℝ)
    (hp : Valid p) (hr : 0 ≤ r) (_hrL : r < p.L) (a : RawRemainder p q₀ r h w) :
    ∃ q : Data, Nonempty (CalibratedRemainder p q r h w) := by
  obtain ⟨q, ⟨a'⟩⟩ := a.calibrated_pure_preparation hp
  exact ⟨q, ⟨a'.finish hp hr⟩⟩

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
