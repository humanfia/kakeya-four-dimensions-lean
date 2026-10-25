/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameCapsAt.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FramePasses
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.GoodFrameCaps

/-!
# The residual pure caps of good frames, in residual base coordinates

The pure half of `eventual_good_frame_caps`, written with the residual base
point and hidden coordinate used by the calibration passes.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem Frame.point_castSucc_eq_resBase {D : Data α} {k : ℕ} {s₀ U' : ℝ}
    (f : Frame D k s₀ U') (p : α × ℝ) :
    (point (f.coeff p.1) p.2 ∘ Fin.castSucc) = f.resBase p := by
  funext e
  fin_cases e <;> rfl

/-- The residual pure caps of every good frame after one original tail. -/
theorem eventual_frame_capsAt (D : Data α) (p : Parameters D) (h1 : D.Basic) (h2 : D.Caps)
    {R s₀ U' : ℝ} (hR : 1 < R) (hs₀ : 0 ≤ s₀) :
    ∀ᶠ k in atTop, ∀ (f : Frame D k s₀ U') (Rk θ K₂ e₀' : ℝ),
      FrameGood f Rk θ K₂ e₀' → D.N k ^ (-1 : ℝ) ≤ θ → f.H * f.a₀ ≤ 1 / 4 →
      f.CapsAt (27 * (6 * D.K k + 5) * D.K k * (D.K k ^ 3 / θ)) R := by
  filter_upwards [eventual_good_frame_caps D p h1 h2 (U' := U') hR hs₀] with k hk
  intro f Rk θ K₂ e₀' hg hθ hq r s hr1 hr2 hs1 hs2 c j
  have hv1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR.le
  have hc := (hk f Rk θ K₂ e₀' hg hθ hq r s 1 hr1 hr2 hs1 hs2 hv1 hR.le).1 c j
  have hset : {x : α × ℝ | f.baseCode r x = c ∧ f.hiddenCode s x = j} =
      {p | Submission.Lib.K4MovingMeshBoxes.baseMesh (D.N k ^ (-r)) (f.resBase p) = c ∧
        ⌊f.resW p / D.N k ^ (-s)⌋ = j} := by
    ext x
    simp only [mem_setOf_eq, Frame.baseCode, f.point_castSucc_eq_resBase]
    rfl
  rw [hset] at hc
  exact hc

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
