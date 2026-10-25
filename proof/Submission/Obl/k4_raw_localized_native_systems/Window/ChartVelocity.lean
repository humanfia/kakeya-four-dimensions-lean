import Submission.Obl.k4_raw_localized_native_systems.Window.RawAssembly
import Submission.Lib.K4XInterface.Charts
import Submission.Lib.K4ChartLifting.Bounds

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k M D : ℕ} {W : Atlas p k} {κ r : ℝ} {e : Fin W.C}

theorem WChart.velocity_inverse (hW : WChart p k W M D κ r e)
    {l : Line} (hl : l ∈ W.A e) :
    ‖Matrix.toEuclideanLin (W.Q e)⁻¹ (v l - W.u e)‖ ≤ 2 * κ * (2 : ℝ) ^ W.T := by
  obtain ⟨ex, hW⟩ := hW
  exact Submission.Lib.K4XInterface.gchart_velocity hW hl

/-- The original small frame confines center velocities through an actual assigned line. -/
theorem WChart.velocity_sub_center (hW : WChart p k W M D κ r e)
    {l : Line} (hl : l ∈ W.A e) : ‖v l - W.u e‖ ≤ 2 * κ ^ 2 := by
  have hκ : 0 ≤ κ := by
    have h := hW.l1_le
    have hsum : 0 ≤ (∑ i : Fin 2, ∑ j : Fin 2, |W.Q e i j|) := by positivity
    have hdiv : 0 ≤ κ / (2 : ℝ) ^ W.T := hsum.trans h
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ W.T)] at hdiv
    simpa using hdiv
  have heq : v l - W.u e = Matrix.toEuclideanLin (W.Q e)
      (Matrix.toEuclideanLin (W.Q e)⁻¹ (v l - W.u e)) :=
    (Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel (W.Q e) hW.det_ne _).symm
  rw [heq]
  apply (Submission.Lib.K4ChartLifting.norm_toEuclideanLin_le _ _).trans
  calc
    _ ≤ (κ / (2 : ℝ) ^ W.T) * (2 * κ * (2 : ℝ) ^ W.T) :=
      mul_le_mul hW.l1_le (hW.velocity_inverse hl) (norm_nonneg _) (by positivity)
    _ = 2 * κ ^ 2 := by field_simp

end
end Submission.Obl.k4_raw_localized_native_systems.Window
