import Submission.Obl.k4_raw_localized_native_systems.Packing.FramePowers

namespace Submission.Obl.k4_raw_localized_native_systems.Packing

open Submission.Obl.k4_finite_width_output_exclusion
open Pairing

noncomputable section

/-- The homogeneous determinant lower bound and the original major-axis
upper bound give a common positive lower bound on every minor width. -/
theorem minor_width_lower_bound {q g κ : ℝ} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q.det ≠ 0) (hq : 0 < q) (hκ : 0 < κ)
    (hdet : q ^ 2 * g ≤ |Q.det|) (hmajor : ‖longCol Q‖ ≤ κ * q) :
    q * g / κ ≤ minorWidth Q := by
  calc
    q * g / κ = (q ^ 2 * g) / (κ * q) := by field_simp
    _ ≤ |Q.det| / ‖longCol Q‖ :=
      div_le_div₀ (abs_nonneg _) hdet (longCol_norm_pos hQ) hmajor

/-- A uniform angular tolerance at the homogeneous width scale satisfies
the label-dependent tolerance used by the raw inverse and packing estimates. -/
theorem homogeneous_angle_bound {q g κ N u θ : ℝ}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {n : Plane}
    (hq : 0 < q) (hκ : 0 < κ) (hN : 0 < N)
    (hminor : q * g / κ ≤ minorWidth Q)
    (hθ : θ ≤ 32 * g * N ^ u)
    (hangle : min ‖n - minorNormal Q‖ ‖n + minorNormal Q‖ ≤ θ) :
    min ‖n - minorNormal Q‖ ‖n + minorNormal Q‖ ≤
      32 * κ * minorWidth Q * N ^ u / q := by
  apply hangle.trans (hθ.trans _)
  have hscaled := mul_le_mul_of_nonneg_left hminor
    (show 0 ≤ 32 * κ * N ^ u / q by positivity)
  calc
    32 * g * N ^ u = (32 * κ * N ^ u / q) * (q * g / κ) := by
      field_simp
    _ ≤ (32 * κ * N ^ u / q) * minorWidth Q := hscaled
    _ = _ := by ring

/-- A single homogeneous relative-width condition implies the raw
label-dependent relative-width condition for every earlier witness. -/
theorem homogeneous_relative_width {q g κ N gC : ℝ}
    {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hq : 0 < q) (hN : 0 < N)
    (hminor : q * g / κ ≤ minorWidth Q)
    (hrel : gC ≤ q ^ 2 * g / (κ * N ^ (4 : ℕ))) :
    gC ≤ minorWidth Q * q / N ^ (4 : ℕ) := by
  apply hrel.trans
  calc
    q ^ 2 * g / (κ * N ^ (4 : ℕ)) = (q * g / κ) * q / N ^ (4 : ℕ) := by ring
    _ ≤ minorWidth Q * q / N ^ (4 : ℕ) := by gcongr

/-- On the long-major portion of a homogeneous family, the earlier normal
velocity strip has one common width. Short majors are charged separately. -/
theorem homogeneous_normal_speed_bound {N q g band a κ : ℝ}
    {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hN : 1 ≤ N) (hq : 0 < q) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (hdet : |Q.det| ≤ q ^ 2 * g * N ^ (2 * band))
    (hmajor : q * N ^ (-a) ≤ ‖longCol Q‖) :
    2 * κ * minorWidth Q / q ≤ 2 * κ * g * N ^ (2 * band + a) := by
  calc
    2 * κ * minorWidth Q / q ≤ 2 * κ * (q * g * N ^ (2 * band + a)) / q := by
      gcongr
      exact minor_width_power_bound hN hq hg hdet hmajor
    _ = _ := by field_simp

/-- The original chart and its homogeneous logarithmic width band supply the
uniform minor lower bound without a separate geometric hypothesis. -/
theorem chart_minor_width_lower_bound {p : Data} {k M D : ℕ} {W : Atlas p k}
    {κ r q width nw band : ℝ} {e : Fin W.C}
    (hW : Window.WChart p k W M D κ r e) (hN : 1 ≤ p.N k) (hκ : 0 < κ)
    (hqtime : q = 1 / (2 : ℝ) ^ W.T)
    (hexact : p.N k ^ (-width) = |(W.Q e).det| * (4 : ℝ) ^ W.T)
    (hband : |width - nw| ≤ band) :
    q * p.N k ^ (-nw - band) / κ ≤ minorWidth (W.Q e) := by
  have hq : 0 < q := by rw [hqtime]; positivity
  exact minor_width_lower_bound hW.det_ne hq hκ
    (determinant_band_bounds hN hqtime hexact hband).1
    (chart_major_bound hW le_rfl hqtime)

/-- Uniform homogeneous cutoffs imply all three geometric conditions of the
raw certificate. The major cutoff may spend less than the raw angle exponent. -/
theorem homogeneous_raw_compatibility {p : Data} {k M D : ℕ} {W : Atlas p k}
    {κ r q width nw band a u θ gC : ℝ} {e : Fin W.C} {n : Plane}
    (hW : Window.WChart p k W M D κ r e) (hN : 1 ≤ p.N k) (hκ : 0 < κ)
    (hqtime : q = 1 / (2 : ℝ) ^ W.T)
    (hexact : p.N k ^ (-width) = |(W.Q e).det| * (4 : ℝ) ^ W.T)
    (hband : |width - nw| ≤ band) (hau : a ≤ u)
    (hmajor : q * p.N k ^ (-a) ≤ ‖longCol (W.Q e)‖)
    (hθ : θ ≤ 32 * p.N k ^ (-nw - band) * p.N k ^ u)
    (hangle : min ‖n - minorNormal (W.Q e)‖ ‖n + minorNormal (W.Q e)‖ ≤ θ)
    (hrel : gC ≤ q ^ 2 * p.N k ^ (-nw - band) / (κ * p.N k ^ (4 : ℕ))) :
    q * p.N k ^ (-u) ≤ ‖longCol (W.Q e)‖ ∧
      min ‖n - minorNormal (W.Q e)‖ ‖n + minorNormal (W.Q e)‖ ≤
        32 * κ * minorWidth (W.Q e) * p.N k ^ u / q ∧
      gC ≤ minorWidth (W.Q e) / ((2 : ℝ) ^ W.T * p.N k ^ (4 : ℕ)) := by
  have hq : 0 < q := by rw [hqtime]; positivity
  have hN0 : 0 < p.N k := lt_of_lt_of_le zero_lt_one hN
  have hminor := chart_minor_width_lower_bound hW hN hκ hqtime hexact hband
  refine ⟨?_, homogeneous_angle_bound hq hκ hN0 hminor hθ hangle, ?_⟩
  · apply le_trans _ hmajor
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hq.le
  · have h := homogeneous_relative_width hq hN0 hminor hrel
    convert h using 1
    rw [hqtime]
    ring

end
end Submission.Obl.k4_raw_localized_native_systems.Packing
