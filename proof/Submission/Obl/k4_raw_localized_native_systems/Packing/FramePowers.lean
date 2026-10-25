import Submission.Obl.k4_raw_localized_native_systems.Packing.Geometry
import Submission.Obl.k4_raw_localized_native_systems.Window.ChartVelocity

namespace Submission.Obl.k4_raw_localized_native_systems.Packing

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing

noncomputable section

theorem long_col_norm_le_l1 (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖longCol Q‖ ≤ ∑ i : Fin 2, ∑ j : Fin 2, |Q i j| := by
  have h₀ : ‖col0 Q‖ ≤ ∑ i : Fin 2, ∑ j : Fin 2, |Q i j| := by
    have h := Submission.Lib.K4ChartLifting.norm_toEuclideanLin_le Q
      (WithLp.toLp 2 ![1, 0])
    have hn : ‖(WithLp.toLp 2 ![1, 0] : Plane)‖ = 1 := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simpa only [toEuclideanLin_fin2_eq, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_smul, zero_smul, add_zero, hn, mul_one] using h
  have h₁ : ‖col1 Q‖ ≤ ∑ i : Fin 2, ∑ j : Fin 2, |Q i j| := by
    have h := Submission.Lib.K4ChartLifting.norm_toEuclideanLin_le Q
      (WithLp.toLp 2 ![0, 1])
    have hn : ‖(WithLp.toLp 2 ![0, 1] : Plane)‖ = 1 := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simpa only [toEuclideanLin_fin2_eq, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_smul, zero_smul, zero_add, hn, mul_one] using h
  unfold longCol
  split_ifs <;> assumption

theorem chart_major_bound {p : Data} {k M D : ℕ} {W : Atlas p k}
    {κ r K q : ℝ} {e : Fin W.C} (hW : Window.WChart p k W M D κ r e)
    (hκK : κ ≤ K) (hqtime : q = 1 / (2 : ℝ) ^ W.T) :
    ‖longCol (W.Q e)‖ ≤ K * q := by
  calc
    _ ≤ κ / (2 : ℝ) ^ W.T := (long_col_norm_le_l1 _).trans hW.l1_le
    _ ≤ K / (2 : ℝ) ^ W.T := div_le_div_of_nonneg_right hκK (by positivity)
    _ = _ := by rw [hqtime]; ring

/-- A homogeneous logarithmic width band gives both actual determinant bounds,
with the physical block length kept explicit. -/
theorem determinant_band_bounds {N width nw band q : ℝ} {T : ℕ}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hN : 1 ≤ N)
    (hq : q = 1 / (2 : ℝ) ^ T)
    (hexact : N ^ (-width) = |Q.det| * (4 : ℝ) ^ T)
    (hband : |width - nw| ≤ band) :
    q ^ 2 * N ^ (-nw - band) ≤ |Q.det| ∧
      |Q.det| ≤ q ^ 2 * N ^ (-nw - band) * N ^ (2 * band) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hfour : (4 : ℝ) ^ T = ((2 : ℝ) ^ T) ^ 2 := by
    calc
      (4 : ℝ) ^ T = ((2 : ℝ) * 2) ^ T := by norm_num
      _ = _ := by rw [mul_pow]; ring
  have heq : |Q.det| = q ^ 2 * N ^ (-width) := by
    rw [hexact, hfour, hq]
    field_simp
  rw [heq]
  rw [abs_le] at hband
  constructor
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (sq_nonneg q)
  · calc
      _ ≤ q ^ 2 * N ^ (-nw + band) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (sq_nonneg q)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hN0]; congr 2 <;> ring

/-- Removing only short major axes converts the homogeneous determinant band
into the actual minor-width bound needed by the common tube. -/
theorem minor_width_power_bound {N q g band u : ℝ}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hN : 1 ≤ N) (hq : 0 < q) (hg : 0 ≤ g)
    (hdet : |Q.det| ≤ q ^ 2 * g * N ^ (2 * band))
    (hmajor : q * N ^ (-u) ≤ ‖longCol Q‖) :
    minorWidth Q ≤ q * g * N ^ (2 * band + u) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hdiv : N ^ (2 * band) / N ^ (-u) = N ^ (2 * band + u) := by
    rw [← Real.rpow_sub hN0]
    congr 1
    ring
  calc
    minorWidth Q ≤ (q ^ 2 * g * N ^ (2 * band)) / (q * N ^ (-u)) :=
      div_le_div₀ (by positivity) hdet (by positivity) hmajor
    _ = q * g * (N ^ (2 * band) / N ^ (-u)) := by field_simp
    _ = _ := by rw [hdiv]

/-- The fixed relative gain requested from the later sources pays the current
strip radius at the physical earlier scale. -/
theorem strip_radius_from_relative_width {N q g E minor gC K r₀ : ℝ}
    (hN : 0 < N) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hg : 0 ≤ g)
    (hE : 1 ≤ E) (hEbound : E ≤ N ^ (4 : ℕ)) (hK : 0 ≤ K)
    (hminor : minor ≤ q * g * E) (hrel : gC ≤ minor * q / N ^ (4 : ℕ))
    (hr₀ : r₀ ≤ K * gC) : r₀ ≤ K * q * g * E ^ 2 := by
  have hE0 : 0 ≤ E := by linarith
  have hE2 : 1 ≤ E ^ 2 := by nlinarith
  have hratio : 0 ≤ E / N ^ (4 : ℕ) := by positivity
  have hratio1 : E / N ^ (4 : ℕ) ≤ 1 := (div_le_one (by positivity)).mpr hEbound
  have hproduct : q * (E / N ^ (4 : ℕ)) ≤ 1 := by
    calc
      q * (E / N ^ (4 : ℕ)) ≤ 1 * 1 := mul_le_mul hq1 hratio1 hratio (by norm_num)
      _ = 1 := one_mul _
  have hwidth : gC ≤ q * g := by
    calc
      gC ≤ minor * q / N ^ (4 : ℕ) := hrel
      _ ≤ (q * g * E) * q / N ^ (4 : ℕ) := by gcongr
      _ = q * g * (q * (E / N ^ (4 : ℕ))) := by ring
      _ ≤ q * g * 1 := mul_le_mul_of_nonneg_left hproduct (mul_nonneg hq hg)
      _ = q * g := mul_one _
  calc
    r₀ ≤ K * (q * g) := hr₀.trans (mul_le_mul_of_nonneg_left hwidth hK)
    _ ≤ K * (q * g) * E ^ 2 := le_mul_of_one_le_right (by positivity) hE2
    _ = _ := by ring

/-- Transfer the earlier normal velocity strip to the current normal through
the same original trajectory. Projective signs need not be chosen globally. -/
theorem common_velocity_normal_bound {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {n v u : Plane} {β θ V₀ ρ B : ℝ}
    (hangle : min ‖n - minorNormal Q‖ ‖n + minorNormal Q‖ ≤ θ)
    (hold : |inner ℝ (minorNormal Q) (v - u)| ≤ B)
    (hcurrent : |inner ℝ n (v - β • n)| ≤ ρ)
    (hvel : ‖v - u‖ ≤ V₀) :
    |inner ℝ (u - β • n) n| ≤ ρ + B + θ * V₀ := by
  have hθ : 0 ≤ θ := (le_min (norm_nonneg _) (norm_nonneg _)).trans hangle
  have htrans := abs_inner_of_projective_close hangle hold
  have heq : inner ℝ (u - β • n) n =
      inner ℝ n (v - β • n) - inner ℝ n (v - u) := by
    rw [real_inner_comm, inner_sub_right, inner_sub_right, inner_sub_right]
    ring
  rw [heq]
  calc
    _ ≤ |inner ℝ n (v - β • n)| + |inner ℝ n (v - u)| := abs_sub _ _
    _ ≤ ρ + (B + θ * ‖v - u‖) := add_le_add hcurrent htrans
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hvel hθ]

theorem earlier_normal_velocity_bound {p : Data} {k M D : ℕ}
    {W : Atlas p k} {κ r q : ℝ} {e : Fin W.C} {l : Line}
    (hW : Window.WChart p k W M D κ r e) (hl : l ∈ W.A e)
    (hq : q = 1 / (2 : ℝ) ^ W.T) :
    |inner ℝ (minorNormal (W.Q e)) (v l - W.u e)| ≤
      2 * κ * minorWidth (W.Q e) / q := by
  have h := abs_inner_offset_le hW.det_ne (hW.velocity_inverse hl)
  apply h.trans_eq
  rw [hq]
  field_simp

/-- The cutoff and co-observed angle threshold imply the exact uniform angle
and center-speed bounds used by `TubeBudget`. -/
theorem compatible_frame_tube_bounds {p : Data} {k M D : ℕ}
    {W : Atlas p k} {κ r K q g E u N r₀ β : ℝ} {e : Fin W.C}
    {n : Plane} {l : Line} (hW : Window.WChart p k W M D κ r e)
    (hl : l ∈ W.A e) (hκ : 0 ≤ κ) (hκK : κ ≤ K) (hK : 1 ≤ K)
    (hκsq : 2 * κ ^ 2 ≤ K) (hq : 0 < q) (hq1 : q ≤ 1)
    (hqtime : q = 1 / (2 : ℝ) ^ W.T) (hg : 0 ≤ g) (hE : 1 ≤ E)
    (hNu : 0 ≤ N ^ u) (hNuE : N ^ u ≤ E)
    (hminor : minorWidth (W.Q e) ≤ q * g * E)
    (hangle : min ‖n - minorNormal (W.Q e)‖ ‖n + minorNormal (W.Q e)‖ ≤
      32 * κ * minorWidth (W.Q e) * N ^ u / q)
    (hv : ‖v l‖ ≤ K) (hr₀ : r₀ ≤ K * q * g * E ^ 2)
    (hcurrent : |inner ℝ n (v l - β • n)| ≤ 2 * r₀) :
    ‖W.u e‖ ≤ 3 * K ^ 2 ∧
      min ‖n - minorNormal (W.Q e)‖ ‖n + minorNormal (W.Q e)‖ ≤
        32 * K * g * E ^ 2 ∧
      |inner ℝ (W.u e - β • n) n| ≤ 64 * K ^ 2 * g * E ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hE2 : E ≤ E ^ 2 := by nlinarith
  have hmin0 := minorWidth_nonneg (W.Q e)
  have hmdiv : minorWidth (W.Q e) / q ≤ g * E := by
    rw [div_le_iff₀ hq]
    nlinarith only [hminor]
  have hθ : 32 * κ * minorWidth (W.Q e) * N ^ u / q ≤ 32 * K * g * E ^ 2 := by
    calc
      _ = 32 * κ * (minorWidth (W.Q e) / q) * N ^ u := by ring
      _ ≤ 32 * K * (g * E) * E := by gcongr
      _ = _ := by ring
  have hvel : ‖v l - W.u e‖ ≤ K := (hW.velocity_sub_center hl).trans hκsq
  have hU : ‖W.u e‖ ≤ 2 * K := by
    have heq : W.u e = v l - (v l - W.u e) := by abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith only [hv, hvel])
  have hB : 2 * κ * minorWidth (W.Q e) / q ≤ 2 * K * g * E := by
    calc
      _ = 2 * κ * (minorWidth (W.Q e) / q) := by ring
      _ ≤ (2 * K) * (g * E) :=
        mul_le_mul (by linarith) hmdiv (div_nonneg hmin0 hq.le) (by positivity)
      _ = _ := by ring
  have hV := common_velocity_normal_bound (hangle.trans hθ)
    ((earlier_normal_velocity_bound hW hl hqtime).trans hB) hcurrent hvel
  have hr : r₀ ≤ K * g * E ^ 2 := hr₀.trans (by
    nlinarith [mul_le_mul_of_nonneg_right hq1
      (show 0 ≤ K * g * E ^ 2 by positivity)])
  have hKg : 2 * K * g * E ≤ 2 * K * g * E ^ 2 :=
    mul_le_mul_of_nonneg_left hE2 (by positivity)
  have hK2 : K ≤ K ^ 2 := by nlinarith
  refine ⟨by nlinarith, hangle.trans hθ, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hK2 (show 0 ≤ g * E ^ 2 by positivity)]

end
end Submission.Obl.k4_raw_localized_native_systems.Packing
