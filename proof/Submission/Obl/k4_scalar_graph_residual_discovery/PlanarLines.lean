/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PlanarLines.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Model

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

namespace BaseLine

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def raw (v : ℝ) : Plane := WithLp.toLp 2 ![1, v]

noncomputable def direction (v : ℝ) : Plane := ‖raw v‖⁻¹ • raw v

def intercept (l : ScalarLine) : Plane := WithLp.toLp 2 ![0, l.2 0]

def point (l : ScalarLine) (t : ℝ) : Plane := WithLp.toLp 2 ![t, scalarY l t]

theorem raw_norm_sq (v : ℝ) : ‖raw v‖ ^ 2 = 1 + v ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [raw, Fin.sum_univ_two]

theorem raw_norm_pos (v : ℝ) : 0 < ‖raw v‖ := by
  have h := raw_norm_sq v
  nlinarith [sq_nonneg v, norm_nonneg (raw v)]

theorem raw_norm_le (v : ℝ) : ‖raw v‖ ≤ 1 + |v| := by
  have h := raw_norm_sq v
  nlinarith [sq_abs v, abs_nonneg v, norm_nonneg (raw v)]

theorem direction_norm (v : ℝ) : ‖direction v‖ = 1 := by
  rw [direction, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (raw_norm_pos v),
    inv_mul_cancel₀ (raw_norm_pos v).ne']

theorem continuous_raw : Continuous raw := by
  unfold raw
  fun_prop

theorem continuous_direction : Continuous direction := by
  exact (continuous_raw.norm.inv₀ (fun v => (raw_norm_pos v).ne')).smul continuous_raw

theorem measurable_intercept : Measurable intercept := by
  unfold intercept
  fun_prop

theorem point_on_line (l : ScalarLine) (t : ℝ) :
    point l t = intercept l + (t * ‖raw (l.2 1)‖) • direction (l.2 1) := by
  rw [direction, smul_smul]
  have hc : t * ‖raw (l.2 1)‖ * ‖raw (l.2 1)‖⁻¹ = t := by
    rw [mul_assoc, mul_inv_cancel₀ (raw_norm_pos _).ne', mul_one]
  rw [hc]
  ext e
  fin_cases e <;> simp [point, intercept, raw, scalarY]

theorem direction_det (v w : ℝ) :
    |Matrix.det (Matrix.of fun i j : Fin 2 => (![direction v, direction w] i) j)| =
      |v - w| / (‖raw v‖ * ‖raw w‖) := by
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    direction, PiLp.smul_apply, smul_eq_mul]
  have hv0 : (raw v).ofLp 0 = 1 := by simp [raw]
  have hv1 : (raw v).ofLp 1 = v := by simp [raw]
  have hw0 : (raw w).ofLp 0 = 1 := by simp [raw]
  have hw1 : (raw w).ofLp 1 = w := by simp [raw]
  rw [hv0, hv1, hw0, hw1]
  simp only [mul_one]
  have heq : ‖raw v‖⁻¹ * (‖raw w‖⁻¹ * w) - ‖raw v‖⁻¹ * v * ‖raw w‖⁻¹ =
      (w - v) / (‖raw v‖ * ‖raw w‖) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  rw [heq, abs_div, abs_sub_comm, abs_of_pos (mul_pos (raw_norm_pos v) (raw_norm_pos w))]

/-- A scalar velocity gap gives the determinant floor for the normalized
base lines used by planar Kakeya. -/
theorem direction_det_ge {v w H b : ℝ} (hH : 0 ≤ H) (hb : 0 ≤ b)
    (hv : |v| ≤ H) (hw : |w| ≤ H) (hgap : b ≤ |v - w|) :
    b / (1 + H) ^ 2 ≤
      |Matrix.det (Matrix.of fun i j : Fin 2 => (![direction v, direction w] i) j)| := by
  rw [direction_det]
  apply (le_div_iff₀ (mul_pos (raw_norm_pos v) (raw_norm_pos w))).2
  have hn : ‖raw v‖ * ‖raw w‖ ≤ (1 + H) ^ 2 := by
    calc
      _ ≤ (1 + |v|) * (1 + |w|) :=
        mul_le_mul (raw_norm_le v) (raw_norm_le w) (norm_nonneg _) (by positivity)
      _ ≤ (1 + H) * (1 + H) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (b / (1 + H) ^ 2) * (1 + H) ^ 2 := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = b := div_mul_cancel₀ _ (by positivity)
    _ ≤ |v - w| := hgap

end BaseLine

end Submission.Obl.k4_scalar_graph_residual_discovery
