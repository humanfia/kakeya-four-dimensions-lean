/- Inlined from LOT tree g-oai-074, obligation o202, session x0952,
commit 2fb339809fcfce34b26992c753e7b7c590ce76f7, file Submission/Obl/k4_horizontal_subcritical_rate_candidates/Wide/ShortBudget.lean.
Numerical proof supplied in response to o274/x0969; namespace/imports renamed.
The target record originated on o274/x0969 commit9d747899. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortNumerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

private theorem tiny_linear {R w : ℝ} (hR : 1 ≤ R) (hw : 0 ≤ w)
    (hbudget : 1000 * R ^ 20 * w ≤ 1) (C : ℝ) (n j : ℕ)
    (hC : C ≤ 1000) (hn : n + j ≤ 20) : C * R ^ n * w ≤ 1 / R ^ j := by
  have hR0 : 0 < R := by linarith
  apply (le_div_iff₀ (pow_pos hR0 _)).mpr
  calc
    (C * R ^ n * w) * R ^ j = C * R ^ (n + j) * w := by rw [pow_add]; ring
    _ ≤ 1000 * R ^ 20 * w := by
      apply mul_le_mul_of_nonneg_right _ hw
      exact mul_le_mul hC (pow_le_pow_right₀ hR hn) (pow_nonneg hR0.le _) (by norm_num)
    _ ≤ 1 := hbudget

private theorem tiny_square {R w : ℝ} (hR : 1 ≤ R) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hbudget : 1000 * R ^ 20 * w ≤ 1) (C : ℝ) (n j : ℕ)
    (hC0 : 0 ≤ C) (hC : C ≤ 1000) (hn : n + j ≤ 20) :
    C * R ^ n * w ^ 2 ≤ 1 / R ^ j := by
  have hsq : w ^ 2 ≤ w := by nlinarith
  exact (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ C * R ^ n)).trans
    (tiny_linear hR hw hbudget C n j hC hn)

/-- A deterministic budget for every comparison inequality. The only tight scale
relation, `q*g ≤ D`, is kept explicit; all other losses fit a fixed polynomial. -/
theorem shortNumerics_of_polynomial_budget {N R H q a g D χ ζ w mesh : ℝ}
    (hRbig : 10000 ≤ R) (hH : 1 ≤ H) (hHR : H ≤ R) (hH6 : H ^ 6 ≤ R)
    (hq0 : 0 < q) (hg0 : 0 < g) (ha0 : 0 < a) (hD0 : 0 < D)
    (hq : 1 / R ^ 2 ≤ q) (hg : 1 / R ^ 2 ≤ g)
    (ha : 1 / R ^ 2 ≤ a) (hD : 1 / R ^ 2 ≤ D)
    (hq1 : q ≤ 1) (ha1 : a ≤ 1) (hmD : q * g ≤ D)
    (hw0 : 0 < w) (hbudget : 1000 * R ^ 20 * w ≤ 1)
    (hχ0 : 0 ≤ χ) (hχ : χ ≤ w ^ 2) (hζ0 : 0 ≤ ζ) (hζ : ζ ≤ χ)
    (hm0 : 0 ≤ mesh) (hmχ : mesh ≤ χ * w) :
    ShortNumerics N H q a g D χ ζ w mesh (R ^ 10) (R ^ 5) (4 * H) := by
  have hR : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hw1 : w ≤ 1 := by
    simpa using tiny_linear hR hw0.le hbudget 1 0 0 (by norm_num) (by norm_num)
  have hms : mesh ≤ w ^ 2 := by
    calc
      mesh ≤ χ * w := hmχ
      _ ≤ w ^ 2 * w := mul_le_mul_of_nonneg_right hχ hw0.le
      _ ≤ w ^ 2 := mul_le_of_le_one_right (sq_nonneg w) hw1
  have hmχ' : mesh ≤ χ := hmχ.trans (mul_le_of_le_one_right hχ0 hw1)
  have hζχ : ζ + χ ≤ 2 * w ^ 2 := by linarith
  have hqinv : q⁻¹ ≤ R ^ 2 := by
    have := inv_anti₀ (by positivity : 0 < 1 / R ^ 2) hq
    simpa using this
  have hginv : g⁻¹ ≤ R ^ 2 := by
    have := inv_anti₀ (by positivity : 0 < 1 / R ^ 2) hg
    simpa using this
  have hDinv : D⁻¹ ≤ R ^ 2 := by
    have := inv_anti₀ (by positivity : 0 < 1 / R ^ 2) hD
    simpa using this
  have hqginv : (q * g)⁻¹ ≤ R ^ 4 := by
    rw [mul_inv_rev]
    calc
      g⁻¹ * q⁻¹ ≤ R ^ 2 * R ^ 2 := mul_le_mul hginv hqinv (by positivity) (by positivity)
      _ = R ^ 4 := by ring
  have hqg : 1 / R ^ 4 ≤ q * g := by
    have := mul_le_mul hq hg (by positivity) (by positivity)
    convert this using 1 <;> field_simp <;> ring
  have hRa : a ≤ H * a := le_mul_of_one_le_left ha0.le hH
  have hz : q * (ζ + χ) ≤ 2 * w ^ 2 := by
    exact (mul_le_mul hq1 hζχ (by positivity) (by norm_num)).trans (by ring_nf; rfl)
  have hs (C : ℝ) (n j : ℕ) (hC0 : 0 ≤ C) (hC : C ≤ 1000) (hn : n + j ≤ 20) :
      C * R ^ n * w ^ 2 ≤ 1 / R ^ j :=
    tiny_square hR hw0.le hw1 hbudget C n j hC0 hC hn
  have hl (C : ℝ) (n j : ℕ) (hC : C ≤ 1000) (hn : n + j ≤ 20) :
      C * R ^ n * w ≤ 1 / R ^ j := tiny_linear hR hw0.le hbudget C n j hC hn
  have hb2 : w ^ 2 ≤ 1 / R ^ 2 := by
    simpa using hs 1 0 2 (by norm_num) (by norm_num) (by norm_num)
  have hb4 : w ^ 2 ≤ 1 / R ^ 4 := by
    simpa using hs 1 0 4 (by norm_num) (by norm_num) (by norm_num)
  have hdiv4 (x : ℝ) (hx : 0 ≤ x) : x / (4 * D) ≤ x * R ^ 2 / 4 := by
    calc
      x / (4 * D) = (x / 4) * D⁻¹ := by field_simp <;> ring
      _ ≤ (x / 4) * R ^ 2 := mul_le_mul_of_nonneg_left hDinv (by positivity)
      _ = x * R ^ 2 / 4 := by ring
  have hdiv2 (x : ℝ) (hx : 0 ≤ x) : x / (2 * (q * g)) ≤ x * R ^ 4 / 2 := by
    calc
      x / (2 * (q * g)) = (x / 2) * (q * g)⁻¹ := by field_simp <;> ring
      _ ≤ (x / 2) * R ^ 4 := mul_le_mul_of_nonneg_left hqginv (by positivity)
      _ = x * R ^ 4 / 2 := by ring
  have hB2 : R ^ 10 + 1 ≤ 2 * R ^ 10 := by linarith [one_le_pow₀ hR (n := 10)]
  refine {
    q_one := hq1
    chi_q := hχ.trans (hb2.trans hq)
    chi_m := hχ.trans (hb4.trans hqg)
    m_D := hmD
    jitter_quarter := ?_
    jitter_resolved := ?_
    interval_drift := ?_
    mesh_time := ?_
    mesh_intercept := ?_
    shear_intercept := ?_
    mesh_slice := ?_
    shear_slice := ?_
    block_freeze := ?_
    sheet_freeze := ?_
    block_graph := ?_
    sheet_graph := ?_
    key_drift := ?_
    key_freeze := ?_
    affine_sample_budget := ?_
    block_coeff := ?_
    sheet_coeff := ?_ }
  · have := hl 4 0 0 (by norm_num) (by norm_num)
    norm_num at this
    linarith
  · exact (hl 18 10 0 (by norm_num) (by norm_num)).trans (by simpa using hH)
  · have h2w : 2 * w ≤ g := by
      have hb : 2 * w ≤ 1 / R ^ 2 := by simpa using hl 2 0 2 (by norm_num) (by norm_num)
      exact hb.trans hg
    calc
      q * (ζ + χ) ≤ q * (2 * w ^ 2) := mul_le_mul_of_nonneg_left hζχ hq0.le
      _ ≤ q * g * w := by nlinarith only [mul_le_mul_of_nonneg_left h2w (by positivity : 0 ≤ q * w)]
  · have h2m : 2 * mesh ≤ q := by
      exact (mul_le_mul_of_nonneg_left hms (by norm_num)).trans
        ((show 2 * w ^ 2 ≤ 1 / R ^ 2 by simpa using hs 2 0 2 (by norm_num) (by norm_num) (by norm_num)).trans hq)
    linarith
  · linarith
  · have hsmall : 2 * R * w ≤ 1 := by simpa using hl 2 1 0 (by norm_num) (by norm_num)
    calc
      4 * H * mesh ≤ 4 * R * (χ * w) := by gcongr
      _ ≤ 2 * χ := by nlinarith [mul_le_mul_of_nonneg_right hsmall hχ0]
  · have hww : w ^ 2 ≤ q * g :=
      hb4.trans hqg
    calc
      mesh ≤ χ * w := hmχ
      _ ≤ w ^ 2 * w := by gcongr
      _ ≤ q * g * w := by gcongr
  · have h4w : 4 * R * w ^ 2 ≤ q * g :=
      (show 4 * R * w ^ 2 ≤ 1 / R ^ 4 by simpa using hs 4 1 4 (by norm_num) (by norm_num) (by norm_num)).trans hqg
    calc
      4 * H * mesh ≤ 4 * R * (w ^ 2 * w) := by gcongr; exact hmχ.trans (by gcongr)
      _ = (4 * R * w ^ 2) * w := by ring
      _ ≤ q * g * w := by gcongr
  · calc
      3 * R ^ 5 * mesh ≤ 3 * R ^ 5 * w ^ 2 := by gcongr
      _ ≤ 1 / R ^ 2 := hs 3 5 2 (by norm_num) (by norm_num) (by norm_num)
      _ ≤ H * a := ha.trans hRa
  · have hi : 7 * (mesh + (mesh + 4 * H * mesh) / (4 * D)) ≤ a := by
      calc
        _ ≤ 7 * (w ^ 2 + (w ^ 2 + 4 * R * w ^ 2) / (4 * D)) := by gcongr
        _ ≤ 7 * (w ^ 2 + (w ^ 2 + 4 * R * w ^ 2) * R ^ 2 / 4) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add le_rfl (hdiv4 (w ^ 2 + 4 * R * w ^ 2) (by positivity))) (by norm_num)
        _ ≤ 21 * R ^ 3 * w ^ 2 := by
          have h13 : 1 ≤ R ^ 3 := one_le_pow₀ hR
          have h23 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
          nlinarith only [mul_le_mul_of_nonneg_right h13 (by positivity : 0 ≤ w ^ 2),
            mul_le_mul_of_nonneg_right h23 (by positivity : 0 ≤ w ^ 2)]
        _ ≤ 1 / R ^ 2 := hs 21 3 2 (by norm_num) (by norm_num) (by norm_num)
        _ ≤ a := ha
    nlinarith only [mul_le_mul_of_nonneg_left hi hH0]
  · calc
      R ^ 5 * (2 * χ + q * (ζ + χ)) ≤ R ^ 5 * (2 * w ^ 2 + 2 * w ^ 2) := by gcongr
      _ = 4 * R ^ 5 * w ^ 2 := by ring
      _ ≤ 1 / R ^ 2 := hs 4 5 2 (by norm_num) (by norm_num) (by norm_num)
      _ ≤ H * a := ha.trans hRa
  · calc
      7 * H * (q * (ζ + χ)) / (4 * D) ≤ 7 * H * (2 * w ^ 2) / (4 * D) := by gcongr
      _ ≤ 7 * H * (2 * w ^ 2) * R ^ 2 / 4 := by
        exact hdiv4 _ (by positivity)
      _ ≤ H * (4 * R ^ 2 * w ^ 2) := by nlinarith only [mul_nonneg hH0 (mul_nonneg (sq_nonneg R) (sq_nonneg w))]
      _ ≤ H * a := mul_le_mul_of_nonneg_left ((hs 4 2 2 (by norm_num) (by norm_num) (by norm_num)).trans ha) hH0
  · have heq : q * (ζ + χ) / (2 * (q * g)) = (ζ + χ) * g⁻¹ / 2 := by field_simp <;> ring
    rw [heq]
    calc
      (R ^ 10 + 1) * 7 * ((ζ + χ) * g⁻¹ / 2) ≤
          (2 * R ^ 10) * 7 * ((2 * w ^ 2) * R ^ 2 / 2) := by
        gcongr
      _ = 14 * R ^ 12 * w ^ 2 := by ring
      _ ≤ 1 := by simpa using hs 14 12 0 (by norm_num) (by norm_num) (by norm_num)
  · have hp : mesh / q + (1 + 4 * H) * mesh / (2 * (q * g)) ≤ 7 / 2 * R ^ 5 * w ^ 2 := by
      calc
        _ ≤ w ^ 2 * R ^ 2 + (1 + 4 * R) * w ^ 2 * R ^ 4 / 2 := by
          apply add_le_add
          · rw [div_eq_mul_inv]
            exact mul_le_mul hms hqinv (by positivity) (by positivity)
          · exact (hdiv2 _ (by positivity)).trans (by gcongr)
        _ ≤ 7 / 2 * R ^ 5 * w ^ 2 := by
          have h25 : R ^ 2 ≤ R ^ 5 := pow_le_pow_right₀ hR (by norm_num)
          have h45 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR (by norm_num)
          nlinarith only [mul_le_mul_of_nonneg_right h25 (by positivity : 0 ≤ w ^ 2),
            mul_le_mul_of_nonneg_right h45 (by positivity : 0 ≤ w ^ 2)]
    calc
      _ ≤ (2 * R ^ 10) * 7 * (7 / 2 * R ^ 5 * w ^ 2) := by gcongr
      _ = 49 * R ^ 15 * w ^ 2 := by ring
      _ ≤ 1 := by simpa using hs 49 15 0 (by norm_num) (by norm_num) (by norm_num)
  · have hH3 : 0 ≤ H ^ 3 := by positivity
    have h57 : 57 * H ^ 3 ≤ R := by
      have hsq : (57 * H ^ 3) ^ 2 ≤ R ^ 2 := by
        calc
          _ = 3249 * H ^ 6 := by ring
          _ ≤ 3249 * R := by gcongr
          _ ≤ R ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_right (by linarith : (3249 : ℝ) ≤ R) hR0.le]
      nlinarith only [hsq, hH3, hR0]
    have hR4 : 1 ≤ R ^ 4 := one_le_pow₀ hR
    have hHH3 : H ≤ H ^ 3 := by simpa using pow_le_pow_right₀ hH (show 1 ≤ 3 by norm_num)
    have hr4q : a / q ^ 2 ≤ R ^ 4 := by
      rw [div_eq_mul_inv, ← inv_pow]
      exact (mul_le_mul ha1 (pow_le_pow_left₀ (by positivity) hqinv 2) (by positivity) (by norm_num)).trans (by ring_nf; rfl)
    calc
      2 * H + H * a + 3 * (1 + 2 * H) ^ 2 * (H * (1 + a / q ^ 2)) ≤
          3 * H + 3 * (3 * H) ^ 2 * (H * (2 * R ^ 4)) := by
        apply add_le_add
        · nlinarith only [mul_le_mul_of_nonneg_left ha1 hH0]
        · gcongr <;> linarith only [hH, hR4, hr4q]
      _ ≤ 57 * H ^ 3 * R ^ 4 := by
        nlinarith only [mul_le_mul hHH3 hR4 (by norm_num : (0 : ℝ) ≤ 1) hH3]
      _ ≤ R ^ 5 := by nlinarith only [mul_le_mul_of_nonneg_right h57 (by positivity : 0 ≤ R ^ 4)]
  · have haInv : a⁻¹ ≤ R ^ 2 := by
      have := inv_anti₀ (by positivity : 0 < 1 / R ^ 2) ha
      simpa using this
    calc
      8 * (R ^ 5 * (2 + 4 * H + 8 * H) / a) ≤ 8 * (R ^ 5 * (14 * R) * R ^ 2) := by
        rw [div_eq_mul_inv]
        gcongr
        linarith
      _ = 112 * R ^ 8 := by ring
      _ ≤ R ^ 10 := by
        have h112 : 112 ≤ R ^ 2 := (by linarith : (112 : ℝ) ≤ R).trans (by simpa using pow_le_pow_right₀ hR (show 1 ≤ 2 by norm_num))
        nlinarith only [mul_le_mul_of_nonneg_right h112 (by positivity : 0 ≤ R ^ 8)]
  · have haInv : a⁻¹ ≤ R ^ 2 := by
      have := inv_anti₀ (by positivity : 0 < 1 / R ^ 2) ha
      simpa using this
    calc
      88 * H / a ≤ 88 * R * R ^ 2 := by rw [div_eq_mul_inv]; gcongr
      _ = 88 * R ^ 3 := by ring
      _ ≤ R ^ 10 := by
        have h88 : 88 ≤ R ^ 7 := (by linarith : (88 : ℝ) ≤ R).trans
          (by simpa using pow_le_pow_right₀ hR (show 1 ≤ 7 by norm_num))
        nlinarith only [mul_le_mul_of_nonneg_right h88 (by positivity : 0 ≤ R ^ 3)]

end Submission.Obl.k4_wide_three_layer_scalar_inputs
