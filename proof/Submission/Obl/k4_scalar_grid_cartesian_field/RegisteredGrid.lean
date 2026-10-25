import Mathlib

namespace Submission.Obl.k4_scalar_grid_cartesian_field

/-- Round an exponent upward to the exact registered grid, with one grid-step error. -/
theorem exists_registered_exponent {M : ℕ} (hM : 1 ≤ M) {r : ℝ} (hr : 0 ≤ r) :
    ∃ m : ℕ, r ≤ (m : ℝ) / M ∧ (m : ℝ) / M ≤ r + 1 / M := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  refine ⟨⌈r * M⌉₊, ?_, ?_⟩
  · exact (le_div_iff₀ hMp).mpr (Nat.le_ceil _)
  · apply (div_le_iff₀ hMp).mpr
    have hc : (⌈r * M⌉₊ : ℝ) ≤ r * M + 1 :=
      (Nat.ceil_lt_add_one (mul_nonneg hr hMp.le)).le
    have heq : (r + 1 / (M : ℝ)) * M = r * M + 1 := by field_simp
    rwa [heq]

/-- Rounding to the preparation grid changes a physical width by at most its supplied loss. -/
theorem registered_width_comparison {N H M r r' : ℝ} (hN : 1 ≤ N) (_hM : 0 < M)
    (hstep : N ^ (1 / M) ≤ H) (hlo : r ≤ r') (hhi : r' ≤ r + 1 / M) :
    N ^ (-r') ≤ N ^ (-r) ∧ N ^ (-r) ≤ H * N ^ (-r') := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  refine ⟨Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hlo), ?_⟩
  calc
    _ = N ^ (r' - r) * N ^ (-r') := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    _ ≤ N ^ (1 / M) * N ^ (-r') := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNp.le _)
      exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg hNp.le _)

/-- Every physical width in a fixed exponent interval has a nearby registered width. -/
theorem exists_registered_width {N H : ℝ} (hN : 1 < N) {M : ℕ}
    (hM : 1 ≤ M) (hstep : N ^ (1 / (M : ℝ)) ≤ H)
    {w : ℝ} (hwlo : N ^ (-2 : ℝ) ≤ w) (hwhi : w ≤ N ^ (-1 : ℝ)) :
    ∃ (r : ℝ) (m : ℕ), 1 ≤ r ∧ r ≤ 3 ∧ r = (m : ℝ) / M ∧
      N ^ (-r) ≤ w ∧ w ≤ H * N ^ (-r) := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hw : 0 < w := (Real.rpow_pos_of_pos hNp _).trans_le hwlo
  let r₀ := -Real.logb N w
  have hr₀lo : 1 ≤ r₀ := by
    have hx : Real.logb N w ≤ (-1 : ℝ) := (Real.logb_le_iff_le_rpow hN hw).mpr hwhi
    dsimp [r₀]
    linarith
  have hr₀hi : r₀ ≤ 2 := by
    have hx : (-2 : ℝ) ≤ Real.logb N w := (Real.le_logb_iff_rpow_le hN hw).mpr hwlo
    dsimp [r₀]
    linarith
  have heq : N ^ (-r₀) = w := by
    dsimp [r₀]
    rw [neg_neg]
    exact Real.rpow_logb hNp hN.ne' hw
  obtain ⟨m, hmlo, hmhi⟩ := exists_registered_exponent hM (by linarith : 0 ≤ r₀)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hone : (1 : ℝ) / M ≤ 1 := by
    exact (div_le_one hMp).mpr (by exact_mod_cast hM)
  obtain ⟨hwfine, hwround⟩ := registered_width_comparison hN.le hMp hstep hmlo hmhi
  refine ⟨(m : ℝ) / M, m, hr₀lo.trans hmlo, ?_, rfl, ?_, ?_⟩
  · linarith
  · simpa only [heq] using hwfine
  · simpa only [heq] using hwround

/-- A physical width within a subpower factor gives the same hidden-dimensional count. -/
theorem rounded_width_rpow_bound {δ b w H d : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hw : 0 < w) (hH : 1 ≤ H)
    (hd : 0 ≤ d) (hdone : d ≤ 1) (hround : w ≤ H * b) :
    (δ / b) ^ d ≤ H * (δ / w) ^ d := by
  have hratio : δ / b ≤ H * (δ / w) := by
    apply (div_le_iff₀ hb).mpr
    have hid : H * (δ / w) * b = δ * (H * b) / w := by ring
    rw [hid]
    exact (le_div_iff₀ hw).mpr (by nlinarith)
  calc
    _ ≤ (H * (δ / w)) ^ d := Real.rpow_le_rpow (div_nonneg hδ.le hb.le) hratio hd
    _ = H ^ d * (δ / w) ^ d := Real.mul_rpow (by linarith) (div_nonneg hδ.le hw.le)
    _ ≤ H ^ (1 : ℝ) * (δ / w) ^ d := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hH hdone) (by positivity)
    _ = _ := by rw [Real.rpow_one]

/-- Convert the preparation's exponent count to a ratio of physical widths. -/
theorem hereditary_exponent_eq_width_ratio {N : ℝ} (hN : 0 < N) (r d : ℝ) :
    N ^ ((2 + d) * (r - 1)) = (N ^ (-1 : ℝ) / N ^ (-r)) ^ (2 + d) := by
  rw [← Real.rpow_sub hN, ← Real.rpow_mul hN.le]
  congr 1
  ring

/-- The two base dimensions cancel against the coarse graph-cell count. -/
theorem hereditary_ratio_identity {h δ b : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hb : 0 < b) (d : ℝ) :
    (h / δ) ^ 2 * (δ / b) ^ (2 + d) = (h / b) ^ 2 * (δ / b) ^ d := by
  rw [Real.rpow_add (div_pos hδ hb), Real.rpow_two]
  field_simp

/-- The frozen horizon comparison gives a fixed compact exponent range for hidden widths. -/
theorem packet_horizon_lower_fixed_power {N K κ h : ℝ} (hN : 2 ≤ N) (hK : 0 < K)
    (hKN : K ≤ N) (hκ : κ ≤ 1) (hscale : N ^ (-κ) / K ≤ h) : N ^ (-2 : ℝ) ≤ h := by
  have hNp : 0 < N := by linarith
  have hnum : N ^ (-1 : ℝ) ≤ N ^ (-κ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) (by linarith)
  calc
    _ = N ^ ((-1 : ℝ) - 1) := by norm_num
    _ = N ^ (-1 : ℝ) / N ^ (1 : ℝ) := Real.rpow_sub hNp _ _
    _ = N ^ (-1 : ℝ) / N := by rw [Real.rpow_one]
    _ ≤ N ^ (-κ) / N := div_le_div_of_nonneg_right hnum hNp.le
    _ ≤ N ^ (-κ) / K := div_le_div_of_nonneg_left (Real.rpow_nonneg hNp.le _) hK hKN
    _ ≤ _ := hscale

/-- Every hidden width in the frozen interval lies in exponents between one and two. -/
theorem hidden_width_fixed_range {N h w : ℝ} (hN : 2 ≤ N) (hh : N ^ (-2 : ℝ) ≤ h)
    (hw : N ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8) ≤ w) : N ^ (-2 : ℝ) ≤ w := by
  have hNp : 0 < N := by linarith
  have hhpos : 0 < h := (Real.rpow_pos_of_pos hNp _).trans_le hh
  calc
    _ ≤ N ^ (-(5 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = N ^ (-1 : ℝ) * (N ^ (-2 : ℝ)) ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_mul hNp.le, ← Real.rpow_add hNp]
      congr 1
      norm_num
    _ ≤ N ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8) := by
      gcongr
    _ ≤ _ := hw

/-- The final fine base mesh is finer than every registered width used for joint support. -/
theorem fine_base_mesh_small {N h : ℝ} (hN : 1 ≤ N) (hh : h ≤ 1) :
    h * N ^ (-10 : ℝ) ≤ N ^ (-3 : ℝ) := by
  calc
    _ ≤ 1 * N ^ (-10 : ℝ) := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (by linarith) _)
    _ = N ^ (-10 : ℝ) := one_mul _
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)

end Submission.Obl.k4_scalar_grid_cartesian_field
