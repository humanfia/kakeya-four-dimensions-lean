/- Adapted within this LOT tree from o218/x0764, commit 8864b003b22d6433fd04c5290ea5d8356d4fcd89,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/CellLipschitz.lean. -/
import Submission.Obl.k4_horizontal_wide_interval_return.CellFrame

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The moving offset of a residual bin varies little across a fine base cell

For the cap transfer into a true cell, a residual bin `sig ∈ [ρ j, ρ (j+1)]` is the hidden-coordinate
window `X ∈ [o, o + a ρ]` with offset `o = fit + a · P_nc + a ρ j`, which moves with the base
point.  At a point of the cell (`z_t ∈ [0,1]`, `|z_Z|, |U| ≤ H`) and for a second base point at
coordinate distance `≤ δ ≤ q g`, the offset changes by at most `δ (3H + 40 a H³/(q g))`.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return

namespace CellFrame

variable {F : CellFrame}

/-- The variation of the affine fit. -/
theorem fit_sub_le {H δ t Z Y t' Z' Y' : ℝ} (hL : ∀ i, |F.L i| ≤ H)
    (ht : |t - t'| ≤ δ) (hZ : |Z - Z'| ≤ δ) (hY : |Y - Y'| ≤ δ) :
    |F.fit t Z Y - F.fit t' Z' Y'| ≤ 3 * H * δ := by
  have heq : F.fit t Z Y - F.fit t' Z' Y' =
      F.L 1 * (t - t') + F.L 2 * (Z - Z') + F.L 3 * (Y - Y') := by
    unfold fit; ring
  rw [heq]
  calc |F.L 1 * (t - t') + F.L 2 * (Z - Z') + F.L 3 * (Y - Y')|
      ≤ |F.L 1| * |t - t'| + |F.L 2| * |Z - Z'| + |F.L 3| * |Y - Y'| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ H * δ + H * δ + H * δ := by
        have hH : 0 ≤ H := (abs_nonneg _).trans (hL 0)
        gcongr <;> exact hL _
    _ = 3 * H * δ := by ring

/-- The variation of the transverse correction. -/
theorem Pnc_sub_le {H δ t Z Y t' Z' Y' : ℝ} (hH : 1 ≤ H) (hq : 0 < F.q) (hg : 0 < F.g)
    (hg1 : F.g ≤ 1) (hδ : 0 ≤ δ) (hδqg : δ ≤ F.q * F.g)
    (hc : ∀ i, |F.c i| ≤ H) (hC : ∀ i, |F.C i| ≤ H)
    (hzt : F.zt t ∈ Set.Icc (0 : ℝ) 1) (hzZ : |F.zZ t Z| ≤ H) (hU : |F.U t Z Y| ≤ H)
    (ht : |t - t'| ≤ δ) (hZ : |Z - Z'| ≤ δ) (hY : |Y - Y'| ≤ δ) :
    |F.Pnc t Z Y - F.Pnc t' Z' Y'| ≤ 40 * H ^ 3 * δ / (F.q * F.g) := by
  have hqg : 0 < F.q * F.g := mul_pos hq hg
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  set e := δ / (F.q * F.g) with he
  have he0 : 0 ≤ e := div_nonneg hδ hqg.le
  have he1 : e ≤ 1 := (div_le_one hqg).mpr hδqg
  -- coordinate increments
  have hδq : δ / F.q ≤ e := by
    rw [he, div_le_div_iff₀ hq hqg]
    nlinarith [mul_le_mul_of_nonneg_left hg1 (mul_nonneg hδ hq.le)]
  have hdzt : |F.zt t - F.zt t'| ≤ e := by
    have : F.zt t - F.zt t' = (t - t') / F.q := by unfold zt; field_simp; ring
    rw [this, abs_div, abs_of_pos hq]
    exact (div_le_div_of_nonneg_right ht hq.le).trans hδq
  have hdzZ : |F.zZ t Z - F.zZ t' Z'| ≤ 2 * H * e := by
    have : F.zZ t Z - F.zZ t' Z' = ((Z - Z') - (t - t') * F.c 1) / F.q := by
      unfold zZ; field_simp; ring
    rw [this, abs_div, abs_of_pos hq]
    have h1 : |(Z - Z') - (t - t') * F.c 1| ≤ 2 * H * δ := by
      calc |(Z - Z') - (t - t') * F.c 1| ≤ |Z - Z'| + |t - t'| * |F.c 1| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ δ + δ * H := by gcongr; exact hc 1
        _ ≤ 2 * H * δ := by nlinarith
    calc |(Z - Z') - (t - t') * F.c 1| / F.q ≤ 2 * H * δ / F.q :=
          div_le_div_of_nonneg_right h1 hq.le
      _ = 2 * H * (δ / F.q) := by ring
      _ ≤ 2 * H * e := by gcongr
  have hdU : |F.U t Z Y - F.U t' Z' Y'| ≤ 3 * H * e := by
    have : F.U t Z Y - F.U t' Z' Y' =
        ((Y - Y') - (t - t') * F.c 3 - F.c 4 * (Z - Z')) / (F.q * F.g) := by
      unfold U; field_simp; ring
    rw [this, abs_div, abs_of_pos hqg, he, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hqg.le
    calc |(Y - Y') - (t - t') * F.c 3 - F.c 4 * (Z - Z')|
        ≤ |Y - Y'| + |t - t'| * |F.c 3| + |F.c 4| * |Z - Z'| := by
          rw [← abs_mul, ← abs_mul]
          exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ δ + δ * H + H * δ := by gcongr <;> exact hc _
      _ ≤ 3 * H * δ := by nlinarith
  -- values at the second point
  have hzt1 : |F.zt t| ≤ 1 := abs_le.mpr ⟨by linarith [hzt.1], hzt.2⟩
  have hU' : |F.U t' Z' Y'| ≤ 4 * H := by
    have := abs_sub_abs_le_abs_sub (F.U t' Z' Y') (F.U t Z Y)
    rw [abs_sub_comm] at this
    nlinarith
  set α₁ := F.C 0 + F.C 1 * F.zt t + F.C 2 * F.zZ t Z
  set α₁' := F.C 0 + F.C 1 * F.zt t' + F.C 2 * F.zZ t' Z'
  have hα₁ : |α₁| ≤ 3 * H ^ 2 := by
    calc |α₁| ≤ |F.C 0| + |F.C 1| * |F.zt t| + |F.C 2| * |F.zZ t Z| := by
          rw [← abs_mul, ← abs_mul]
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ H + H * 1 + H * H := by gcongr <;> exact hC _
      _ ≤ 3 * H ^ 2 := by nlinarith
  have hdα₁ : |α₁ - α₁'| ≤ 3 * H ^ 2 * e := by
    have : α₁ - α₁' = F.C 1 * (F.zt t - F.zt t') + F.C 2 * (F.zZ t Z - F.zZ t' Z') := by
      simp only [α₁, α₁']; ring
    rw [this]
    calc |F.C 1 * (F.zt t - F.zt t') + F.C 2 * (F.zZ t Z - F.zZ t' Z')|
        ≤ |F.C 1| * |F.zt t - F.zt t'| + |F.C 2| * |F.zZ t Z - F.zZ t' Z'| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ H * e + H * (2 * H * e) := by gcongr <;> exact hC _
      _ ≤ 3 * H ^ 2 * e := by nlinarith [mul_nonneg (mul_nonneg hH0 (sub_nonneg.mpr hH)) he0]
  have hPeq : F.Pnc t Z Y - F.Pnc t' Z' Y' =
      (α₁ - α₁') * F.U t' Z' Y' + α₁ * (F.U t Z Y - F.U t' Z' Y') +
        F.C 3 * (F.U t Z Y - F.U t' Z' Y') * (F.U t Z Y + F.U t' Z' Y') := by
    simp only [Pnc, α₁, α₁']; ring
  rw [hPeq]
  have hsumU : |F.U t Z Y + F.U t' Z' Y'| ≤ 5 * H := by
    calc |F.U t Z Y + F.U t' Z' Y'| ≤ |F.U t Z Y| + |F.U t' Z' Y'| := abs_add_le _ _
      _ ≤ H + 4 * H := add_le_add hU hU'
      _ = 5 * H := by ring
  calc |(α₁ - α₁') * F.U t' Z' Y' + α₁ * (F.U t Z Y - F.U t' Z' Y') +
        F.C 3 * (F.U t Z Y - F.U t' Z' Y') * (F.U t Z Y + F.U t' Z' Y')|
      ≤ |α₁ - α₁'| * |F.U t' Z' Y'| + |α₁| * |F.U t Z Y - F.U t' Z' Y'| +
          |F.C 3| * |F.U t Z Y - F.U t' Z' Y'| * |F.U t Z Y + F.U t' Z' Y'| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (3 * H ^ 2 * e) * (4 * H) + (3 * H ^ 2) * (3 * H * e) + H * (3 * H * e) * (5 * H) := by
        gcongr; exact hC _
    _ = 36 * H ^ 3 * e := by ring
    _ ≤ 40 * H ^ 3 * δ / (F.q * F.g) := by
        rw [he, mul_div_assoc]
        gcongr
        norm_num

end CellFrame

end Submission.Obl.k4_horizontal_wide_interval_return
