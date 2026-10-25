/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameSlopeBounds.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameChain

/-!
# Slope bounds of every residual level

The crude pass at the root level, the crude passes at every level (to bound
the parent coefficients that confine the fine passes), the fine passes and the
chain give the slope bounds `FrameSlopes` at every level, under explicit
numerical conditions on the mesh exponents `r₁` (crude) and `r₂` (fine).
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

/-- The calibration constant of a pass. -/
def passA (A₀ bK Cr Φ K θ Y : ℝ) : ℝ :=
  A₀ * (1 + bK) ^ A₀ * (1 + 16 * (8 * bK + 4) * Cr * Φ * K ^ 5 / θ ^ 2 * Y) ^ (6 : ℕ)

theorem passA_nonneg {A₀ bK Cr Φ K θ Y : ℝ} (hA₀ : 0 ≤ A₀) (hbK : 0 ≤ bK) (hCr : 0 ≤ Cr)
    (hΦ : 0 ≤ Φ) (hK : 0 ≤ K) (hY : 0 ≤ Y) : 0 ≤ passA A₀ bK Cr Φ K θ Y := by
  unfold passA
  positivity

theorem passA_mono {A₀ bK Cr Φ K θ Y Y' : ℝ} (hA₀ : 0 ≤ A₀) (hbK : 0 ≤ bK) (hCr : 0 ≤ Cr)
    (hΦ : 0 ≤ Φ) (hK : 0 ≤ K) (hY : 0 ≤ Y) (hYY : Y ≤ Y') :
    passA A₀ bK Cr Φ K θ Y ≤ passA A₀ bK Cr Φ K θ Y' := by
  unfold passA
  gcongr

theorem rpow_le_one_add_rpow {N c x y : ℝ} (hN : 1 ≤ N) (hx : 0 ≤ x) (hxy : x ≤ y) :
    N ^ (c * x) ≤ 1 + N ^ (c * y) := by
  have hy : 0 ≤ N ^ (c * y) := Real.rpow_nonneg (by linarith) _
  rcases le_or_gt 0 c with hc | hc
  · have : N ^ (c * x) ≤ N ^ (c * y) :=
      Real.rpow_le_rpow_of_exponent_le hN (mul_le_mul_of_nonneg_left hxy hc)
    linarith
  · have : N ^ (c * x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith)
    linarith

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

theorem FrameGood.level_nonneg (hg : FrameGood f Rk θ K₂ e₀') (h : ℕ) :
    0 ≤ (h : ℝ) * (U' / f.m) := by
  have := hg.U'_pos
  have : (0 : ℝ) < f.m := by exact_mod_cast hg.m_pos
  positivity

theorem FrameGood.level_le (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    (h : ℝ) * (U' / f.m) ≤ U' := by
  have hm : (0 : ℝ) < f.m := by exact_mod_cast hg.m_pos
  have hh' : (h : ℝ) ≤ f.m := by exact_mod_cast hh
  have hU := hg.U'_pos
  calc (h : ℝ) * (U' / f.m) ≤ f.m * (U' / f.m) := by gcongr
    _ = U' := by field_simp

theorem FrameGood.inv_resq_le (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    (f.resq h)⁻¹ ≤ D.K k ^ 2 * D.N k ^ (D.κ * ((h : ℝ) * (U' / f.m))) := by
  rw [Frame.resq, zpow_neg, zpow_natCast, inv_inv]
  exact (hg.res_count hh).2

theorem FrameGood.inv_resq_sq_le (hg : FrameGood f Rk θ K₂ e₀') (hκ : D.κ ≤ 1) {h : ℕ}
    (hh : h ≤ f.m) : (f.resq h ^ 2)⁻¹ ≤ D.K k ^ 4 * D.N k ^ (2 * U') := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hN1 : 1 ≤ D.N k := by linarith [hg.N_ge]
  have h1 := hg.inv_resq_le hh
  have hx := hg.level_nonneg h
  have hxU := hg.level_le hh
  have hκ0 := hg.κ_pos
  have hq := f.resq_pos h
  have h2 : D.N k ^ (D.κ * ((h : ℝ) * (U' / f.m))) ≤ D.N k ^ U' :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
  have h3 : (f.resq h)⁻¹ ≤ D.K k ^ 2 * D.N k ^ U' := h1.trans (by gcongr)
  have e : (D.N k ^ U') ^ 2 = D.N k ^ (2 * U') := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    push_cast
    ring
  rw [← inv_pow]
  calc (f.resq h)⁻¹ ^ 2 ≤ (D.K k ^ 2 * D.N k ^ U') ^ 2 := by gcongr
    _ = D.K k ^ 4 * D.N k ^ (2 * U') := by rw [mul_pow, e]; ring

/-- The second-order level ratio is controlled by the last level. -/
theorem FrameGood.ratio_two (hg : FrameGood f Rk θ K₂ e₀') {g h' : ℕ} (hgh : g < h')
    (hh' : h' ≤ f.m) :
    D.N k ^ (-((g : ℝ) * (U' / f.m))) / f.resq (g + 1) ^ 2 ≤
      D.N k ^ (U' / f.m) * D.K k ^ 8 *
        (1 + D.N k ^ (-((h' : ℝ) * (U' / f.m))) / f.resq h' ^ 2) := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hN1 : 1 ≤ D.N k := by linarith [hg.N_ge]
  have hK1 : 1 ≤ D.K k := hg.K_ge
  have hg1 : g + 1 ≤ f.m := by omega
  have hx := hg.level_nonneg (g + 1)
  have hη : 0 ≤ U' / f.m := by
    have := hg.U'_pos
    have : (0 : ℝ) < f.m := by exact_mod_cast hg.m_pos
    positivity
  have hxy : ((g + 1 : ℕ) : ℝ) * (U' / f.m) ≤ (h' : ℝ) * (U' / f.m) := by
    have : ((g + 1 : ℕ) : ℝ) ≤ h' := by exact_mod_cast hgh
    exact mul_le_mul_of_nonneg_right this hη
  have hq1 := f.resq_pos (g + 1)
  have hq2 := f.resq_pos h'
  have hP := hg.inv_resq_le hg1
  have hQ : D.N k ^ (D.κ * ((h' : ℝ) * (U' / f.m))) ≤ D.K k ^ 2 * (f.resq h')⁻¹ := by
    have := (hg.res_count hh').1
    rw [div_le_iff₀ (by positivity)] at this
    rw [Frame.resq, zpow_neg, zpow_natCast, inv_inv]
    linarith
  have e1 : D.N k ^ (-((g : ℝ) * (U' / f.m))) =
      D.N k ^ (U' / f.m) * D.N k ^ (-(((g + 1 : ℕ) : ℝ) * (U' / f.m))) := by
    rw [← Real.rpow_add hN]
    congr 1
    push_cast
    ring
  have e2 : D.N k ^ (-(((g + 1 : ℕ) : ℝ) * (U' / f.m))) *
      (D.N k ^ (D.κ * (((g + 1 : ℕ) : ℝ) * (U' / f.m)))) ^ 2 =
      D.N k ^ ((2 * D.κ - 1) * (((g + 1 : ℕ) : ℝ) * (U' / f.m))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1
    push_cast
    ring
  have e3 : D.N k ^ ((2 * D.κ - 1) * ((h' : ℝ) * (U' / f.m))) =
      D.N k ^ (-((h' : ℝ) * (U' / f.m))) *
        (D.N k ^ (D.κ * ((h' : ℝ) * (U' / f.m)))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1
    push_cast
    ring
  have hcmp := rpow_le_one_add_rpow (c := 2 * D.κ - 1) hN1 hx hxy
  rw [div_eq_mul_inv, ← inv_pow, e1]
  calc D.N k ^ (U' / f.m) * D.N k ^ (-(((g + 1 : ℕ) : ℝ) * (U' / f.m))) *
        (f.resq (g + 1))⁻¹ ^ 2
      ≤ D.N k ^ (U' / f.m) * D.N k ^ (-(((g + 1 : ℕ) : ℝ) * (U' / f.m))) *
          (D.K k ^ 2 * D.N k ^ (D.κ * (((g + 1 : ℕ) : ℝ) * (U' / f.m)))) ^ 2 := by gcongr
    _ = D.N k ^ (U' / f.m) * D.K k ^ 4 *
          (D.N k ^ (-(((g + 1 : ℕ) : ℝ) * (U' / f.m))) *
            (D.N k ^ (D.κ * (((g + 1 : ℕ) : ℝ) * (U' / f.m)))) ^ 2) := by ring
    _ = D.N k ^ (U' / f.m) * D.K k ^ 4 *
          D.N k ^ ((2 * D.κ - 1) * (((g + 1 : ℕ) : ℝ) * (U' / f.m))) := by rw [e2]
    _ ≤ D.N k ^ (U' / f.m) * D.K k ^ 4 *
          (1 + D.N k ^ ((2 * D.κ - 1) * ((h' : ℝ) * (U' / f.m)))) := by gcongr
    _ ≤ D.N k ^ (U' / f.m) * D.K k ^ 4 *
          (1 + D.N k ^ (-((h' : ℝ) * (U' / f.m))) * (D.K k ^ 2 * (f.resq h')⁻¹) ^ 2) := by
        rw [e3]
        gcongr
    _ = D.N k ^ (U' / f.m) * (D.K k ^ 4 + D.K k ^ 8 *
          (D.N k ^ (-((h' : ℝ) * (U' / f.m))) * ((f.resq h')⁻¹) ^ 2)) := by ring
    _ ≤ D.N k ^ (U' / f.m) * (D.K k ^ 8 + D.K k ^ 8 *
          (D.N k ^ (-((h' : ℝ) * (U' / f.m))) * ((f.resq h')⁻¹) ^ 2)) := by
        have hK48 : D.K k ^ 4 ≤ D.K k ^ 8 := pow_le_pow_right₀ hK1 (by norm_num)
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = D.N k ^ (U' / f.m) * D.K k ^ 8 *
          (1 + D.N k ^ (-((h' : ℝ) * (U' / f.m))) / f.resq h' ^ 2) := by
        simp only [div_eq_mul_inv, inv_pow]
        ring

/-- The first-order level ratio is bounded. -/
theorem FrameGood.ratio_one (hg : FrameGood f Rk θ K₂ e₀') (hκ : D.κ ≤ 1) {g : ℕ}
    (hg' : g < f.m) :
    D.N k ^ (-((g : ℝ) * (U' / f.m))) / f.resq (g + 1) ≤ D.N k ^ (U' / f.m) * D.K k ^ 2 := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hN1 : 1 ≤ D.N k := by linarith [hg.N_ge]
  have hx := hg.level_nonneg (g + 1)
  have hq1 := f.resq_pos (g + 1)
  have hP := hg.inv_resq_le (show g + 1 ≤ f.m by omega)
  have e1 : D.N k ^ (-((g : ℝ) * (U' / f.m))) =
      D.N k ^ (U' / f.m) * D.N k ^ (-(((g + 1 : ℕ) : ℝ) * (U' / f.m))) := by
    rw [← Real.rpow_add hN]
    congr 1
    push_cast
    ring
  have e2 : D.N k ^ (-(((g + 1 : ℕ) : ℝ) * (U' / f.m))) *
      D.N k ^ (D.κ * (((g + 1 : ℕ) : ℝ) * (U' / f.m))) =
      D.N k ^ ((D.κ - 1) * (((g + 1 : ℕ) : ℝ) * (U' / f.m))) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have h1 : D.N k ^ ((D.κ - 1) * (((g + 1 : ℕ) : ℝ) * (U' / f.m))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith)
  rw [div_eq_mul_inv, e1]
  calc D.N k ^ (U' / f.m) * D.N k ^ (-(((g + 1 : ℕ) : ℝ) * (U' / f.m))) *
        (f.resq (g + 1))⁻¹
      ≤ D.N k ^ (U' / f.m) * D.N k ^ (-(((g + 1 : ℕ) : ℝ) * (U' / f.m))) *
          (D.K k ^ 2 * D.N k ^ (D.κ * (((g + 1 : ℕ) : ℝ) * (U' / f.m)))) := by gcongr
    _ = D.N k ^ (U' / f.m) * D.K k ^ 2 *
          (D.N k ^ (-(((g + 1 : ℕ) : ℝ) * (U' / f.m))) *
            D.N k ^ (D.κ * (((g + 1 : ℕ) : ℝ) * (U' / f.m)))) := by ring
    _ ≤ D.N k ^ (U' / f.m) * D.K k ^ 2 * 1 := by rw [e2]; gcongr
    _ = _ := mul_one _

theorem chain_final_three {a w x M c ρ L : ℝ} (ha : 0 ≤ a) (hw : 0 ≤ w) (hx : 0 ≤ x)
    (hxM : x ≤ M) (hc : 1 ≤ c) (hρ : 0 ≤ ρ) (hL : L ≤ a + x * (w * (1 + ρ))) :
    L ≤ c * (a + M * w) * (1 + ρ) := by
  have h1 : 0 ≤ (c - 1) * ((a + M * w) * (1 + ρ)) :=
    mul_nonneg (by linarith) (mul_nonneg (by nlinarith) (by linarith))
  have h2 : 0 ≤ a * ρ := mul_nonneg ha hρ
  have h3 : 0 ≤ (M - x) * (w * (1 + ρ)) :=
    mul_nonneg (by linarith) (mul_nonneg hw (by linarith))
  nlinarith

theorem chain_final_one {a w w₁ x M c ρ L : ℝ} (ha : 0 ≤ a) (hw₁ : 0 ≤ w₁) (hw₁w : w₁ ≤ w)
    (hx : 0 ≤ x) (hxM : x ≤ M) (hc : 0 ≤ c) (hρ : 0 ≤ ρ)
    (hL : L ≤ c * a + x * (c * w₁)) : L ≤ c * (a + M * w) * (1 + ρ) := by
  have h1 : 0 ≤ c * ((a + M * w) * ρ) :=
    mul_nonneg hc (mul_nonneg (by nlinarith) hρ)
  have h2 : 0 ≤ c * ((M - x) * w) := mul_nonneg hc (mul_nonneg (by linarith) (by linarith))
  have h3 : 0 ≤ c * (x * (w - w₁)) := mul_nonneg hc (mul_nonneg hx (by linarith))
  nlinarith

/-- The slope bounds at every level, from the residual caps of the frame. -/
theorem FrameGood.frameSlopes (hg : FrameGood f Rk θ K₂ e₀') (hκ : D.κ ≤ 1) {A₀ : ℝ}
    (hA₀ : 1 ≤ A₀) (hA : BoxCalibration A₀) {Cr R r₁ r₂ : ℝ} (hCr : 0 < Cr)
    (hcaps : f.CapsAt Cr R) (hr₁ : R⁻¹ ≤ r₁) (hr₁' : r₁ ≤ R) (hr₂ : R⁻¹ ≤ r₂)
    (hr₂' : r₂ ≤ R) (hUR : U' ≤ R)
    (hc1 : passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ (D.N k ^ (D.d * U')) *
      (D.K k ^ 4 * D.N k ^ (2 * U')) * D.N k ^ (-r₁) ≤ 1 / 2)
    (hc2 : 3 * (1 + boxK (D.K k) K₂) * (passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ
      (D.N k ^ (D.d * U')) * (2 * f.H)) * (D.K k ^ 4 * D.N k ^ (2 * U')) * D.N k ^ (-r₂) ≤
        D.N k ^ (-U'))
    (hc3 : passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
      (D.N k ^ (D.d * (U' / f.m))) * (D.K k ^ 4 * D.N k ^ (2 * U')) * D.N k ^ (-r₂) ≤ 1 / 2)
    {h : ℕ} (hh : h ≤ f.m) :
    FrameSlopes f h ((3 + 13 * D.K k ^ 4 * K₂ ^ 2) *
      (passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ 1 * (2 * f.H) +
        f.m * (passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
          (D.N k ^ (D.d * (U' / f.m))) * (2 * f.H) * (D.N k ^ (U' / f.m) * D.K k ^ 8)))) := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hN1 : 1 ≤ D.N k := by linarith [hg.N_ge]
  have hK : 1 ≤ D.K k := hg.K_ge
  have hK0 : 0 ≤ D.K k := by linarith
  have hK₂ : 1 ≤ K₂ := hg.K₂_ge
  have hH : 1 ≤ f.H := hg.H_ge
  have hd := hg.d_nonneg
  have hU := hg.U'_pos
  have hR0 : 0 ≤ R := by linarith
  have hA₀0 : 0 ≤ A₀ := by linarith
  have hbK := one_le_boxK hK hK₂
  have hbK0 : 0 ≤ boxK (D.K k) K₂ := by linarith
  have hm0 : (0 : ℝ) < f.m := by exact_mod_cast hg.m_pos
  have hη : 0 ≤ U' / f.m := by positivity
  have hA₁0 : 0 ≤ passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ 1 :=
    passA_nonneg hA₀0 hbK0 hCr.le (by linarith) hK0 zero_le_one
  have hA₂0 : 0 ≤ passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
      (D.N k ^ (D.d * (U' / f.m))) :=
    passA_nonneg hA₀0 hbK0 hCr.le (by linarith) hK0 (by positivity)
  have hAc0 : 0 ≤ passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ
      (D.N k ^ (D.d * U')) :=
    passA_nonneg hA₀0 hbK0 hCr.le (by linarith) hK0 (by positivity)
  have hNdU : 1 ≤ D.N k ^ (D.d * U') := Real.one_le_rpow hN1 (by positivity)
  have hA₁c : passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ 1 ≤
      passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ (D.N k ^ (D.d * U')) :=
    passA_mono hA₀0 hbK0 hCr.le (by linarith) hK0 zero_le_one hNdU
  have hmesh : ∀ g ≤ f.m, ∀ r : ℝ, D.N k ^ (-r) / f.resq g ^ 2 ≤
      (D.K k ^ 4 * D.N k ^ (2 * U')) * D.N k ^ (-r) := by
    intro g hg' r
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (hg.inv_resq_sq_le hκ hg') (by positivity)
  -- crude passes at every level
  have hcrude : ∀ g (hg' : g ≤ f.m) (i : Fin (f.retained g).card),
      f.resq g * |f.labelL g i 1 - f.boxZ g i * f.labelL g i 3| ≤
        passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ (D.N k ^ (D.d * U')) *
          (2 * f.H) ∧
      f.resq g * |f.labelL g i 2 + f.resMid g i * f.labelL g i 3| ≤
        passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ (D.N k ^ (D.d * U')) *
          (2 * f.H) ∧
      f.resq g ^ 2 * |f.labelL g i 3| ≤
        passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ (D.N k ^ (D.d * U')) *
          (2 * f.H) := by
    intro g hg' i
    refine hg.crude_pass hA hCr hcaps hg' i hr₁ hr₁' hR0 ?_ ?_
    · exact passA_mono hA₀0 hbK0 hCr.le (by linarith) hK0 (by positivity)
        (Real.rpow_le_rpow_of_exponent_le hN1
          (mul_le_mul_of_nonneg_left (hg.level_le hg') hd))
    · calc _ ≤ passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ (D.N k ^ (D.d * U')) *
            ((D.K k ^ 4 * D.N k ^ (2 * U')) * D.N k ^ (-r₁)) :=
          mul_le_mul_of_nonneg_left (hmesh g hg' r₁) hAc0
        _ ≤ 1 / 2 := by rw [← mul_assoc]; exact hc1
  -- the root level with the sharp constant
  have h0 : ∀ i : Fin (f.retained 0).card,
      f.resq 0 * |f.labelL 0 i 1 - f.boxZ 0 i * f.labelL 0 i 3| ≤
        passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ 1 * (2 * f.H) ∧
      f.resq 0 * |f.labelL 0 i 2 + f.resMid 0 i * f.labelL 0 i 3| ≤
        passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ 1 * (2 * f.H) ∧
      f.resq 0 ^ 2 * |f.labelL 0 i 3| ≤
        passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ 1 * (2 * f.H) := by
    intro i
    refine hg.crude_pass hA hCr hcaps (Nat.zero_le _) i hr₁ hr₁' hR0 ?_ ?_
    · simp only [Nat.cast_zero, zero_mul, mul_zero, Real.rpow_zero]
      exact le_rfl
    · calc _ ≤ passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ (D.N k ^ (D.d * U')) *
            ((D.K k ^ 4 * D.N k ^ (2 * U')) * D.N k ^ (-r₁)) :=
          mul_le_mul hA₁c (hmesh 0 (Nat.zero_le _) r₁) (by positivity) hAc0
        _ ≤ 1 / 2 := by rw [← mul_assoc]; exact hc1
  -- coefficient bounds of every label
  have hΛ : ∀ g (hg' : g ≤ f.m) (i : Fin (f.retained g).card),
      |f.labelL g i 1| + |f.labelL g i 2| + |f.labelL g i 3| ≤
        3 * (1 + boxK (D.K k) K₂) * (passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 2) (D.K k) θ
          (D.N k ^ (D.d * U')) * (2 * f.H)) * (D.K k ^ 4 * D.N k ^ (2 * U')) := by
    intro g hg' i
    obtain ⟨c1, c2, c3⟩ := hcrude g hg' i
    have hb := coeff_sum_le_of_box (f.resq_pos g) (f.resq_le_one g) (hg.abs_boxZ hg' i)
      (hg.abs_resMid i) (by positivity) c1 c2 c3
    refine hb.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hg.inv_resq_sq_le hκ hg') (by positivity)
  -- fine passes
  have hstep : ∀ (g : ℕ) (hg' : g < f.m) (i : Fin (f.retained (g + 1)).card),
      f.resq (g + 1) * |(f.labelL (g + 1) i - f.labelL g (f.upLabel hg hg' i)) 1 -
          f.boxZ (g + 1) i * (f.labelL (g + 1) i - f.labelL g (f.upLabel hg hg' i)) 3| ≤
          passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
            (D.N k ^ (D.d * (U' / f.m))) * (2 * f.H * D.N k ^ (-((g : ℝ) * (U' / f.m)))) ∧
        f.resq (g + 1) * |(f.labelL (g + 1) i - f.labelL g (f.upLabel hg hg' i)) 2 +
          f.resMid (g + 1) i * (f.labelL (g + 1) i - f.labelL g (f.upLabel hg hg' i)) 3| ≤
          passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
            (D.N k ^ (D.d * (U' / f.m))) * (2 * f.H * D.N k ^ (-((g : ℝ) * (U' / f.m)))) ∧
        f.resq (g + 1) ^ 2 * |(f.labelL (g + 1) i - f.labelL g (f.upLabel hg hg' i)) 3| ≤
          passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
            (D.N k ^ (D.d * (U' / f.m))) * (2 * f.H * D.N k ^ (-((g : ℝ) * (U' / f.m)))) := by
    intro g hg' i
    refine hg.fine_pass (A := passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
      (D.N k ^ (D.d * (U' / f.m)))) hA hCr hcaps hg' i hr₂ hr₂'
      ((hg.level_le hg'.le).trans hUR) (hΛ g hg'.le _) ?_ le_rfl ?_
    · refine hc2.trans ?_
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hg.level_le hg'.le])
    · calc _ ≤ passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
            (D.N k ^ (D.d * (U' / f.m))) * ((D.K k ^ 4 * D.N k ^ (2 * U')) * D.N k ^ (-r₂)) :=
          mul_le_mul_of_nonneg_left (hmesh (g + 1) hg' r₂) hA₂0
        _ ≤ 1 / 2 := by rw [← mul_assoc]; exact hc3
  have hq := f.resq_pos h
  have hρ2 : 0 ≤ D.N k ^ (-((h : ℝ) * (U' / f.m))) / f.resq h ^ 2 := by positivity
  have hρ1 : 0 ≤ D.N k ^ (-((h : ℝ) * (U' / f.m))) / f.resq h := by positivity
  have hBx : 0 ≤ 13 * D.K k ^ 4 * K₂ ^ 2 := by positivity
  have hw₁ : 0 ≤ passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
      (D.N k ^ (D.d * (U' / f.m))) * (2 * f.H) * (D.N k ^ (U' / f.m) * D.K k ^ 2) := by
    positivity
  have hw₁w : passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
      (D.N k ^ (D.d * (U' / f.m))) * (2 * f.H) * (D.N k ^ (U' / f.m) * D.K k ^ 2) ≤
      passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
      (D.N k ^ (D.d * (U' / f.m))) * (2 * f.H) * (D.N k ^ (U' / f.m) * D.K k ^ 8) := by
    have : D.K k ^ 2 ≤ D.K k ^ 8 := pow_le_pow_right₀ hK (by norm_num)
    gcongr
  have hchain := hg.slope_chain (by positivity) hA₂0 h0 hstep hh
    (W3 := passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ
      (D.N k ^ (D.d * (U' / f.m))) * (2 * f.H) * (D.N k ^ (U' / f.m) * D.K k ^ 8) *
        (1 + D.N k ^ (-((h : ℝ) * (U' / f.m))) / f.resq h ^ 2))
    (W1 := (3 + 13 * D.K k ^ 4 * K₂ ^ 2) * (passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6)
      (D.K k) θ (D.N k ^ (D.d * (U' / f.m))) * (2 * f.H) * (D.N k ^ (U' / f.m) * D.K k ^ 2)))
    ?_ ?_ h le_rfl
  · intro i
    obtain ⟨c3, c1⟩ := hchain i
    have hxM : (h : ℝ) ≤ f.m := by exact_mod_cast hh
    refine ⟨?_, fun l hl t ht => ?_⟩
    · exact chain_final_three (ρ := D.N k ^ (-((h : ℝ) * (U' / f.m))) / f.resq h ^ 2)
        (by positivity) (by positivity) (Nat.cast_nonneg _) hxM (by linarith) hρ2 c3
    · exact chain_final_one (ρ := D.N k ^ (-((h : ℝ) * (U' / f.m))) / f.resq h)
        (by positivity) hw₁ hw₁w (Nat.cast_nonneg _) hxM (by positivity) hρ1
        (c1 (l, t) ⟨hl, ht⟩)
  · intro g hgh
    have hr := hg.ratio_two hgh hh
    calc passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ (D.N k ^ (D.d * (U' / f.m))) *
          (2 * f.H * D.N k ^ (-((g : ℝ) * (U' / f.m)))) / f.resq (g + 1) ^ 2
        = passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6) (D.K k) θ (D.N k ^ (D.d * (U' / f.m))) *
          (2 * f.H) * (D.N k ^ (-((g : ℝ) * (U' / f.m))) / f.resq (g + 1) ^ 2) := by ring
      _ ≤ _ := by
        rw [mul_assoc _ (D.N k ^ (U' / f.m) * D.K k ^ 8)]
        exact mul_le_mul_of_nonneg_left hr (by positivity)
  · intro g hgh
    have hr := hg.ratio_one hκ (lt_of_lt_of_le hgh hh)
    calc (3 + 13 * D.K k ^ 4 * K₂ ^ 2) * (passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6)
          (D.K k) θ (D.N k ^ (D.d * (U' / f.m))) *
          (2 * f.H * D.N k ^ (-((g : ℝ) * (U' / f.m))))) / f.resq (g + 1)
        = (3 + 13 * D.K k ^ 4 * K₂ ^ 2) * (passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6)
          (D.K k) θ (D.N k ^ (D.d * (U' / f.m))) * (2 * f.H)) *
          (D.N k ^ (-((g : ℝ) * (U' / f.m))) / f.resq (g + 1)) := by ring
      _ ≤ (3 + 13 * D.K k ^ 4 * K₂ ^ 2) * (passA A₀ (boxK (D.K k) K₂) Cr (4 * f.H + 6)
          (D.K k) θ (D.N k ^ (D.d * (U' / f.m))) * (2 * f.H)) *
          (D.N k ^ (U' / f.m) * D.K k ^ 2) := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
