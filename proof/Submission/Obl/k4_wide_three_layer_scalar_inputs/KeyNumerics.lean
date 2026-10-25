import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortNumerics
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.ShortKey

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Inherited.Native

/-- The unit-scale variation inequality scales to every graph tolerance
at least one. -/
theorem scale_key_variation {B X W : ℝ} (hB : 0 ≤ B) (hX : 0 ≤ X) (hW : 1 ≤ W)
    (h : (B + 1) * X ≤ 1) : (B + W) * X ≤ W := by
  have hBW : B + W ≤ (B + 1) * W := by
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hW)]
  calc (B + W) * X ≤ ((B + 1) * W) * X := mul_le_mul_of_nonneg_right hBW hX
    _ = W * ((B + 1) * X) := by ring
    _ ≤ W * 1 := mul_le_mul_of_nonneg_left h (by linarith)
    _ = W := mul_one _

/-- At a jet tolerance at least two, the same unit-scale inequality
pays the larger coefficient-ball center as well. -/
theorem scale_key_jet_variation {B X M : ℝ} (hB : 2 ≤ B) (hX : 0 ≤ X) (hM : 2 ≤ M)
    (h : (B + 1) * X ≤ 1) : (B + 2 * M) * X ≤ M := by
  have hBM : B + 2 * M ≤ (B + 1) * M := by
    nlinarith [mul_nonneg (show 0 ≤ B - 2 by linarith) (show 0 ≤ M - 2 by linarith)]
  calc (B + 2 * M) * X ≤ ((B + 1) * M) * X := mul_le_mul_of_nonneg_right hBM hX
    _ = M * ((B + 1) * X) := by ring
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left h (by linarith)
    _ = M := mul_one _

/-- Connect the pure short-scale estimates to the numerical record of
both the matching and finer jet-count kernels. All remaining hypotheses
are scalar power budgets, with no hidden geometric or measure premise. -/
theorem keyNum_of_shortNumerics_tolerances
    {N H q a g D χ ζ w mesh B Lb Lv K d r v' Rc s₁ t₀ K₁ Mst A η R₀ W₁ W₂ : ℝ}
    {κ : Fin 3 → ℤ}
    (hs : ShortNumerics N H q a g D χ ζ w mesh B Lb Lv)
    (hN : 1 < N) (hH : 1 ≤ H) (hK : 0 ≤ K) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hq : 0 < q) (hg : 0 < g) (ha : 0 < a) (hζ : 0 ≤ ζ) (hLv : 0 ≤ Lv)
    (hB : 2 ≤ B) (hK₁ : 0 < K₁) (hw : 0 < w)
    (hχ : χ = N ^ (-v')) (hmesh : mesh = N ^ (-r))
    (hRc : 0 ≤ Rc) (hs₁0 : 0 ≤ s₁) (hs₁R : s₁ ≤ Rc)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1)
    (hL0 : |(κ 0 : ℝ) * χ| ≤ Lv) (hL1 : |(κ 1 : ℝ) * χ| ≤ Lv)
    (hM : 2 ≤ Mst) (hWM : 2 * H ≤ Mst) (hR₀ : R₀ * (4 * H) ≤ Mst)
    (hA1 : 1 ≤ A) (hAη : A ≤ (Mst / (4 * H)) ^ η)
    (hfit : 16 * a * H ≤ N ^ (-s₁))
    (hcap : 24000 * K * (N ^ (-s₁)) ^ d ≤ A * a ^ d)
    (hlog : -Real.logb N (18 * a * Mst) ≤ Rc)
    (hjet : K₁ * 12000 * K * (4 * H + 2) * 18 * (4 * H + 1) ≤ A)
    (hW₁1 : 1 ≤ W₁) (hW₁H : W₁ ≤ 2 * H) (hW₂1 : 1 ≤ W₂) (hW₂H : W₂ ≤ 2 * H) :
    KeyNum N K d r v' Rc s₁ t₀ q (q * g) ζ Lv a (2 * H) K₁ B
      W₁ W₂ (4 * H) Mst A w η R₀ κ := by
  have hB0 : 0 ≤ B := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hmesh0 : 0 < mesh := by rw [hmesh]; exact Real.rpow_pos_of_pos (by linarith) _
  let V := 7 * (mesh / q + (1 + Lv) * mesh / (2 * (q * g)))
  let Z := 7 * (q * (ζ + χ) / (2 * (q * g)))
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hZ0 : 0 ≤ Z := by
    have hχ0 : 0 < χ := by rw [hχ]; exact Real.rpow_pos_of_pos (by linarith) _
    dsimp [Z]; positivity
  have hV : (B + 1) * V ≤ 1 := by convert hs.key_freeze using 1 <;> dsimp [V] <;> ring
  have hZ : (B + 1) * Z ≤ 1 := by convert hs.key_drift using 1 <;> dsimp [Z] <;> ring
  have hvar₁ : (B + W₁) * V ≤ W₁ := scale_key_variation hB0 hV0 hW₁1 hV
  have hvar₂ : (B + W₂) * V ≤ W₂ := scale_key_variation hB0 hV0 hW₂1 hV
  have hdrift₁ : (B + W₁) * Z ≤ W₁ := scale_key_variation hB0 hZ0 hW₁1 hZ
  have hdrift₂ : (B + W₂) * Z ≤ W₂ := scale_key_variation hB0 hZ0 hW₂1 hZ
  have hvarJ : (B + 2 * Mst) * V ≤ Mst := scale_key_jet_variation hB hV0 hM hV
  have hdriftJ : (B + 2 * Mst) * Z ≤ Mst := scale_key_jet_variation hB hZ0 hM hZ
  have hcapw : 12000 * K * ((q * g) * w + q * (ζ + χ)) * (N ^ (-s₁)) ^ d ≤
      A * (q * g) * w * a ^ d := by
    have hhidden : 0 ≤ (N ^ (-s₁)) ^ d := Real.rpow_nonneg (by positivity) _
    calc _ ≤ 12000 * K * (2 * ((q * g) * w)) * (N ^ (-s₁)) ^ d := by
          gcongr
          linarith [hs.interval_drift]
      _ = ((q * g) * w) * (24000 * K * (N ^ (-s₁)) ^ d) := by ring
      _ ≤ ((q * g) * w) * (A * a ^ d) := mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = _ := by ring
  constructor
  · exact hN
  · exact hK
  · exact hd0
  · exact hd1
  · exact hRc
  · exact hs₁0
  · exact hs₁R
  · exact hq
  · exact mul_pos hq hg
  · exact hζ
  · exact hLv
  · exact ha
  · exact hK₁
  · positivity
  · exact hunit
  · simpa only [← hχ] using hL0
  · simpa only [← hχ] using hL1
  · simpa only [← hmesh] using hs.mesh_time
  · simpa only [← hmesh, ← hχ] using hs.mesh_intercept
  · simpa only [← hmesh] using hs.mesh_slice
  · simpa only [← hmesh, ← hχ] using hs.shear_intercept
  · simpa only [← hmesh] using hs.shear_slice
  · simpa only [← hχ] using hs.interval_drift
  · linarith
  · linarith
  · linarith
  · exact hW₁H.trans hWM
  · exact hW₂H.trans hWM
  · exact hR₀
  · exact hA1
  · exact hAη
  · exact hw
  · exact hs.jitter_quarter
  · linarith [hs.jitter_resolved]
  · nlinarith [mul_le_mul_of_nonneg_left hW₁H (show 0 ≤ 8 * a by positivity)]
  · nlinarith [mul_le_mul_of_nonneg_left hW₂H (show 0 ≤ 8 * a by positivity)]
  · simpa only [← hχ] using hcapw
  · simpa only [← hmesh, mul_assoc, V] using hvar₁
  · simpa only [← hmesh, mul_assoc, V] using hvar₂
  · simpa only [← hχ, mul_assoc, Z] using hdrift₁
  · simpa only [← hχ, mul_assoc, Z] using hdrift₂
  · simpa only [← hmesh, mul_assoc, V] using hvarJ
  · simpa only [← hχ, mul_assoc, Z] using hdriftJ
  · exact hlog
  · convert hjet using 1 <;> ring

/-- The equal-tolerance specialization used by the finer counts. -/
theorem keyNum_of_shortNumerics
    {N H q a g D χ ζ w mesh B Lb Lv K d r v' Rc s₁ t₀ K₁ Mst A η R₀ : ℝ}
    {κ : Fin 3 → ℤ}
    (hs : ShortNumerics N H q a g D χ ζ w mesh B Lb Lv)
    (hN : 1 < N) (hH : 1 ≤ H) (hK : 0 ≤ K) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hq : 0 < q) (hg : 0 < g) (ha : 0 < a) (hζ : 0 ≤ ζ) (hLv : 0 ≤ Lv)
    (hB : 2 ≤ B) (hK₁ : 0 < K₁) (hw : 0 < w)
    (hχ : χ = N ^ (-v')) (hmesh : mesh = N ^ (-r))
    (hRc : 0 ≤ Rc) (hs₁0 : 0 ≤ s₁) (hs₁R : s₁ ≤ Rc)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1)
    (hL0 : |(κ 0 : ℝ) * χ| ≤ Lv) (hL1 : |(κ 1 : ℝ) * χ| ≤ Lv)
    (hM : 2 ≤ Mst) (hWM : 2 * H ≤ Mst) (hR₀ : R₀ * (4 * H) ≤ Mst)
    (hA1 : 1 ≤ A) (hAη : A ≤ (Mst / (4 * H)) ^ η)
    (hfit : 16 * a * H ≤ N ^ (-s₁))
    (hcap : 24000 * K * (N ^ (-s₁)) ^ d ≤ A * a ^ d)
    (hlog : -Real.logb N (18 * a * Mst) ≤ Rc)
    (hjet : K₁ * 12000 * K * (4 * H + 2) * 18 * (4 * H + 1) ≤ A) :
    KeyNum N K d r v' Rc s₁ t₀ q (q * g) ζ Lv a (2 * H) K₁ B
      (2 * H) (2 * H) (4 * H) Mst A w η R₀ κ := by
  exact keyNum_of_shortNumerics_tolerances hs hN hH hK hd0 hd1 hq hg ha hζ hLv hB hK₁ hw
    hχ hmesh hRc hs₁0 hs₁R hunit hL0 hL1 hM hWM hR₀ hA1 hAη hfit hcap hlog hjet
    (by linarith) le_rfl (by linarith) le_rfl

end Submission.Obl.k4_wide_three_layer_scalar_inputs
