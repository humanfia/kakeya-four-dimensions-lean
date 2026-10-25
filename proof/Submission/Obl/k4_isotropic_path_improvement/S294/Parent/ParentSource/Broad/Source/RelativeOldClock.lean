-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.RelativeOldClock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/RelativeOldClock.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path
import Submission.Obl.k4_scalar_angular_pair_agreement.Extrap

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Native MeasureTheory

noncomputable section

section Path

variable {W : ℕ} {p : PathData W} {N L κ₁ δ₀ σ : ℝ}
    {m Mp Dp : ℕ} {s : ℕ → ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- The clock of the actual later block, measured in the original root
clock, has exactly the two original path errors. -/
theorem Native.PathData.Valid.relative_old_clock_bounds
    (hN : 0 < N) (root old : ℕ) (hroot : root < m) (hold : old < m) :
    N^(-((κ₁*(s old-s root)+2*δ₀)*L)) ≤
        (((2 : ℝ)^p.T old)⁻¹)/(((2 : ℝ)^p.T root)⁻¹) ∧
    (((2 : ℝ)^p.T old)⁻¹)/(((2 : ℝ)^p.T root)⁻¹) ≤
        N^(-((κ₁*(s old-s root)-2*δ₀)*L)) := by
  have hrootPath := hp.2.2.2.2.1 root hroot
  have holdPath := hp.2.2.2.2.1 old hold
  have heq : (((2 : ℝ)^p.T old)⁻¹)/(((2 : ℝ)^p.T root)⁻¹)=
      (2 : ℝ)^p.T root/(2 : ℝ)^p.T old := by
    simp only [div_eq_mul_inv,inv_inv,mul_comm]
  rw [heq]
  constructor
  · calc
      _ = N^((κ₁*s root-δ₀)*L)/N^((κ₁*s old+δ₀)*L) := by
        rw [← Real.rpow_sub hN]
        congr 1
        ring
      _ ≤ (2 : ℝ)^p.T root/N^((κ₁*s old+δ₀)*L) :=
        div_le_div_of_nonneg_right hrootPath.2.2.1 (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) holdPath.2.2.2.1
  · calc
      _ ≤ N^((κ₁*s root+δ₀)*L)/(2 : ℝ)^p.T old :=
        div_le_div_of_nonneg_right hrootPath.2.2.2.1 (by positivity)
      _ ≤ N^((κ₁*s root+δ₀)*L)/N^((κ₁*s old-δ₀)*L) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) holdPath.2.2.1
      _ = _ := by rw [← Real.rpow_sub hN]; congr 1; ring

/-- The later-to-root ratio is an actual dyadic block length, rather
than an unrelated real approximation to one. -/
theorem Native.PathData.Valid.relative_old_clock_dyadic
    (hN : 1 ≤ N) (hL : 0 ≤ L) (root old : ℕ)
    (hroot : root < m) (hold : old < m)
    (hgap : 2*δ₀ ≤ κ₁*(s old-s root)) :
    p.T root ≤ p.T old ∧
      (((2 : ℝ)^p.T old)⁻¹)/(((2 : ℝ)^p.T root)⁻¹)=
        ((2 : ℝ)^(p.T old-p.T root))⁻¹ := by
  have hrootPath := hp.2.2.2.2.1 root hroot
  have holdPath := hp.2.2.2.2.1 old hold
  have hpower : (2 : ℝ)^p.T root ≤ (2 : ℝ)^p.T old := by
    apply hrootPath.2.2.2.1.trans
    apply le_trans _ holdPath.2.2.1
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith only [mul_le_mul_of_nonneg_right hgap hL]
  have hT : p.T root ≤ p.T old :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpower
  refine ⟨hT,?_⟩
  have hh := Submission.Obl.k4_scalar_angular_pair_agreement.ratio_eq hT
  simpa only [inv_div] using congrArg (fun x : ℝ => x⁻¹) hh

/-- The original path-error envelope alone pays the multiplicative
clock slack in the native qualification theorem. -/
theorem Native.PathData.Valid.relative_old_clock_native_bounds
    (hN : 1 ≤ N) (root old : ℕ) (hroot : root < m) (hold : old < m)
    {K : ℝ} (hK : N^(2*δ₀*L) ≤ K) :
    N^(-(κ₁*(s old-s root)*L))/K ≤
        (((2 : ℝ)^p.T old)⁻¹)/(((2 : ℝ)^p.T root)⁻¹) ∧
    (((2 : ℝ)^p.T old)⁻¹)/(((2 : ℝ)^p.T root)⁻¹) ≤
        K*N^(-(κ₁*(s old-s root)*L)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  obtain ⟨hlo,hhi⟩ := hp.relative_old_clock_bounds hNp root old hroot hold
  constructor
  · apply le_trans _ hlo
    calc
      _ ≤ N^(-(κ₁*(s old-s root)*L))/N^(2*δ₀*L) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hK
      _ = _ := by rw [← Real.rpow_sub hNp]; congr 1; ring
  · apply hhi.trans
    calc
      _ = N^(2*δ₀*L)*N^(-(κ₁*(s old-s root)*L)) := by
        rw [← Real.rpow_add hNp]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK (by positivity)

end Path

namespace RelativeOldClock

/-- Both ends of the relative clock-exponent interval are uniform in
the supplied grid and independent of the physical problem's L. -/
theorem exponent_range {κ precision gain sOld sRoot : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgain : 0 < gain)
    (hroot : 0 ≤ sRoot) (hrootSmall : κ*sRoot ≤ gain)
    (hlo : ((precision+2)/κ)*gain ≤ sOld)
    (hhi : sOld ≤ (((precision+2)/κ)+2)*gain) :
    (precision+1)*gain ≤ κ*(sOld-sRoot) ∧
      κ*(sOld-sRoot) ≤ (precision+4)*gain := by
  have hlow := mul_le_mul_of_nonneg_left hlo hκ.le
  have hhigh := mul_le_mul_of_nonneg_left hhi hκ.le
  have heq : κ*(((precision+2)/κ)*gain)=(precision+2)*gain := by field_simp [hκ.ne']
  have heq' : κ*((((precision+2)/κ)+2)*gain)=(precision+2+2*κ)*gain := by
    field_simp [hκ.ne']
  rw [heq] at hlow
  rw [heq'] at hhigh
  constructor
  · nlinarith only [hlow,hrootSmall]
  · nlinarith only [hhigh,mul_nonneg hκ.le hroot,mul_le_mul_of_nonneg_right hκ1 hgain.le]

/-- Work at the analytic base N^(gain L), and keep all qualification
constants fixed before the actual root-relative clock is supplied. -/
theorem analytic_base_identity {N gain : ℝ} (hN : 0 < N) (hgain : gain≠0)
    (L κ sOld sRoot : ℝ) :
    (N^(gain*L))^(κ*(sOld-sRoot)/gain)=N^(κ*(sOld-sRoot)*L) := by
  rw [← Real.rpow_mul hN.le]
  congr 1
  field_simp

end RelativeOldClock

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
