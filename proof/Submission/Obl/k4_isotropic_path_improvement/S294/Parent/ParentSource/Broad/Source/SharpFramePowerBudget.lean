-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.SharpFramePowerBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/SharpFramePowerBudget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/SharpFramePowerBudget.lean.
All earlier source attributions below are retained. -/
-- From this LOT tree, o265 session x0943, branch origin/x0943, Broad/Source/SharpFramePowerBudget.lean.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SharpClockBudget

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

/-- The frame distortion costs four powers of the common source envelope. -/
theorem sharp_frame_coefficient_le_power
    {κ K sizeLoss : ℝ} (hK : 1 ≤ K) (hκ : 0 ≤ κ) (hκK : κ ≤ K)
    (hsize : 0 ≤ sizeLoss) (hsizeK : sizeLoss ≤ K) :
    1+4*κ+6*κ^3*sizeLoss ≤ 11*K^4 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hOne : 1 ≤ K^4 := one_le_pow₀ hK
  have hLinear : κ ≤ K^4 := hκK.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hK (by norm_num : (1:ℕ) ≤ 4))
  have hCubic : κ^3*sizeLoss ≤ K^4 := by
    calc
      _ ≤ K^3*K := mul_le_mul (pow_le_pow_left₀ hκ hκK 3) hsizeK hsize (pow_nonneg hK0 _)
      _ = _ := by ring
  linarith

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- A polynomial multiple of the fine dyadic width has a polynomial
inverse-frame budget. No gain from 1-kappa1 is used. -/
theorem Native.PathData.Valid.sharp_frame_budget_le_power
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hκ₁ : κ₁ ≤ 1)
    (i j : ℕ) (hi : i < m) (hj : j < m) (hs : s i ≤ s j)
    {mesh factor K : ℝ} (hfactor : 0 ≤ factor) (hK : 1 ≤ K) (hκK : p.κ ≤ K)
    (herror : Nk^(2*δ₀*L) ≤ K)
    (hmesh : mesh ≤ factor*(δ Nk (p.r j)/δ Nk (p.r i))) :
    3*((1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*
      ((2:ℝ)^p.T j/(2:ℝ)^p.T i))*mesh ≤ 66*factor*K^6 := by
  have hNp : 0 < Nk := zero_lt_one.trans_le hN
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hCf := sharp_frame_coefficient_le_power hK hκ hκK
    (Real.rpow_nonneg hNp.le _) herror
  have hN4 : Nk^(4*δ₀*L) ≤ K^2 := by
    calc
      _ = (Nk^(2*δ₀*L))^2 := by
        rw [←Real.rpow_mul_natCast hNp.le]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) herror 2
  calc
    _ ≤ 6*(1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*factor*Nk^(4*δ₀*L) :=
      hp.sharp_frame_budget_le hN hL hκ₁ i j hi hj hs hfactor hmesh
    _ ≤ 6*(11*K^4)*factor*K^2 := by gcongr
    _ = _ := by ring

/-- The resolution multiplier in the actual sharp isotropic census is
itself a fixed power of the source envelope. -/
theorem Native.PathData.Valid.sharp_isotropic_resolution_le_power
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hκ₁ : κ₁ ≤ 1)
    (i j : ℕ) (hi : i < m) (hj : j < m) (hs : s i ≤ s j)
    {mesh K G : ℝ} (hK : 2304 ≤ K) (hκK : p.κ ≤ K)
    (herror : Nk^(2*δ₀*L) ≤ K) (u v : ℕ) (hG : 0 ≤ G) (hGK : G ≤ K^v)
    (hmesh : mesh ≤ K^u*(δ Nk (p.r j)/δ Nk (p.r i))) :
    max 1 (max
      (3*((1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*
        ((2:ℝ)^p.T j/(2:ℝ)^p.T i))*mesh)
      (6*(4*p.κ*G*(1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))))) ≤
      K^(max (u+7) (v+6)) := by
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hNp : 0 < Nk := zero_lt_one.trans_le hN
  have hCf := sharp_frame_coefficient_le_power hK1 hκ hκK
    (Real.rpow_nonneg hNp.le _) herror
  have hframe := hp.sharp_frame_budget_le_power hN hL hκ₁ i j hi hj hs
    (pow_nonneg hK0 _) hK1 hκK herror hmesh
  refine max_le (one_le_pow₀ hK1) (max_le ?_ ?_)
  · calc
      _ ≤ 66*K^u*K^6 := hframe
      _ ≤ K*K^u*K^6 := by gcongr; linarith
      _ = K^(u+7) := by simp only [pow_add]; ring
      _ ≤ _ := pow_le_pow_right₀ hK1 (Nat.le_max_left _ _)
  · calc
      _ ≤ 6*(4*K*(K^v)*(11*K^4)) := by gcongr
      _ = 264*K^v*K^5 := by ring
      _ ≤ K*K^v*K^5 := by gcongr; linarith
      _ = K^(v+6) := by simp only [pow_add]; ring
      _ ≤ _ := pow_le_pow_right₀ hK1 (Nat.le_max_right _ _)

end Path

/-- The full-reference sharp census coefficient has an explicit envelope
power, once its actual resolution multiplier has been bounded. -/
theorem sharp_isotropic_count_coefficient_le_power
    {K κ C : ℝ} (hK : 2304 ≤ K) (hκ : 0 ≤ κ) (hκK : κ ≤ K)
    (hC : 0 ≤ C) (u R : ℕ) (hCK : C ≤ K^u) :
    62208*C^3*K^(3*R+28)*κ^4 ≤ K^(3*u+3*R+34) := by
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hconstant : (62208:ℝ) ≤ K^2 := by nlinarith
  calc
    _ ≤ K^2*(K^u)^3*K^(3*R+28)*K^4 := by gcongr
    _ = _ := by simp only [pow_mul,pow_add]; ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
