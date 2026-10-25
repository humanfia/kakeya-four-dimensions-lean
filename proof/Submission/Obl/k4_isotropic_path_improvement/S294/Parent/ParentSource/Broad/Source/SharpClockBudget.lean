-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.SharpClockBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/SharpClockBudget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/SharpClockBudget.lean.
All earlier source attributions below are retained. -/
-- From this LOT tree, o265 session x0943, branch origin/x0943, Broad/Source/SharpClockBudget.lean.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SharpFrameResolution
import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- The fine/old clock growth cancels the actual dyadic width ratio even
at the allowed endpoint kappa1=1. Only frozen path errors remain. -/
theorem Native.PathData.Valid.clock_dyadic_width_ratio_le
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hκ₁ : κ₁ ≤ 1)
    (i j : ℕ) (hi : i < m) (hj : j < m) (hs : s i ≤ s j) :
    ((2:ℝ)^p.T j/(2:ℝ)^p.T i)*(δ Nk (p.r j)/δ Nk (p.r i)) ≤
      2*Nk^(4*δ₀*L) := by
  have hNp : 0 < Nk := zero_lt_one.trans_le hN
  have hδi : Nk^(-p.r i) ≤ δ Nk (p.r i) :=
    (Submission.Obl.k4_horizon_chart_assembly.resolution_bounds hNp (p.r i)).1
  have hδj : δ Nk (p.r j) ≤ 2*Nk^(-p.r j) :=
    (Submission.Obl.k4_horizon_chart_assembly.resolution_bounds hNp (p.r j)).2
  have hδip : 0 < δ Nk (p.r i) := (Real.rpow_pos_of_pos hNp _).trans_le hδi
  have hratio : δ Nk (p.r j)/δ Nk (p.r i) ≤ 2*Nk^(-(p.r j-p.r i)) := by
    calc
      _ ≤ (2*Nk^(-p.r j))/Nk^(-p.r i) := by gcongr
      _ = _ := by
        rw [mul_div_assoc,←Real.rpow_sub hNp]
        congr 1
        ring
  have hscale := path_relative_mesh_le_time_ratio hp hN hL hκ₁ i j hi hj hs
  have hclock : ((2:ℝ)^p.T j/(2:ℝ)^p.T i)*Nk^(-(p.r j-p.r i)) ≤ Nk^(4*δ₀*L) := by
    calc
      _ ≤ ((2:ℝ)^p.T j/(2:ℝ)^p.T i)*
          (Nk^(4*δ₀*L)*((2:ℝ)^p.T i/(2:ℝ)^p.T j)) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ((2:ℝ)^p.T j/(2:ℝ)^p.T i)*(2*Nk^(-(p.r j-p.r i))) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 2*(((2:ℝ)^p.T j/(2:ℝ)^p.T i)*Nk^(-(p.r j-p.r i))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hclock (by norm_num)

/-- A physical mesh at most a fixed multiple of the genuine fine width
has a controlled inverse-frame resolution cost, uniformly at kappa1=1. -/
theorem Native.PathData.Valid.sharp_frame_budget_le
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hκ₁ : κ₁ ≤ 1)
    (i j : ℕ) (hi : i < m) (hj : j < m) (hs : s i ≤ s j)
    {mesh factor : ℝ} (hfactor : 0 ≤ factor)
    (hmesh : mesh ≤ factor*(δ Nk (p.r j)/δ Nk (p.r i))) :
    3*((1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*
      ((2:ℝ)^p.T j/(2:ℝ)^p.T i))*mesh ≤
        6*(1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*factor*Nk^(4*δ₀*L) := by
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hclock := hp.clock_dyadic_width_ratio_le hN hL hκ₁ i j hi hj hs
  calc
    _ ≤ 3*((1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*
        ((2:ℝ)^p.T j/(2:ℝ)^p.T i))*(factor*(δ Nk (p.r j)/δ Nk (p.r i))) := by
      gcongr
    _ = (3*(1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*factor)*
        (((2:ℝ)^p.T j/(2:ℝ)^p.T i)*(δ Nk (p.r j)/δ Nk (p.r i))) := by ring
    _ ≤ (3*(1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*factor)*(2*Nk^(4*δ₀*L)) :=
      mul_le_mul_of_nonneg_left hclock (by positivity)
    _ = _ := by ring

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
