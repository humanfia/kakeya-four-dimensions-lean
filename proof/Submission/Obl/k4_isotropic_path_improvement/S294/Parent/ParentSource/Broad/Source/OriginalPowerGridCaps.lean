-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalPowerGridCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalPowerGridCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalPowerGridCaps.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalAnisotropicCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.DirectPackaging
import Submission.Obl.k4_quadratic_finite_greedy_cover.ScaleTransfer

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open scoped ENNReal

noncomputable section

/-- Half a normalized unrounded signal width fits its actual dyadic depth. -/
theorem dyadic_relative_half_width {N : ℝ} (hN : 0 < N) (old step : ℝ) :
    δ N old * N ^ (-step) / 2 ≤ δ N (old + step) := by
  have hold := (Submission.Obl.k4_quadratic_finite_greedy_cover.δ_bounds hN old).2
  have hnew := (Submission.Obl.k4_quadratic_finite_greedy_cover.δ_bounds hN (old + step)).1
  have hpow : N ^ (-old) * N ^ (-step) = N ^ (-(old + step)) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  calc
    _ ≤ (2 * N ^ (-old)) * N ^ (-step) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_right hold (by positivity)
    _ = N ^ (-(old + step)) := by rw [← hpow]; ring
    _ ≤ _ := hnew

/-- Separate spatial and signal powers combine without changing dimension. -/
theorem anisotropic_cap_power_identity {N : ℝ} (hN : 0 < N)
    (χ r t dimension error tolerance κ K : ℝ) :
    (64 * K ^ 2 * κ * N ^ (-dimension * ((χ * t)) + 2 * error + tolerance)) *
        (2 * (N ^ χ) ^ (-r)) ^ 3 =
      (512 * K ^ 2 * κ * N ^ (2 * error + tolerance)) *
        (N ^ χ) ^ (-3 * r - dimension * t) := by
  have hpow : N ^ (-dimension * (χ * t) + 2 * error + tolerance) =
      N ^ (2 * error + tolerance) * (N ^ χ) ^ (-dimension * t) := by
    rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1
    ring
  have hcube : ((N ^ χ) ^ (-r)) ^ 3 = (N ^ χ) ^ (-3 * r) := by
    rw [← Real.rpow_mul_natCast (Real.rpow_nonneg hN.le _)]
    congr 1
    ring
  rw [hpow, mul_pow, hcube,
    show -3*r-dimension*t=(-3*r)+(-dimension*t) by ring,
    Real.rpow_add (Real.rpow_pos_of_pos hN _)]
  norm_num only [show (2 : ℝ)^3=8 by norm_num]
  ring

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hpure : Q.uniformPureCeiling ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- The actual original pure ceiling simultaneously controls every base
power and every signal power in an auxiliary mesh. The profile dimension
is unchanged, and the only slack is the displayed constant budget. -/
theorem Native.PreparedAngularPath.original_power_grid_cap
    (old : Fin p.C) (hr : 0 ≤ p.r (p.lev old))
    (χ r t : ℝ) (hχ : 0 ≤ χ) (ht : 0 ≤ t)
    (hdepth : p.r (p.lev old) + χ * t ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old))
    (hbase : ∀ᵐ z ∂μ, z ∈ Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z ∈ p.F old)
    {dimension f₀ error Kcap : ℝ}
    (hprofile : |d.f (p.r (p.lev old)) - f₀ - dimension * p.r (p.lev old)| ≤ error)
    (hprofile' : |d.f (p.r (p.lev old) + χ*t) - f₀ -
      dimension * (p.r (p.lev old) + χ*t)| ≤ error)
    (hbudget : 512 * (max p.κ (d.K k)) ^ 2 * p.κ *
      d.N k ^ (2 * error + τ + ε) ≤ Kcap) (c : Fin 4 → ℤ) :
    (d.ν k (p.γ old) (p.A old) *
      ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹))⁻¹ *
        μ ((p.originalPhysicalCode (d.N k) old
          ((d.N k ^ χ) ^ (-r)) ((d.N k ^ χ) ^ (-t))) ⁻¹' {c}) ≤
      ENNReal.ofReal (Kcap * (d.N k ^ χ) ^ (-3*r-dimension*t)) := by
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hmesh : 0 < (d.N k ^ χ) ^ (-r) := by positivity
  have hhidden : 0 < (d.N k ^ χ) ^ (-t) := by positivity
  have hstep : 0 ≤ χ*t := mul_nonneg hχ ht
  have hscale : δ (d.N k) (p.r (p.lev old)+χ*t) ≤ δ (d.N k) (p.r (p.lev old)) :=
    Broad.δ_antitone hN (le_add_of_nonneg_right hstep)
  have hhiddenEq : (d.N k ^ χ) ^ (-t) = d.N k ^ (-(χ*t)) := by
    rw [← Real.rpow_mul hNp.le]
    congr 1
    ring
  have hwidth : δ (d.N k) (p.r (p.lev old)) * (d.N k ^ χ) ^ (-t) / 2 ≤
      δ (d.N k) (p.r (p.lev old)+χ*t) := by
    rw [hhiddenEq]
    exact dyadic_relative_half_width hNp _ _
  have hraw := Q.original_anisotropic_grid_cap hpure hd hp old
    (p.r (p.lev old)+χ*t) (add_nonneg hr hstep) hdepth hscale hmesh hhidden hwidth
    μ hμ hbase hF hprofile hprofile' c
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hid : (64 * (max p.κ (d.K k)) ^ 2 * p.κ *
      d.N k ^ (-dimension * ((p.r (p.lev old)+χ*t)-p.r (p.lev old)) + 2*error+τ+ε)) *
        (2*(d.N k ^ χ)^(-r))^3 =
      (512 * (max p.κ (d.K k)) ^ 2 * p.κ * d.N k ^ (2*error+τ+ε)) *
        (d.N k ^ χ) ^ (-3*r-dimension*t) := by
    convert anisotropic_cap_power_identity hNp χ r t dimension error (τ+ε) p.κ
      (max p.κ (d.K k)) using 1 <;> congr 2 <;> ring
  rw [← ENNReal.ofReal_mul (by positivity), hid] at hraw
  exact hraw.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hbudget (by positivity)))

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
