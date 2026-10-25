-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ParentFramePower, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ParentFramePower.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ParentFramePower.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CenterVelocity
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.GradientMeshBudget

/-! # Explicit envelope powers for the physical parent source census -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native

noncomputable section

section Original

variable {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- The actual unshearing factor has a uniform fifth-power bound. -/
theorem original_unshearing_le_power {K : ℝ} (hK : 9 ≤ K)
    (hmax : max p.κ (d.K k) ≤ K) (herror : d.N k ^ (2 * δ₀ * d.L) ≤ K)
    (old : Fin p.C) :
    1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + ‖p.u old‖) ≤ K ^ 5 := by
  have hNp : 0 ≤ d.N k := by linarith [hd.1 k]
  apply physical_unshearing_power hK
    (zero_lt_one.trans_le hp.1).le ((le_max_left _ _).trans hmax)
    (Real.rpow_nonneg hNp _) herror (norm_nonneg _)
  have hcenter := (hd.path_frame_bounds hp old).1
  have hOrig : d.K k ≤ K := (le_max_right _ _).trans hmax
  linarith

/-- The existing actual clock/width budget gains just five unshearing powers,
including the endpoint `kappa1=1`. -/
theorem original_unsheared_frame_budget_le_power
    (hN : 1 ≤ d.N k) (hκ₁ : κ₁ ≤ 1)
    (i j : ℕ) (hi : i < m) (hj : j < m) (hs : s i ≤ s j)
    {mesh factor K : ℝ} (hfactor : 0 ≤ factor) (hK : 9 ≤ K)
    (hmax : max p.κ (d.K k) ≤ K) (herror : d.N k ^ (2 * δ₀ * d.L) ≤ K)
    (old : Fin p.C)
    (hmesh : mesh ≤ factor * (δ (d.N k) (p.r j) / δ (d.N k) (p.r i))) :
    3 * ((1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) *
        ((2 : ℝ) ^ p.T j / (2 : ℝ) ^ p.T i)) *
      (1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + ‖p.u old‖)) * mesh ≤
        66 * factor * K ^ 11 := by
  have hK1 : 1 ≤ K := by linarith
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hNp : 0 ≤ d.N k := zero_le_one.trans hN
  have hbase := hp.sharp_frame_budget_le_power hN (le_of_lt hd.2.2.2.1) hκ₁
    i j hi hj hs hfactor hK1 ((le_max_left _ _).trans hmax) herror hmesh
  have hU := original_unshearing_le_power hd hp hK hmax herror old
  have hU0 : 0 ≤ 1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + ‖p.u old‖) := by positivity
  calc
    _ = (3 * ((1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) *
        ((2 : ℝ) ^ p.T j / (2 : ℝ) ^ p.T i)) * mesh) *
      (1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + ‖p.u old‖)) := by ring
    _ ≤ (66 * factor * K ^ 6) * K ^ 5 :=
      mul_le_mul hbase hU hU0 (by positivity)
    _ = _ := by rw [show (11 : ℕ) = 6 + 5 by norm_num, pow_add]; ring

/-- An envelope-power mesh enlargement gives the actual unsheared frame
resolution, with all constants absorbed once. -/
theorem original_unsheared_resolution_le_power
    (hN : 1 ≤ d.N k) (hκ₁ : κ₁ ≤ 1)
    (i j : ℕ) (hi : i < m) (hj : j < m) (hs : s i ≤ s j)
    {mesh K : ℝ} (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (herror : d.N k ^ (2 * δ₀ * d.L) ≤ K) (old : Fin p.C) (u : ℕ)
    (hmesh : mesh ≤ K ^ u * (δ (d.N k) (p.r j) / δ (d.N k) (p.r i))) :
    max 1 (3 * ((1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) *
        ((2 : ℝ) ^ p.T j / (2 : ℝ) ^ p.T i)) *
      (1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + ‖p.u old‖)) * mesh) ≤ K ^ (u + 12) := by
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 ≤ K := hK1.trans' (by norm_num)
  refine max_le (one_le_pow₀ hK1) ?_
  calc
    _ ≤ 66 * K ^ u * K ^ 11 :=
      original_unsheared_frame_budget_le_power hd hp hN hκ₁ i j hi hj hs
        (pow_nonneg hK0 _) (by linarith) hmax herror old hmesh
    _ ≤ K * K ^ u * K ^ 11 := by gcongr; linarith
    _ = _ := by simp only [pow_add]; ring

/-- The true physical Lipschitz coefficient is an explicit power, with the
old block length and physical thickness left outside it. -/
theorem original_parent_slope_le_power {K G : ℝ} (hK : 2304 ≤ K)
    (hmax : max p.κ (d.K k) ≤ K) (herror : d.N k ^ (2 * δ₀ * d.L) ≤ K)
    (v : ℕ) (hG : 0 ≤ G) (hGK : G ≤ K ^ v) (old : Fin p.C) :
    12 * K * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) *
      (1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + ‖p.u old‖)) ≤ K ^ (v + 11) := by
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 ≤ K := hK1.trans' (by norm_num)
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hNp : 0 ≤ d.N k := by linarith [hd.1 k]
  have hCf := sharp_frame_coefficient_le_power hK1 hκ ((le_max_left _ _).trans hmax)
    (Real.rpow_nonneg hNp _) herror
  have hU := original_unshearing_le_power hd hp (by linarith) hmax herror old
  calc
    _ ≤ 12 * K * (K ^ v) * (11 * K ^ 4) * (K ^ 5) := by gcongr
    _ = 132 * K ^ v * K ^ 10 := by ring
    _ ≤ K * K ^ v * K ^ 10 := by gcongr; linarith
    _ = _ := by simp only [pow_add]; ring

/-- A power-budget anisotropic mesh discharges the actual physical slope condition. -/
theorem original_parent_anisotropic_mesh_budget {K G a h base hidden : ℝ}
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (herror : d.N k ^ (2 * δ₀ * d.L) ≤ K) (v : ℕ) (hG : 0 ≤ G) (hGK : G ≤ K ^ v)
    (old : Fin p.C) (hh : 0 ≤ h) (hbase : 0 ≤ base)
    (hmesh : K ^ (v + 12) * h * base ≤ a * hidden) :
    6 * (12 * K * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) *
      (1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + ‖p.u old‖))) * h * base ≤
      a * hidden := by
  have hK0 : 0 ≤ K := by linarith
  calc
    _ ≤ 6 * K ^ (v + 11) * h * base := by
      gcongr
      exact original_parent_slope_le_power hd hp hK hmax herror v hG hGK old
    _ ≤ K * K ^ (v + 11) * h * base := by gcongr; linarith
    _ = K ^ (v + 12) * h * base := by simp only [pow_add]; ring
    _ ≤ _ := hmesh

end Original

/-- The additional original unsheared determinant factor costs one power. -/
theorem physical_parent_count_coefficient_le_power
    {K κ C sizeLoss : ℝ} (hK : 2304 ≤ K) (hκ : 0 ≤ κ) (hκK : κ ≤ K)
    (hC : 0 ≤ C) (u R : ℕ) (hCK : C ≤ K ^ u)
    (hsize : 0 ≤ sizeLoss) (hsizeK : sizeLoss ≤ K) :
    62208 * C ^ 3 * K ^ (3 * R + 28) * κ ^ 4 * sizeLoss ≤
      K ^ (3 * u + 3 * R + 35) := by
  have hK0 : 0 ≤ K := by linarith
  calc
    _ ≤ K ^ (3 * u + 3 * R + 34) * K := mul_le_mul
      (sharp_isotropic_count_coefficient_le_power hK hκ hκK hC u R hCK) hsizeK hsize
      (pow_nonneg hK0 _)
    _ = _ := by simp only [pow_add]; ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
