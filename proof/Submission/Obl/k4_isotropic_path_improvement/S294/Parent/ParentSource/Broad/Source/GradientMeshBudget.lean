-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.GradientMeshBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/GradientMeshBudget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/GradientMeshBudget.lean.
All earlier source attributions below are retained. -/
-- From this LOT tree, o265 session x0943, branch origin/x0943, Broad/Source/GradientMeshBudget.lean.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.GradientCoefficientPower
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SharpFramePowerBudget

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

/-- A polynomial enlargement of the fine width absorbs the genuine
whole-core gradient's additive error. -/
theorem gradient_error_le_half_power_mesh
    {K G ratio mesh : ℝ} (hK : 3 ≤ K) (v : ℕ) (hGK : G ≤ K^v)
    (hratio : 0 ≤ ratio) (hmesh : K^(v+10)*ratio ≤ mesh) :
    (2+G/2)*(K^14*(K^6)⁻¹*ratio) ≤ mesh/2 := by
  have hK1 : 1 ≤ K := by linarith
  have hKp : 0 < K := by linarith
  have hOne : 1 ≤ K^v := one_le_pow₀ hK1
  have hK2 : (5:ℝ) ≤ K^2 := by nlinarith
  have hcoef : 2+G/2 ≤ K^v*K^2/2 := by
    calc
      _ ≤ (5/2)*K^v := by linarith
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hK2 (pow_nonneg hKp.le v)]
  have hcancel : K^14*(K^6)⁻¹=K^8 := by
    rw [show K^14=K^8*K^6 by ring,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hKp.ne'),mul_one]
  calc
    _ = (2+G/2)*(K^8*ratio) := by rw [hcancel]
    _ ≤ (K^v*K^2/2)*(K^8*ratio) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (pow_nonneg hKp.le _) hratio)
    _ = K^(v+10)*ratio/2 := by simp only [pow_add]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hmesh (by norm_num)

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- An at-most-one-envelope-factor dyadic enlargement of the gradient
error scale has a fully explicit resolution exponent, uniformly at kappa1=1. -/
theorem Native.PathData.Valid.gradient_mesh_resolution_le_power
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hκ₁ : κ₁ ≤ 1)
    (i j : ℕ) (hi : i < m) (hj : j < m) (hs : s i ≤ s j)
    {mesh K G : ℝ} (hK : 2304 ≤ K) (hκK : p.κ ≤ K)
    (herror : Nk^(2*δ₀*L) ≤ K) (v : ℕ) (hG : 0 ≤ G) (hGK : G ≤ K^v)
    (hmesh : mesh ≤ K^(v+11)*(δ Nk (p.r j)/δ Nk (p.r i))) :
    max 1 (max
      (3*((1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*
        ((2:ℝ)^p.T j/(2:ℝ)^p.T i))*mesh)
      (6*(4*p.κ*G*(1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))))) ≤ K^(v+18) := by
  have hh := hp.sharp_isotropic_resolution_le_power hN hL hκ₁ i j hi hj hs hK hκK
    herror (v+11) v hG hGK hmesh
  have hexp : max ((v+11)+7) (v+6)=v+18 := by omega
  simpa only [hexp] using hh

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
