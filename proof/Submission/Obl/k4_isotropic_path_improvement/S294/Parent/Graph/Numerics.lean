-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.Numerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Graph/Numerics.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Numerical scale choices for the physical velocity graph:
with coarse cube `hidden^(2/3)` and graph precision `liftRho = hidden^((1-d)/24)`,
all scale hypotheses of `physical_coarse_velocity_rows` hold once
`hidden^((1-d)/24)` is below an explicit polynomial in `K⁻¹`, `fraction` and `ε`.
-/
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

noncomputable section

/-- Scale relations of the physical graph from one smallness condition. -/
theorem graph_scale_relations {K d fraction ε C hidden : ℝ}
    (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hd1 : d < 1) (hfraction : 0 < fraction) (hε : 0 < ε)
    (hC : 0 < C) (hh0 : 0 < hidden) (hh1 : hidden ≤ 1)
    (hsmall : hidden ^ ((1 - d) / 24) ≤
      min (1 / (64 * K)) (min (1 / (36 * K ^ 4))
        ((fraction / 4) ^ 4 * ε ^ 4 / (256 * C ^ 3 * K ^ 9 + 1)))) :
    let coarse := hidden ^ ((2 : ℝ) / 3)
    let liftRho := hidden ^ ((1 - d) / 24)
    8 * K * coarse ^ 2 < hidden ∧ 32 * K * coarse ≤ liftRho / 2 ∧
      36 * K ^ 3 * (K * liftRho) ≤ 1 ∧
      256 * C ^ 3 * K ^ 9 * hidden ^ ((1 - d) / 3) ≤ (fraction * liftRho / 4) ^ 4 * ε ^ 4 := by
  intro coarse liftRho
  set e := (1 - d) / 24 with he
  have he0 : 0 < e := by rw [he]; linarith
  have he1 : e ≤ 1 / 24 := by rw [he]; linarith
  have hpos : 0 < hidden ^ e := Real.rpow_pos_of_pos hh0 e
  have hK0 : 0 < K := by linarith
  have h1 : hidden ^ e ≤ 1 / (64 * K) := hsmall.trans (min_le_left _ _)
  have h2 : hidden ^ e ≤ 1 / (36 * K ^ 4) := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : hidden ^ e ≤ (fraction / 4) ^ 4 * ε ^ 4 / (256 * C ^ 3 * K ^ 9 + 1) :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- powers of hidden below one are monotone decreasing in the exponent
  have hmono {a b : ℝ} (hab : a ≤ b) : hidden ^ b ≤ hidden ^ a :=
    Real.rpow_le_rpow_of_exponent_ge hh0 hh1 hab
  have hcoarse2 : coarse ^ 2 = hidden ^ ((4 : ℝ) / 3) := by
    simp only [coarse]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh0.le]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 8 K hidden^(4/3) < hidden
    rw [hcoarse2]
    have hsplit : hidden ^ ((4 : ℝ) / 3) = hidden * hidden ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_one_add' hh0.le (by norm_num)]
      norm_num
    rw [hsplit]
    have hthird : hidden ^ ((1 : ℝ) / 3) ≤ hidden ^ e := hmono (by linarith)
    have hlt : 8 * K * hidden ^ ((1 : ℝ) / 3) < 1 := by
      calc 8 * K * hidden ^ ((1 : ℝ) / 3) ≤ 8 * K * (1 / (64 * K)) := by gcongr; exact hthird.trans h1
        _ = 1 / 8 := by field_simp; ring
        _ < 1 := by norm_num
    nlinarith
  · -- 64 K hidden^(2/3) ≤ hidden^e
    have hcmp : coarse ≤ hidden ^ e * hidden ^ e := by
      simp only [coarse]
      rw [← Real.rpow_add hh0]
      exact hmono (by linarith)
    have hK64 : 64 * K * hidden ^ e ≤ 1 := by
      calc 64 * K * hidden ^ e ≤ 64 * K * (1 / (64 * K)) := by gcongr
        _ = 1 := by field_simp
    have : 32 * K * coarse ≤ 32 * K * (hidden ^ e * hidden ^ e) := by gcongr
    nlinarith
  · -- 36 K^4 liftRho ≤ 1
    have : 36 * K ^ 3 * (K * liftRho) = 36 * K ^ 4 * hidden ^ e := by simp only [liftRho]; ring
    rw [this]
    calc 36 * K ^ 4 * hidden ^ e ≤ 36 * K ^ 4 * (1 / (36 * K ^ 4)) := by gcongr
      _ = 1 := by field_simp
  · -- MK4 budget: hidden^(8e) ≤ hidden^(4e) * hidden^(4e), using hidden^(4e) small
    have h8 : hidden ^ ((1 - d) / 3) = (hidden ^ e) ^ 4 * (hidden ^ e) ^ 4 := by
      have h4 : (hidden ^ e) ^ (4 : ℕ) = hidden ^ (e * 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hh0.le]
        norm_num
      rw [h4, ← Real.rpow_add hh0]
      congr 1
      rw [he]
      ring
    rw [h8]
    have hA : 0 < 256 * C ^ 3 * K ^ 9 + 1 := by positivity
    have hq : (hidden ^ e) ^ 4 ≤ hidden ^ e := by
      have hle1 : hidden ^ e ≤ 1 := Real.rpow_le_one hh0.le hh1 he0.le
      calc (hidden ^ e) ^ 4 = hidden ^ e * (hidden ^ e) ^ 3 := by ring
        _ ≤ hidden ^ e * 1 := by gcongr; exact pow_le_one₀ hpos.le hle1
        _ = hidden ^ e := mul_one _
    have hkey : (256 * C ^ 3 * K ^ 9) * (hidden ^ e) ^ 4 ≤ (fraction / 4) ^ 4 * ε ^ 4 := by
      have h3' := (le_div_iff₀ hA).mp h3
      nlinarith [pow_nonneg hpos.le 4]
    have : (fraction * liftRho / 4) ^ 4 * ε ^ 4 =
        ((fraction / 4) ^ 4 * ε ^ 4) * (hidden ^ e) ^ 4 := by simp only [liftRho]; ring
    rw [this]
    calc 256 * C ^ 3 * K ^ 9 * ((hidden ^ e) ^ 4 * (hidden ^ e) ^ 4)
        = (256 * C ^ 3 * K ^ 9 * (hidden ^ e) ^ 4) * (hidden ^ e) ^ 4 := by ring
      _ ≤ ((fraction / 4) ^ 4 * ε ^ 4) * (hidden ^ e) ^ 4 := by gcongr

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
