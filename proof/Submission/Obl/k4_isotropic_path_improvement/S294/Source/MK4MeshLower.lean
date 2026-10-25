-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.MK4MeshLower, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.MK4Numerics

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter

noncomputable section

/-- The actual rounded MK4 mesh also has a lower bound. The one
integer rounding costs exactly eight; its exponent is fixed by d. -/
theorem mk4_mesh_index_lower {T d : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hd : d < 1) :
    T^(24/(1-d))/8 ≤ Submission.Lib.K4DyadicRowScales.mesh (meshIndexOf T d) := by
  let n := meshIndexOf T d
  let x := 8*Real.logb 2 (1/T)/(1-d)
  have hd0 : 0 < 1-d := by linarith
  have hlog : 0 ≤ Real.logb 2 (1/T) := Real.logb_nonneg (by norm_num)
    (by rw [le_div_iff₀ hT]; linarith)
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hn : (n:ℝ) ≤ x+1 := (Nat.ceil_lt_add_one hx).le
  have hmesh : Submission.Lib.K4DyadicRowScales.mesh n=(2:ℝ)^(-(3*(n:ℝ))) := by
    rw [Submission.Lib.K4DyadicRowScales.mesh_eq_zpow,←Real.rpow_intCast]
    push_cast
    ring_nf
  have hTlog : T=(2:ℝ)^(-Real.logb 2 (1/T)) := by
    rw [Real.rpow_neg (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    field_simp
  have h8 : (8:ℝ)=(2:ℝ)^(3:ℝ) := by norm_num
  have hpower : T^(24/(1-d))/8=(2:ℝ)^(-3*(x+1)) := by
    conv_lhs => rw [hTlog]
    rw [←Real.rpow_mul (by norm_num),h8,←Real.rpow_sub (by norm_num)]
    congr 1
    dsimp only [x]
    ring
  rw [hpower,hmesh]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hn])

/-- A lower power for the actual internal MK4 target gives a uniform
lower power for its graph mesh, including the integer-rounding loss. -/
theorem mk4_mesh_lower_power {N T t margin d : ℝ}
    (hN : 1 ≤ N) (hT : N^(-t) ≤ T) (hT1 : T ≤ 1) (hd : d < 1)
    (hconstant : 8 ≤ N^margin) :
    N^(-(24*t/(1-d)+margin)) ≤
      Submission.Lib.K4DyadicRowScales.mesh (meshIndexOf T d) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hTp : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hT
  have hα : 0 ≤ 24/(1-d) := by positivity
  have hpower : N^(-(24*t/(1-d))) ≤ T^(24/(1-d)) := by
    calc
      _ = (N^(-t))^(24/(1-d)) := by
        rw [←Real.rpow_mul hNp.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hNp.le _) hT hα
  apply le_trans _ (mk4_mesh_index_lower hTp hT1 hd)
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<8)]
  calc
    _ ≤ N^(-(24*t/(1-d)+margin))*N^margin :=
      mul_le_mul_of_nonneg_left hconstant (Real.rpow_nonneg hNp.le _)
    _ = N^(-(24*t/(1-d))) := by rw [←Real.rpow_add hNp]; congr 1; ring
    _ ≤ _ := hpower

/-- Wait before choosing the actual row target: every permitted target
then yields the same lower graph-mesh power. -/
theorem eventually_mk4_mesh_lower_power
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {t margin d : ℝ} (hmargin : 0 < margin) (hd : d < 1) :
    ∀ᶠ k in atTop, ∀ T : ℝ, N k^(-t) ≤ T → T ≤ 1 →
      N k^(-(24*t/(1-d)+margin)) ≤
        Submission.Lib.K4DyadicRowScales.mesh (meshIndexOf T d) := by
  have hlarge := ((tendsto_rpow_atTop hmargin).comp hN).eventually (eventually_ge_atTop 8)
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  intro T hT hT1
  exact mk4_mesh_lower_power hk hT hT1 hd hc

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
