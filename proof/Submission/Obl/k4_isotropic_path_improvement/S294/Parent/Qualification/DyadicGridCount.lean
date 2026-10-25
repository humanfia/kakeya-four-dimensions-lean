-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.DyadicGridCount, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.SnapshotDyadicScales
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set Filter

/-- The actual selected dyadic level costs only a logarithm above
a polynomial scalar cutoff, including exact dyadic endpoints. -/
theorem parameterLevel_add_one_le_log {N ζ Z : ℝ} (hN : 1 < N)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hfloor : N^(-Z) ≤ ζ) :
    ((parameterLevel ζ+1:ℕ):ℝ) ≤ 2+(Z/Real.log 2)*Real.log N := by
  let q := parameterLevel ζ
  have hqpos : 0 < (2:ℝ)^q := by positivity
  have hh := (parameterLevel_width ζ hζ hζ1).1
  change ζ/2 ≤ ((2:ℝ)^q)⁻¹ at hh
  rw [inv_eq_one_div] at hh
  have hmul := (le_div_iff₀ hqpos).mp hh
  have hpow : (2:ℝ)^q ≤ 2/ζ := (le_div_iff₀ hζ).mpr (by nlinarith)
  have hNpos : 0 < N := zero_lt_one.trans hN
  have hupper : (2:ℝ)^q ≤ 2*N^Z := by
    calc
      _ ≤ 2/ζ := hpow
      _ ≤ 2/N^(-Z) := div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hNpos _) hfloor
      _ = _ := by rw [Real.rpow_neg hNpos.le,div_inv_eq_mul]
  have hlog := Real.log_le_log hqpos hupper
  rw [Real.log_pow,Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.rpow_pos_of_pos hNpos _).ne',
    Real.log_rpow hNpos] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : (q:ℝ) ≤ 1+(Z/Real.log 2)*Real.log N := by
    calc
      _ ≤ (Real.log 2+Z*Real.log N)/Real.log 2 := (le_div_iff₀ hlog2).mpr hlog
      _ = _ := by field_simp
  dsimp only [q] at hq
  push_cast
  linarith

/-- All logarithmic width counts in the original floor/support
factories fit any fixed positive power, uniformly over their cutoffs. -/
theorem eventually_parameterLevel_add_one_le (N : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) {Z a : ℝ} (hZ : 0 ≤ Z) (ha : 0 < a) :
    ∀ᶠ k in atTop, ∀ ζ : ℝ, (N k)^(-Z) ≤ ζ → ζ ≤ 1 →
      ((parameterLevel ζ+1:ℕ):ℝ) ≤ (N k)^a := by
  let C := Z/Real.log 2
  have hC : 0 ≤ C := div_nonneg hZ (Real.log_pos (by norm_num)).le
  let eps := (2*(C+1))⁻¹
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hlog := hN.eventually ((isLittleO_log_rpow_atTop ha).bound heps)
  have hlarge := ((tendsto_rpow_atTop ha).comp hN).eventually_ge_atTop 4
  filter_upwards [hN.eventually_gt_atTop 1,hlog,hlarge] with k hk hlogk hlargek
  change 4 ≤ (N k)^a at hlargek
  intro ζ hfloor hζ1
  have hNpos : 0 < N k := zero_lt_one.trans hk
  have hζ : 0 < ζ := (Real.rpow_pos_of_pos hNpos _).trans_le hfloor
  have hbound := parameterLevel_add_one_le_log hk hζ hζ1 hfloor
  have hlog' : Real.log (N k) ≤ eps*(N k)^a := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hk.le),
      abs_of_nonneg (Real.rpow_nonneg hNpos.le _)] using hlogk
  have hhalf : C*eps ≤ 1/2 := by
    dsimp only [eps]
    rw [←div_eq_mul_inv,div_le_iff₀ (by positivity : 0 < 2*(C+1))]
    linarith
  calc
    _ ≤ 2+C*Real.log (N k) := hbound
    _ ≤ 2+(1/2)*(N k)^a := by
      have hh := mul_le_mul_of_nonneg_left hlog' hC
      have hh' := mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hNpos.le a)
      nlinarith
    _ ≤ (N k)^a := by linarith

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
