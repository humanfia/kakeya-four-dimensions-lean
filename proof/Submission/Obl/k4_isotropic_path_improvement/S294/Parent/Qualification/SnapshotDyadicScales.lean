-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.SnapshotDyadicScales, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/SnapshotDyadicScales.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicParameterBins

/-! # One finite original parameter grid covers all scalar snapshot widths -/
set_option autoImplicit false
namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set

/-- Parameter dyadic widths decrease with their integer depth. -/
theorem dyadicParameterWidth_antitone : Antitone dyadicParameterWidth := by
  intro i j hij
  dsimp only [dyadicParameterWidth]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hij)

/-- One step halves an original dyadic parameter width. -/
theorem dyadicParameterWidth_succ (n : ℕ) :
    dyadicParameterWidth (n+1)=dyadicParameterWidth n/2 := by
  simp only [dyadicParameterWidth,pow_succ,mul_inv_rev,div_eq_mul_inv]
  ring

/-- The chosen parameter levels are monotone, even at dyadic endpoints. -/
theorem parameterLevel_antitone_on_unit {q r : ℝ}
    (hq : 0 < q) (hqr : q ≤ r) (hr : r ≤ 1) : parameterLevel r ≤ parameterLevel q := by
  by_cases heq : q=r
  · simp only [heq,le_refl]
  have hqstrict : q < r := lt_of_le_of_ne hqr heq
  have hr0 := hq.trans_le hqr
  by_contra hn
  have hsucc : parameterLevel q+1 ≤ parameterLevel r := Nat.succ_le_of_lt (lt_of_not_ge hn)
  have hw := dyadicParameterWidth_antitone hsucc
  rw [dyadicParameterWidth_succ] at hw
  have hqwidth := (parameterLevel_width q hq (hqr.trans hr)).2
  have hrwidth := (parameterLevel_width r hr0 hr).1
  linarith

/-- All real widths above a fixed floor use one finite original grid. -/
theorem parameterLevel_below_floor {ζ q : ℝ} (hζ : 0 < ζ)
    (hζq : ζ ≤ q) (hq1 : q ≤ 1) : parameterLevel q < parameterLevel ζ+1 := by
  exact Nat.lt_succ_of_le (parameterLevel_antitone_on_unit hζ hζq hq1)

/-- Full original dyadic coefficient bins form the exact nested grid. -/
theorem coarsen_nested_parameterCode {m : ℕ} (ρ : ℝ) (hρ : 0 < ρ) {i j : ℕ}
    (hij : i ≤ j) (c : Fin m → ℝ) :
    coarsenParameterCode (j-i) (parameterCode (ρ*dyadicParameterWidth j) c)=
      parameterCode (ρ*dyadicParameterWidth i) c := by
  have hscale : (ρ*dyadicParameterWidth i)*dyadicParameterWidth (j-i)=
      ρ*dyadicParameterWidth j := by
    calc
      _ = ρ*dyadicParameterWidth (i+(j-i)) := by
        simp only [dyadicParameterWidth,pow_add,mul_inv_rev]
        ring
      _ = _ := by rw [Nat.add_sub_of_le hij]
  have h := coarsen_parameterCode (ρ*dyadicParameterWidth i)
    (mul_pos hρ (dyadicParameterWidth_pos i)) (j-i) c
  simpa only [hscale] using h

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
