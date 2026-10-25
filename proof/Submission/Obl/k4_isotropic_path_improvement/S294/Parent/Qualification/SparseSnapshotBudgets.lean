-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.SparseSnapshotBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.SparseResidualScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set Filter

/-- Exact comparisons on the original integer dyadic width grid. -/
theorem dyadicParameterWidth_le_iff (i j : ℕ) :
    dyadicParameterWidth i ≤ dyadicParameterWidth j ↔ j ≤ i := by
  dsimp only [dyadicParameterWidth]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  exact pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)

/-- Products stay on the same original dyadic grid. -/
theorem dyadicParameterWidth_add (i j : ℕ) :
    dyadicParameterWidth (i+j)=dyadicParameterWidth i*dyadicParameterWidth j := by
  simp only [dyadicParameterWidth,pow_add,mul_inv_rev]
  ring

/-- A dyadic cutoff rounds its own integer index by at most one. -/
theorem parameterLevel_dyadic_upper (i : ℕ) :
    parameterLevel (dyadicParameterWidth i) ≤ i+1 := by
  have hw1 : dyadicParameterWidth i ≤ 1 := by
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hh := (parameterLevel_width _ (dyadicParameterWidth_pos i) hw1).1
  rw [←dyadicParameterWidth_succ] at hh
  exact (dyadicParameterWidth_le_iff _ _).mp hh

/-- At a prescribed fixed number of intervals, any polynomial cutoff
admits sparse dyadic snapshots with a prescribed polynomial ratio.
This fixes the count before all later measures and source data. -/
theorem eventually_sparse_scales_at_length (N : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) {Z a : ℝ} (ha : 0<a)
    (n : ℕ) (hn : 0<n) (hgap : Z<a*(n:ℝ)) :
    ∀ᶠ k in atTop, ∀ ζ : ℝ, (N k)^(-Z) ≤ ζ → ζ ≤ 1 →
      ∃ step : ℕ, 0<step ∧
        (∀ i : ℕ, dyadicParameterWidth (i*step)=
          (2:ℝ)^step*dyadicParameterWidth ((i+1)*step)) ∧
        (2:ℝ)^step ≤ (N k)^a ∧
        dyadicParameterWidth (n*step) ≤ ζ ∧
        ζ/(2:ℝ)^(n+1) ≤ dyadicParameterWidth (n*step) ∧
        n*step ≤ parameterLevel ζ+n := by
  have hgap' : 0<a*(n:ℝ)-Z := sub_pos.mpr hgap
  filter_upwards [hN.eventually_gt_atTop 0,
    ((tendsto_rpow_atTop hgap').comp hN).eventually_ge_atTop ((2:ℝ)^(n+1))] with k hk hlarge
  intro ζ hfloor hζ1
  have hζ : 0<ζ := (Real.rpow_pos_of_pos hk _).trans_le hfloor
  have hbudget : (2:ℝ)^(n+1)/ζ ≤ ((N k)^a)^n := by
    calc
      _ ≤ (2:ℝ)^(n+1)/(N k)^(-Z) :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hk _) hfloor
      _ = (2:ℝ)^(n+1)*(N k)^Z := by rw [Real.rpow_neg hk.le,div_inv_eq_mul]
      _ ≤ (N k)^(a*(n:ℝ)-Z)*(N k)^Z :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hk.le _)
      _ = ((N k)^a)^n := by
        rw [←Real.rpow_add hk,sub_add_cancel,Real.rpow_mul hk.le,Real.rpow_natCast]
  let q := parameterLevel ζ
  let step' := q/n+1
  have hstep' : 0<step' := Nat.succ_pos _
  have hlow : q ≤ n*step' := by
    have hh := Nat.lt_mul_div_succ q hn
    dsimp only [step']
    omega
  have hhigh : n*step' ≤ q+n := by
    have hh := Nat.mul_div_le q n
    dsimp only [step']
    nlinarith
  have hpw (i : ℕ) : dyadicParameterWidth (i*step')=
      (2:ℝ)^step'*dyadicParameterWidth ((i+1)*step') := by
    have hpow : (2:ℝ)^((i+1)*step')=(2:ℝ)^step'*(2:ℝ)^(i*step') := by
      rw [show (i+1)*step'=step'+i*step' by ring,pow_add]
    change ((2:ℝ)^(i*step'))⁻¹=(2:ℝ)^step'*((2:ℝ)^((i+1)*step'))⁻¹
    rw [hpow,mul_inv_rev,mul_left_comm,mul_inv_cancel₀ (by positivity),mul_one]
  have hlast' := (dyadicParameterWidth_antitone hlow).trans (parameterLevel_width ζ hζ hζ1).2
  have hlo' : ζ/(2:ℝ)^(n+1) ≤ dyadicParameterWidth (n*step') := by
    calc
      _=(ζ/2)*dyadicParameterWidth n := by
        simp only [dyadicParameterWidth,pow_succ,div_eq_mul_inv,mul_inv_rev]
        ring
      _ ≤ dyadicParameterWidth q*dyadicParameterWidth n :=
        mul_le_mul_of_nonneg_right (parameterLevel_width ζ hζ hζ1).1 (dyadicParameterWidth_pos n).le
      _ = dyadicParameterWidth (q+n) := (dyadicParameterWidth_add _ _).symm
      _ ≤ _ := dyadicParameterWidth_antitone hhigh
  have hpower' : ((2:ℝ)^step')^n ≤ (2:ℝ)^(n+1)/ζ := by
    apply (le_div_iff₀ hζ).mpr
    have hh := (div_le_iff₀ (by positivity : 0<(2:ℝ)^(n+1))).mp hlo'
    have heq : ((2:ℝ)^step')^n*dyadicParameterWidth (n*step')=1 := by
      rw [←pow_mul,Nat.mul_comm step' n]
      exact mul_inv_cancel₀ (by positivity)
    calc
      _ ≤ ((2:ℝ)^step')^n*(dyadicParameterWidth (n*step')*(2:ℝ)^(n+1)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by rw [←mul_assoc,heq,one_mul]
  exact ⟨step',hstep',hpw,
    sparse_ratio_le_of_power_budget hζ (Real.rpow_nonneg hk.le a) hn hpower' hbudget,
    hlast',hlo',hhigh⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
