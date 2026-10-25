-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.SparseResidualScales, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.SnapshotDyadicScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set Filter

noncomputable section

/-- A fixed number of sparse dyadic snapshots reaches the qualification
floor. The rounding cost is fixed, independent of that floor. -/
theorem exists_sparse_residual_scales {ζ : ℝ} (hζ : 0<ζ) (hζ1 : ζ≤1)
    (n : ℕ) (hn : 0<n) :
    ∃ step : ℕ, 0<step ∧
      (∀ i : ℕ, dyadicParameterWidth (i*step)=
        (2:ℝ)^step*dyadicParameterWidth ((i+1)*step)) ∧
      dyadicParameterWidth (n*step)≤ζ ∧
      ζ/(2:ℝ)^(n+1)≤dyadicParameterWidth (n*step) ∧
      ((2:ℝ)^step)^n≤(2:ℝ)^(n+1)/ζ := by
  let q := parameterLevel ζ
  let step := q/n+1
  have hstep : 0<step := Nat.succ_pos (q/n)
  have hlow : q≤n*step := by
    dsimp only [step]
    have h := Nat.lt_mul_div_succ q hn
    omega
  have hhigh : n*step≤q+n := by
    dsimp only [step]
    have h := Nat.mul_div_le q n
    nlinarith
  have hqlo := (parameterLevel_width ζ hζ hζ1).1
  have hqhi := (parameterLevel_width ζ hζ hζ1).2
  have hlastLo : ζ/(2:ℝ)^(n+1)≤dyadicParameterWidth (n*step) := by
    calc
      ζ/(2:ℝ)^(n+1)=(ζ/2)*dyadicParameterWidth n := by
        simp only [dyadicParameterWidth,pow_succ,div_eq_mul_inv,mul_inv_rev]
        ring
      _ ≤ dyadicParameterWidth q*dyadicParameterWidth n :=
        mul_le_mul_of_nonneg_right hqlo (dyadicParameterWidth_pos n).le
      _ = dyadicParameterWidth (q+n) := by
        simp only [dyadicParameterWidth,pow_add,mul_inv_rev]
        ring
      _ ≤ _ := dyadicParameterWidth_antitone hhigh
  refine ⟨step,hstep,?_,(dyadicParameterWidth_antitone hlow).trans hqhi,hlastLo,?_⟩
  · intro i
    have hpow : (2:ℝ)^((i+1)*step)=(2:ℝ)^step*(2:ℝ)^(i*step) := by
      rw [show (i+1)*step=step+i*step by ring,pow_add]
    change ((2:ℝ)^(i*step))⁻¹=(2:ℝ)^step*((2:ℝ)^((i+1)*step))⁻¹
    rw [hpow,mul_inv_rev,mul_left_comm,mul_inv_cancel₀ (by positivity),mul_one]
  · have hpositive : 0<(2:ℝ)^(n+1) := by positivity
    have hh : ζ≤dyadicParameterWidth (n*step)*(2:ℝ)^(n+1) :=
      (div_le_iff₀ hpositive).mp hlastLo
    apply (le_div_iff₀ hζ).mpr
    rw [←pow_mul]
    have heq : (2:ℝ)^(step*n)*dyadicParameterWidth (n*step)=1 := by
      rw [Nat.mul_comm step n]
      simp only [dyadicParameterWidth]
      exact mul_inv_cancel₀ (by positivity)
    calc
      (2:ℝ)^(step*n)*ζ≤(2:ℝ)^(step*n)*(dyadicParameterWidth (n*step)*(2:ℝ)^(n+1)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by rw [←mul_assoc,heq,one_mul]

/-- The sparse ratio fits a prescribed power budget as soon as its
fixed-length total range does. -/
theorem sparse_ratio_le_of_power_budget {ζ A : ℝ} {n step : ℕ}
    (hζ : 0<ζ) (hA : 0≤A) (hn : 0<n)
    (hgrid : ((2:ℝ)^step)^n≤(2:ℝ)^(n+1)/ζ)
    (hbudget : (2:ℝ)^(n+1)/ζ≤A^n) : (2:ℝ)^step≤A := by
  exact (pow_le_pow_iff_left₀ (by positivity) hA hn.ne').mp (hgrid.trans hbudget)


/-- The number of residual snapshots is fixed before the sample and
the qualification floor. A polynomial floor needs only a polynomial
ratio at each of these finitely many snapshots. -/
theorem eventually_sparse_residual_scales (N : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) {Z a : ℝ} (hZ : 0≤Z) (ha : 0<a) :
    ∃ n : ℕ, 0<n ∧ ∀ᶠ k in atTop, ∀ ζ : ℝ,
      (N k)^(-Z)≤ζ → ζ≤1 →
      ∃ step : ℕ, 0<step ∧
        (∀ i : ℕ, dyadicParameterWidth (i*step)≤
          (N k)^a*dyadicParameterWidth ((i+1)*step)) ∧
        dyadicParameterWidth (n*step)≤ζ ∧
        ζ/(2:ℝ)^(n+1)≤dyadicParameterWidth (n*step) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (Z/a))
  have hn1 : (1:ℝ)<n := (le_max_left _ _).trans_lt hn
  have hnpos : 0<n := by exact_mod_cast (zero_lt_one.trans hn1)
  have hZn : Z/a<(n:ℝ) := (le_max_right _ _).trans_lt hn
  have hgap : 0<a*(n:ℝ)-Z := by
    have hh := (div_lt_iff₀ ha).mp hZn
    nlinarith
  refine ⟨n,hnpos,?_⟩
  filter_upwards [hN.eventually_gt_atTop 0,
    ((tendsto_rpow_atTop hgap).comp hN).eventually_ge_atTop ((2:ℝ)^(n+1))] with k hk hlarge
  intro ζ hfloor hζ1
  have hζ : 0<ζ := (Real.rpow_pos_of_pos hk _).trans_le hfloor
  obtain ⟨step,hstep,hratio,hlast,hlo,hpower⟩ := exists_sparse_residual_scales hζ hζ1 n hnpos
  have hbudget : (2:ℝ)^(n+1)/ζ≤((N k)^a)^n := by
    calc
      _ ≤ (2:ℝ)^(n+1)/(N k)^(-Z) :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hk _) hfloor
      _ = (2:ℝ)^(n+1)*(N k)^Z := by rw [Real.rpow_neg hk.le,div_inv_eq_mul]
      _ ≤ (N k)^(a*(n:ℝ)-Z)*(N k)^Z :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hk.le _)
      _ = ((N k)^a)^n := by
        rw [←Real.rpow_add hk,sub_add_cancel,Real.rpow_mul hk.le,Real.rpow_natCast]
  have hstepBudget := sparse_ratio_le_of_power_budget hζ
    (Real.rpow_nonneg hk.le a) hnpos hpower hbudget
  refine ⟨step,hstep,?_,hlast,hlo⟩
  intro i
  exact (le_of_eq (hratio i)).trans
    (mul_le_mul_of_nonneg_right hstepBudget (dyadicParameterWidth_pos _).le)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
