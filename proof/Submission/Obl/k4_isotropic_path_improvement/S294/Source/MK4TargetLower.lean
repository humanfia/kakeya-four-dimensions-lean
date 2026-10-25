-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.MK4TargetLower, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.MK4MeshLower
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordGeometryPowers

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter

noncomputable section

/-- The literal internal target used to choose the MK4 graph mesh. -/
def mk4MeshTarget (theta Kg epsilon : ℝ) : ℝ :=
  min (theta/(80*Kg^7)) (min (1/(64*Kg)) (min (1/(36*Kg^4))
    (((1/4:ℝ)/4)^4*epsilon^4/
      (256*Parent.ParentSource.Broad.Velocity.curvatureRowConstant^3*Kg^9+1))))

/-- One fixed constant absorbs every denominator of the MK4 target. -/
def mk4MeshFloorConstant : ℝ :=
  max 80 ((16:ℝ)^4*(256*Parent.ParentSource.Broad.Velocity.curvatureRowConstant^3+1))

/-- A lower power of the literal MK4 target, from the actual row
accuracy, actual envelope and actual retained original mass. -/
theorem mk4_target_lower_power
    {N Kg theta epsilon g t e margin : ℝ}
    (hN : 1 ≤ N) (hKg : 1 ≤ Kg) (hKgN : Kg ≤ N^g)
    (htheta : N^(-t) ≤ theta) (hepsilon : N^(-e) ≤ epsilon)
    (hg : 0 ≤ g) (ht : 0 ≤ t) (he : 0 ≤ e)
    (hconstant : mk4MeshFloorConstant ≤ N^margin) :
    N^(-(t+4*e+16*g+margin)) ≤ mk4MeshTarget theta Kg epsilon := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hKg0 : 0 ≤ Kg := zero_le_one.trans hKg
  have hKgp : 0 < Kg := zero_lt_one.trans_le hKg
  have hcurv := Parent.ParentSource.Broad.Velocity.curvatureRowConstant_pos
  have h80 : (80:ℝ) ≤ N^margin := (le_max_left _ _).trans hconstant
  have hC : (16:ℝ)^4*(256*Parent.ParentSource.Broad.Velocity.curvatureRowConstant^3+1) ≤
      N^margin := (le_max_right _ _).trans hconstant
  have hp (n : ℕ) {coefficient target : ℝ}
      (hc : 0 ≤ coefficient) (hcN : coefficient ≤ N^margin)
      (hexp : margin+g*(n:ℝ)-(t+4*e+16*g+margin) ≤ target) :
      coefficient*Kg^n*N^(-(t+4*e+16*g+margin)) ≤ N^target := by
    exact envelope_power_budget_of_margin n hN hKg0 hKgN hc hcN
      (by linarith only [hexp])
  unfold mk4MeshTarget
  refine le_min ?_ (le_min ?_ (le_min ?_ ?_))
  · rw [le_div_iff₀ (by positivity : (0:ℝ) < 80*Kg^7)]
    calc
      _ = 80*Kg^7*N^(-(t+4*e+16*g+margin)) := by ring
      _ ≤ N^(-t) := hp 7 (by norm_num) h80 (by norm_num; linarith only [hg,he])
      _ ≤ theta := htheta
  · rw [le_div_iff₀ (by positivity : (0:ℝ) < 64*Kg)]
    have hh := hp 1 (by norm_num : (0:ℝ) ≤ 64) (by linarith : (64:ℝ) ≤ N^margin)
      (by norm_num; linarith only [hg,ht,he] : margin+g*(1:ℕ)-(t+4*e+16*g+margin) ≤ 0)
    simpa only [pow_one,Real.rpow_zero,mul_comm,mul_left_comm,mul_assoc] using hh
  · rw [le_div_iff₀ (by positivity : (0:ℝ) < 36*Kg^4)]
    have hh := hp 4 (by norm_num : (0:ℝ) ≤ 36) (by linarith : (36:ℝ) ≤ N^margin)
      (by norm_num; linarith only [hg,ht,he] : margin+g*(4:ℕ)-(t+4*e+16*g+margin) ≤ 0)
    simpa only [Real.rpow_zero,mul_comm,mul_left_comm,mul_assoc] using hh
  · have hdenom : 0 < 256*Parent.ParentSource.Broad.Velocity.curvatureRowConstant^3*Kg^9+1 := by
      positivity
    rw [le_div_iff₀ hdenom]
    have hKg9 : 1 ≤ Kg^9 := one_le_pow₀ hKg
    have hdenomBound : 256*Parent.ParentSource.Broad.Velocity.curvatureRowConstant^3*Kg^9+1 ≤
        (256*Parent.ParentSource.Broad.Velocity.curvatureRowConstant^3+1)*Kg^9 := by
      nlinarith only [hKg9]
    have hh := hp 9 (by positivity)
      hC (by norm_num; linarith only [hg,ht] :
        margin+g*(9:ℕ)-(t+4*e+16*g+margin) ≤ -4*e)
    have hepsilon0 : 0 ≤ epsilon := (Real.rpow_nonneg hNp.le _).trans hepsilon
    have hEpsilon4 : N^(-4*e) ≤ epsilon^4 := by
      calc
        _ = (N^(-e))^4 := by
          rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
          congr 1
          ring
        _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hepsilon 4
    have hbudget : (16:ℝ)^4*
        (N^(-(t+4*e+16*g+margin))*
          (256*Parent.ParentSource.Broad.Velocity.curvatureRowConstant^3*Kg^9+1)) ≤ epsilon^4 := by
      calc
        _ ≤ (16:ℝ)^4*(N^(-(t+4*e+16*g+margin))*
            ((256*Parent.ParentSource.Broad.Velocity.curvatureRowConstant^3+1)*Kg^9)) := by
          gcongr
        _ = _ := by ring
        _ ≤ N^(-4*e) := hh
        _ ≤ _ := hEpsilon4
    norm_num at hbudget ⊢
    linarith only [hbudget]

/-- The actual rounded MK4 graph mesh has a lower power with no
remaining hypothesis about its internal minimum target. -/
theorem mk4_parameters_mesh_lower_power
    {N Kg theta epsilon g t e margin d : ℝ}
    (hN : 1 ≤ N) (hKg : 1 ≤ Kg) (hKgN : Kg ≤ N^g)
    (htheta : N^(-t) ≤ theta) (hepsilon : N^(-e) ≤ epsilon)
    (hg : 0 ≤ g) (ht : 0 ≤ t) (he : 0 ≤ e) (hd : d < 1)
    (hconstant : mk4MeshFloorConstant ≤ N^margin) :
    N^(-(24*(t+4*e+16*g+margin)/(1-d)+margin)) ≤
      Submission.Lib.K4DyadicRowScales.mesh (meshIndexOf (mk4MeshTarget theta Kg epsilon) d) := by
  have h80 : (80:ℝ) ≤ N^margin := (le_max_left _ _).trans hconstant
  have hrounding : (8:ℝ) ≤ N^margin := by linarith only [h80]
  apply mk4_mesh_lower_power hN
    (mk4_target_lower_power hN hKg hKgN htheta hepsilon hg ht he hconstant) _ hd hrounding
  have hKgp : 0 < Kg := zero_lt_one.trans_le hKg
  apply (min_le_right _ _).trans
  apply (min_le_left _ _).trans
  rw [div_le_one (by positivity : (0:ℝ) < 64*Kg)]
  linarith only [hKg]

/-- The tail is chosen before all actual MK4 parameters. Only their
three scalar exponent bounds are used after the sample. -/
theorem eventually_mk4_parameters_mesh_lower_power
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {g t e margin d : ℝ} (hg : 0 ≤ g) (ht : 0 ≤ t) (he : 0 ≤ e)
    (hmargin : 0 < margin) (hd : d < 1) :
    ∀ᶠ k in atTop, ∀ Kg theta epsilon : ℝ,
      1 ≤ Kg → Kg ≤ N k^g → N k^(-t) ≤ theta → N k^(-e) ≤ epsilon →
      N k^(-(24*(t+4*e+16*g+margin)/(1-d)+margin)) ≤
        Submission.Lib.K4DyadicRowScales.mesh
          (meshIndexOf (mk4MeshTarget theta Kg epsilon) d) := by
  have hlarge := ((tendsto_rpow_atTop hmargin).comp hN).eventually
    (eventually_ge_atTop mk4MeshFloorConstant)
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  intro Kg theta epsilon hKg hKgN htheta hepsilon
  exact mk4_parameters_mesh_lower_power hk hKg hKgN htheta hepsilon hg ht he hd hc

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
