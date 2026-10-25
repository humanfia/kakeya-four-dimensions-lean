-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.PostStateMassBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.InternalStateBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open scoped ENNReal

noncomputable section

/-- The regularity factor times the two terminal exceptions fits an
original-reference loss. The path factor is included in the exponent
comparison, so the estimate is uniform over the actual path. -/
theorem post_state_exception_cost_le
    {N κ display regularity native gap : ℝ} {Pfac eta : ENNReal}
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hκN : κ ≤ N^gap)
    (hdisplay : regularity+2*gap ≤ display) (hnative : regularity+2*gap ≤ native)
    (hlarge : (1024:ℝ)*10002 ≤ N^gap)
    (hPfac : Pfac ≤ ENNReal.ofReal (N^regularity))
    (heta : eta ≤ ENNReal.ofReal (N^(-native))) :
    Pfac*(ENNReal.ofReal (2/N^display)+10000*eta) ≤ ENNReal.ofReal (κ⁻¹/1024) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hdecay : N^(-gap) ≤ 1/((1024:ℝ)*10002) := by
    rw [Real.rpow_neg hNp.le]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hlarge
  have hterm (a c : ℝ) : N^regularity*(c*N^(-a))*N^gap=c*N^(regularity-a+gap) := by
    rw [Real.rpow_add hNp,Real.rpow_sub hNp,Real.rpow_neg hNp.le]
    ring
  have hcost : (N^regularity*(2/N^display+10000*N^(-native)))*κ ≤ 1/1024 := by
    calc
      _ ≤ (N^regularity*(2/N^display+10000*N^(-native)))*N^gap :=
        mul_le_mul_of_nonneg_left hκN (by positivity)
      _ = 2*N^(regularity-display+gap)+10000*N^(regularity-native+gap) := by
        rw [mul_add,add_mul]
        have heq : 2/N^display=2*N^(-display) := by
          rw [Real.rpow_neg hNp.le,div_eq_mul_inv]
        rw [heq,hterm,hterm]
      _ ≤ 2*N^(-gap)+10000*N^(-gap) := add_le_add
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
          (by norm_num))
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
          (by norm_num))
      _ ≤ 1/1024 := by linarith
  have hreal : N^regularity*(2/N^display+10000*N^(-native)) ≤ κ⁻¹/1024 := by
    apply (mul_le_mul_iff_right₀ hκp).mp
    have heq : κ*(κ⁻¹/1024)=1/1024 := by field_simp
    rw [heq]
    simpa only [mul_comm] using hcost
  calc
    _ ≤ ENNReal.ofReal (N^regularity)*
        (ENNReal.ofReal (2/N^display)+10000*ENNReal.ofReal (N^(-native))) :=
      mul_le_mul' hPfac (add_le_add le_rfl (mul_le_mul' le_rfl heta))
    _ = ENNReal.ofReal (N^regularity*(2/N^display+10000*N^(-native))) := by
      rw [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤N^regularity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10000)]
      norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- A positive exponent gap supplies the exact terminal exception
budget before the actual sample and all path coefficients. -/
theorem eventually_post_state_exception_cost
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {display regularity native : ℝ}
    (hdisplay : regularity < display) (hnative : regularity < native) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ : ℝ, 1 ≤ κ → κ ≤ N k^sigma → ∀ Pfac eta : ENNReal,
        Pfac ≤ ENNReal.ofReal (N k^regularity) → eta ≤ ENNReal.ofReal (N k^(-native)) →
        Pfac*(ENNReal.ofReal (2/N k^display)+10000*eta) ≤ ENNReal.ofReal (κ⁻¹/1024) := by
  let sigma := min 1 (min (display-regularity) (native-regularity)/4)
  have hsigma : 0 < sigma := lt_min one_pos
    (div_pos (lt_min (sub_pos.mpr hdisplay) (sub_pos.mpr hnative)) (by norm_num))
  have hsigmaDisplay : regularity+2*sigma ≤ display := by
    have h1 := min_le_right 1 (min (display-regularity) (native-regularity)/4)
    have h2 := min_le_left (display-regularity) (native-regularity)
    dsimp only [sigma]
    linarith
  have hsigmaNative : regularity+2*sigma ≤ native := by
    have h1 := min_le_right 1 (min (display-regularity) (native-regularity)/4)
    have h2 := min_le_right (display-regularity) (native-regularity)
    dsimp only [sigma]
    linarith
  have hlarge := ((tendsto_rpow_atTop hsigma).comp hN).eventually
    (eventually_ge_atTop ((1024:ℝ)*10002))
  refine ⟨sigma,hsigma,min_le_left _ _,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hconstant
  intro κ hκ hκN Pfac eta hPfac heta
  exact post_state_exception_cost_le hk hκ hκN hsigmaDisplay hsigmaNative hconstant hPfac heta

/-- The exact final mass premise of sample assembly follows from the
terminal exception budget, the whole-state support charge, and the
already paid state-retention charge. -/
theorem post_state_mass_budget
    {N κ Krecord b budget allowance entropy : ℝ} {Pfac eta chargeR mass : ENNReal}
    (hκ : 0 < κ)
    (hstates : RecordBudgets.StateBudgetsAt N κ Krecord b budget allowance entropy)
    (hexception : Pfac*(ENNReal.ofReal (2/N^allowance)+10000*eta) ≤
      ENNReal.ofReal (κ⁻¹/1024))
    (hcharge : chargeR ≤ ENNReal.ofReal (κ⁻¹/1024))
    (hmass : ENNReal.ofReal (κ⁻¹/64) ≤ mass) :
    Pfac*(ENNReal.ofReal (2/N^allowance)+10000*eta)+chargeR+
      6561*ENNReal.ofReal (N^(-b)) ≤ mass := by
  calc
    _ ≤ ENNReal.ofReal (κ⁻¹/1024)+ENNReal.ofReal (κ⁻¹/1024)+
        ENNReal.ofReal (κ⁻¹/1024) :=
      add_le_add (add_le_add hexception hcharge) hstates.state_loss
    _ = ENNReal.ofReal (κ⁻¹/1024+κ⁻¹/1024+κ⁻¹/1024) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (κ⁻¹/64) := ENNReal.ofReal_le_ofReal (by
      have : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
      linarith)
    _ ≤ mass := hmass

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
