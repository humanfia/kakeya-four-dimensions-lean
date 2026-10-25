-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.FixedSourcePowers

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordBudgets

open Filter
open Parent.ParentSource
open scoped ENNReal

noncomputable section

/-- A single later cut exponent must fit BOTH the arbitrary narrow
prediction budget and the fixed final palette allowance. -/
def cutExponent (budget allowance : ℝ) : ℝ := min budget allowance/64

theorem cutExponent_pos {budget allowance : ℝ}
    (hbudget : 0 < budget) (hallowance : 0 < allowance) :
    0 < cutExponent budget allowance := div_pos (lt_min hbudget hallowance) (by norm_num)

/-- The source's literal record-deletion, state-retention, strip and
palette bounds at one sample. -/
def StateBudgetsAt (N κ Krecord b budget allowance entropy : ℝ) : Prop :=
    0 < N^(-b) ∧
    N^(-b)*(⌈Krecord^12⌉₊:ℝ) ≤ κ⁻¹/1024 ∧
    (6561:ℝ)*N^(-b) ≤ κ⁻¹/1024 ∧
    ENNReal.ofReal ((8*(2*N^(-budget)))/N^(-b))/ENNReal.ofReal (N^(-b)) ≤
      (1/2000000000000:ENNReal) ∧
    ENNReal.ofReal ((8*N^entropy)/N^(-b))/ENNReal.ofReal (N^(-b)) ≤
      ENNReal.ofReal (N^allowance/4)

/-- Exact scalar budgets for the actual original-record cut and the
6561-option final state keep. The palette factor and front fraction are
those of the source producer; the record bound is on its genuine K^12. -/
theorem record_cut_budgets
    {N κ Krecord b budget allowance entropy : ℝ}
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hK : 1 ≤ Krecord) (hb : 0 < b)
    (hbudget : 64*b ≤ budget) (hallowance : 64*b ≤ allowance)
    (hentropy : entropy ≤ allowance/4)
    (hκN : κ ≤ N^(b/4)) (hrecord : Krecord^12 ≤ N^(b/4))
    (hlarge : 32000000000000 ≤ N^(b/4)) :
    StateBudgetsAt N κ Krecord b budget allowance entropy := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hcut : 0 < N^(-b) := Real.rpow_pos_of_pos hNp _
  have hsmall : N^(-(b/4)) ≤ 1/32000000000000 := by
    rw [Real.rpow_neg hNp.le]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hlarge
  have hceil : (⌈Krecord^12⌉₊:ℝ) ≤ 2*N^(b/4) := by
    have hK0 : 0 ≤ Krecord := by linarith
    have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ Krecord^12)
    linarith
  have hcost : N^(-b)*(⌈Krecord^12⌉₊:ℝ)*κ ≤ 1/1024 := by
    calc
      _ ≤ N^(-b)*(2*N^(b/4))*N^(b/4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hceil hcut.le) hκN hκp.le (by positivity)
      _ = 2*N^(-b+b/4+b/4) := by
        rw [Real.rpow_add hNp,Real.rpow_add hNp]
        ring
      _ ≤ 2*N^(-(b/4)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by norm_num)
      _ ≤ 1/1024 := by linarith
  have hkeepCost : (6561:ℝ)*N^(-b)*κ ≤ 1/1024 := by
    calc
      _ ≤ 6561*N^(-b)*N^(b/4) := mul_le_mul_of_nonneg_left hκN (by positivity)
      _ = 6561*N^(-b+b/4) := by rw [Real.rpow_add hNp]; ring
      _ ≤ 6561*N^(-(b/4)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by norm_num)
      _ ≤ 1/1024 := by linarith
  have hstrip : ((8*(2*N^(-budget)))/N^(-b))/N^(-b) ≤ 1/2000000000000 := by
    calc
      _ = 16*(N^(-budget)/N^(-b)/N^(-b)) := by ring
      _ = 16*N^((-budget)-(-b)-(-b)) := by rw [Real.rpow_sub hNp,Real.rpow_sub hNp]
      _ ≤ 16*N^(-(b/4)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by norm_num)
      _ ≤ _ := by linarith
  have hpal : ((8*N^entropy)/N^(-b))/N^(-b) ≤ N^allowance/4 := by
    have hp : 0 < N^allowance := Real.rpow_pos_of_pos hNp _
    have hratio : (((8*N^entropy)/N^(-b))/N^(-b))/N^allowance ≤ 1/4 := by
      calc
        (((8*N^entropy)/N^(-b))/N^(-b))/N^allowance =
            8*(N^entropy/N^(-b)/N^(-b)/N^allowance) := by ring
        _ = 8*N^(entropy-(-b)-(-b)-allowance) := by
          rw [Real.rpow_sub hNp,Real.rpow_sub hNp,Real.rpow_sub hNp]
        _ ≤ 8*N^(-(b/4)) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by norm_num)
        _ ≤ 1/4 := by linarith
    have hh := (div_le_iff₀ hp).mp hratio
    linarith
  refine ⟨hcut,?_,?_,?_,?_⟩
  · apply (mul_le_mul_iff_right₀ hκp).mp
    have heq : κ*(κ⁻¹/1024)=1/1024 := by field_simp
    rw [heq]
    simpa only [mul_comm] using hcost
  · apply (mul_le_mul_iff_right₀ hκp).mp
    have heq : κ*(κ⁻¹/1024)=1/1024 := by field_simp
    rw [heq]
    simpa only [mul_comm] using hkeepCost
  · calc
      _ = ENNReal.ofReal (((8*(2*N^(-budget)))/N^(-b))/N^(-b)) :=
        (ENNReal.ofReal_div_of_pos hcut).symm
      _ ≤ ENNReal.ofReal (1/2000000000000:ℝ) := ENNReal.ofReal_le_ofReal hstrip
      _ = _ := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
  · calc
      _ = ENNReal.ofReal (((8*N^entropy)/N^(-b))/N^(-b)) :=
        (ENNReal.ofReal_div_of_pos hcut).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hpal

/-- The actual native pregeometry envelope fits all record/state
budgets. The path exponent is chosen before k and every coefficient;
the cutoff fits both the front prediction exponent and final K.
There is no abstract record-count or palette-cap premise. -/
theorem eventually_native_record_state_budgets
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {budget allowance entropy : ℝ} (hbudget : 0 < budget)
    (hallowance : 0 < allowance) (hentropy : entropy ≤ allowance/4) :
    let b := cutExponent budget allowance;
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source tolerance : ℝ, 1 ≤ κ → κ ≤ N k^sigma → source ≤ N k^sigma →
        0 ≤ tolerance → tolerance ≤ 2*(min budget allowance)/FixedSourcePowers.slack →
        StateBudgetsAt (N k) κ (Native.nativePreGeometryEnvelope κ source (N k) tolerance)
          b budget allowance entropy := by
  let b := cutExponent budget allowance
  have hb : 0 < b := cutExponent_pos hbudget hallowance
  have hmin : 0 < min budget allowance := lt_min hbudget hallowance
  have hbBudget : 64*b ≤ budget := by
    dsimp only [b,cutExponent]
    linarith [min_le_left budget allowance]
  have hbAllowance : 64*b ≤ allowance := by
    dsimp only [b,cutExponent]
    linarith [min_le_right budget allowance]
  obtain ⟨sigma0,hsigma0,hsigma01,hEnvelope⟩ :=
    FixedSourcePowers.eventually_native_envelope_power N hN hmin
  let sigma := min sigma0 (min 1 (b/4))
  have hsigma : 0 < sigma := lt_min hsigma0 (lt_min one_pos (by positivity))
  have hsigma1 : sigma ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hsigma0le : sigma ≤ sigma0 := min_le_left _ _
  have hsigmaB : sigma ≤ b/4 := (min_le_right _ _).trans (min_le_right _ _)
  have hNlarge : ∀ᶠ k in atTop, 1 ≤ N k := hN.eventually (eventually_ge_atTop 1)
  have hconstant : ∀ᶠ k in atTop, 32000000000000 ≤ N k^(b/4) :=
    ((tendsto_rpow_atTop (by positivity : 0 < b/4)).comp hN).eventually
      (eventually_ge_atTop 32000000000000)
  refine ⟨sigma,hsigma,hsigma1,?_⟩
  filter_upwards [hNlarge,hconstant,hEnvelope] with k hNk hlarge henv
  intro κ source tolerance hκone hκ hsource htol0 htol
  have hκ0 : κ ≤ N k^sigma0 := hκ.trans
    (Real.rpow_le_rpow_of_exponent_le hNk hsigma0le)
  have hsource0 : source ≤ N k^sigma0 := hsource.trans
    (Real.rpow_le_rpow_of_exponent_le hNk hsigma0le)
  have hEnvelopePower := henv κ source tolerance hκone hκ0 hsource0 htol
  have hEnvelopeOne : 1 ≤ Native.nativePreGeometryEnvelope κ source (N k) tolerance :=
    (by norm_num : (1:ℝ)≤2304).trans
      (Native.native_pre_geometry_envelope_bounds hκone hNk htol0).1
  have hPower : 12 ≤ FixedSourcePowers.power := by
    unfold FixedSourcePowers.power
    omega
  have hrecord : (Native.nativePreGeometryEnvelope κ source (N k) tolerance)^12 ≤ N k^(b/4) := by
    calc
      _ ≤ (Native.nativePreGeometryEnvelope κ source (N k) tolerance)^FixedSourcePowers.power :=
        pow_le_pow_right₀ hEnvelopeOne hPower
      _ ≤ N k^((min budget allowance)/256) := hEnvelopePower
      _ = _ := by
        congr 1
        dsimp only [b,cutExponent]
        ring
  exact record_cut_budgets hNk hκone hEnvelopeOne hb hbBudget hbAllowance hentropy
    (hκ.trans (Real.rpow_le_rpow_of_exponent_le hNk hsigmaB)) hrecord hlarge


/-- The skeleton's two freely chosen pure tolerances fit the minimum
budget. Its grid cap pays the final palette allowance even if the late
front prediction exponent is comparatively large. -/
theorem pure_tolerance_fits_record_budget
    {gridTolerance budget allowance : ℝ} (hbudget : 0 < budget)
    (hallowance : 0 < allowance)
    (hgrid : gridTolerance ≤ allowance/(10000*FixedSourcePowers.slack)) :
    2*min gridTolerance (budget/(1024*FixedSourcePowers.slack)) ≤
      2*(min budget allowance)/FixedSourcePowers.slack := by
  have hs := FixedSourcePowers.slack_positive
  have hB : min gridTolerance (budget/(1024*FixedSourcePowers.slack))*
      FixedSourcePowers.slack ≤ budget/1024 := by
    calc
      _ ≤ (budget/(1024*FixedSourcePowers.slack))*FixedSourcePowers.slack :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le
      _ = _ := by field_simp
  have hA : min gridTolerance (budget/(1024*FixedSourcePowers.slack))*
      FixedSourcePowers.slack ≤ allowance/10000 := by
    calc
      _ ≤ (allowance/(10000*FixedSourcePowers.slack))*FixedSourcePowers.slack :=
        mul_le_mul_of_nonneg_right ((min_le_left _ _).trans hgrid) hs.le
      _ = _ := by field_simp
  rw [le_div_iff₀ hs]
  have hboth : min gridTolerance (budget/(1024*FixedSourcePowers.slack))*
      FixedSourcePowers.slack ≤ min budget allowance := le_min
    (hB.trans (by linarith)) (hA.trans (by linarith))
  nlinarith

/-- The real record deletion bound in its exact original-law ENNReal
form used by the global ancestor record source. -/
theorem StateBudgetsAt.record_loss
    {N κ Krecord b budget allowance entropy : ℝ}
    (h : StateBudgetsAt N κ Krecord b budget allowance entropy) :
    ENNReal.ofReal (N^(-b))*(⌈Krecord^12⌉₊:ENNReal) ≤ ENNReal.ofReal (κ⁻¹/1024) := by
  have hh := ENNReal.ofReal_le_ofReal h.2.1
  simpa only [ENNReal.ofReal_mul h.1.le,ENNReal.ofReal_natCast] using hh

/-- The same quantitative keep budget in the literal 6561-option law
units of the final state producer. -/
theorem StateBudgetsAt.state_loss
    {N κ Krecord b budget allowance entropy : ℝ}
    (h : StateBudgetsAt N κ Krecord b budget allowance entropy) :
    (6561:ENNReal)*ENNReal.ofReal (N^(-b)) ≤ ENNReal.ofReal (κ⁻¹/1024) := by
  have hh := ENNReal.ofReal_le_ofReal h.2.2.1
  simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤6561),ENNReal.ofReal_ofNat] using hh


end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordBudgets
