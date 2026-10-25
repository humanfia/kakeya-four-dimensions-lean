-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.InternalStateBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordBudgets

open Filter
open Parent.ParentSource
open scoped ENNReal

noncomputable section

/-- An internal state budget can be displayed at any larger palette
allowance without changing the record or state cut. -/
theorem StateBudgetsAt.mono_allowance
    {N κ Krecord b budget allowance display entropy : ℝ}
    (hN : 1 ≤ N) (hallowance : allowance ≤ display)
    (h : StateBudgetsAt N κ Krecord b budget allowance entropy) :
    StateBudgetsAt N κ Krecord b budget display entropy := by
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_⟩
  exact h.2.2.2.2.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN hallowance) (by norm_num)))

/-- The actual conditional palette coefficient is paid by a small
internal power. Its exponent includes both record/state divisions. -/
theorem post_cut_palette_power
    {N b allowance entropy : ℝ} (hN : 1 ≤ N)
    (hallowance : 0 < allowance) (hb : 64*b ≤ allowance)
    (hentropy : entropy ≤ allowance/4) (hlarge : 8 ≤ N^(allowance/8)) :
    ENNReal.ofReal ((8*N^entropy)/N^(-b))/ENNReal.ofReal (N^(-b)) ≤
      ENNReal.ofReal (N^(allowance/2)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hcut : 0 < N^(-b) := Real.rpow_pos_of_pos hNp _
  rw [←ENNReal.ofReal_div_of_pos hcut]
  apply ENNReal.ofReal_le_ofReal
  calc
    ((8*N^entropy)/N^(-b))/N^(-b) = 8*N^(entropy-(-b)-(-b)) := by
      rw [Real.rpow_sub hNp,Real.rpow_sub hNp]
      ring
    _ ≤ N^(allowance/8)*N^(entropy-(-b)-(-b)) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hNp.le _)
    _ = N^(allowance/8+entropy-(-b)-(-b)) := by
      rw [←Real.rpow_add hNp]
      congr 1
      ring
    _ ≤ N^(allowance/2) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- Choose the path exponent before the sample using a possibly much
smaller internal allowance. The final state parameter may still use
the larger display allowance. All coefficients refer to the actual
native record envelope and the same cut N^(-min(budget,internal)/64). -/
theorem eventually_native_internal_state_budgets
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {budget internal display entropy : ℝ} (hbudget : 0 < budget)
    (hinternal : 0 < internal) (hdisplay : internal ≤ display)
    (hentropy : entropy ≤ internal/4) :
    let b := cutExponent budget internal;
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source tolerance : ℝ, 1 ≤ κ → κ ≤ N k^sigma → source ≤ N k^sigma →
        0 ≤ tolerance → tolerance ≤ 2*(min budget internal)/FixedSourcePowers.slack →
        StateBudgetsAt (N k) κ (Native.nativePreGeometryEnvelope κ source (N k) tolerance)
          b budget display entropy ∧
        ENNReal.ofReal ((8*N k^entropy)/N k^(-b))/ENNReal.ofReal (N k^(-b)) ≤
          ENNReal.ofReal (N k^(internal/2)) := by
  obtain ⟨sigma,hsigma,hsigma1,hbudgets⟩ :=
    eventually_native_record_state_budgets N hN hbudget hinternal hentropy
  have hNlarge : ∀ᶠ k in atTop, 1 ≤ N k := hN.eventually (eventually_ge_atTop 1)
  have hconstant : ∀ᶠ k in atTop, 8 ≤ N k^(internal/8) :=
    ((tendsto_rpow_atTop (by positivity : 0 < internal/8)).comp hN).eventually
      (eventually_ge_atTop 8)
  have hb : 64*cutExponent budget internal ≤ internal := by
    unfold cutExponent
    linarith [min_le_right budget internal]
  refine ⟨sigma,hsigma,hsigma1,?_⟩
  filter_upwards [hbudgets,hNlarge,hconstant] with k hk hNk hc
  intro κ source tolerance hκone hκ hsource htol0 htol
  exact ⟨(hk κ source tolerance hκone hκ hsource htol0 htol).mono_allowance hNk hdisplay,
    post_cut_palette_power hNk hinternal hb hentropy hc⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordBudgets
