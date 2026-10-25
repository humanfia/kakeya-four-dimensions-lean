-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleRecordBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.InternalEntropyBudget

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open Parent.ParentSource
open scoped ENNReal

noncomputable section

/-- The literal front scales give the actual record/state cut budgets,
with the small native internal allowance and the larger final display
parameter. Neither an entropy bound nor a tolerance comparison is an
input: both follow from the gain cap, grid and window choices. -/
theorem eventually_sample_record_state_budgets
    (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {κ₁ d₁ precision loss gain L δ₀ front divisor : ℝ} {Ep m C : ℕ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hd0 : 0 ≤ d₁) (hd1 : d₁ < 1)
    (hprecision : 1 ≤ precision) (hloss : 0 < loss) (hgain : 0 < gain)
    (hL : 0 < L) (hgainCap : gain ≤ gainCap tune κ₁ d₁ Ep precision loss)
    (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ)) (hδ : δ₀ ≤ gain/100)
    (hδtol : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain)
    (hC : (C:ℝ) ≤ windowOf tune κ₁ d₁ Ep precision loss gain*(m:ℝ)+1)
    (hfront : 0 < front) (hdivisor : 1 ≤ divisor) (hdivisorMax : divisor ≤ 5000)
    (htau : 0 ≤ tauOf tune δ₀ L front) :
    let display := loss*gain*L/((Ep:ℝ)+1)
    let internal := tune.budget κ₁ d₁ Ep precision loss*display/divisor
    let entropy := entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss gain δ₀ L)
    let b := RecordBudgets.cutExponent front internal
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source : ℝ, 1 ≤ κ → κ ≤ N k^sigma → source ≤ N k^sigma →
        RecordBudgets.StateBudgetsAt (N k) κ
          (Native.nativePreGeometryEnvelope κ source (N k) (2*tauOf tune δ₀ L front))
          b front display entropy ∧
        ENNReal.ofReal ((8*N k^entropy)/N k^(-b))/ENNReal.ofReal (N k^(-b)) ≤
          ENNReal.ofReal (N k^(internal/2)) := by
  let display := loss*gain*L/((Ep:ℝ)+1)
  let internal := tune.budget κ₁ d₁ Ep precision loss*display/divisor
  let entropy := entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss gain δ₀ L)
  have hEp : 0 < (Ep:ℝ)+1 := by positivity
  have hdisplay : 0 < display := by dsimp only [display]; positivity
  have hB : 0 < tune.budget κ₁ d₁ Ep precision loss := tune.budget_pos _ _ _ _ _
  have hB1 : tune.budget κ₁ d₁ Ep precision loss ≤ 1 := tune.budget_le_one _ _ _ _ _
  have hdivisor0 : 0 < divisor := zero_lt_one.trans_le hdivisor
  have hinternal : 0 < internal := by dsimp only [internal]; positivity
  have hinternalDisplay : internal ≤ display := by
    dsimp only [internal]
    rw [div_le_iff₀ hdivisor0]
    calc
      _ ≤ 1*display := mul_le_mul_of_nonneg_right hB1 hdisplay.le
      _ ≤ display*divisor := by nlinarith only [mul_le_mul_of_nonneg_left hdivisor hdisplay.le]
  have hentropy : entropy ≤ internal/4 := front_entropy_le_internal_quarter
    (mul_nonneg hB.le hdisplay.le) hdivisor0 hdivisorMax
    (front_entropy_le_internal_power tune hκ hκ1 hd0 hd1 hprecision hloss hgain hL.le hgainCap
      hm hgm hδ hC)
  have htol : 2*tauOf tune δ₀ L front ≤ 2*min front internal/FixedSourcePowers.slack := by
    have hh := doubled_tau_fits_internal_budget tune hloss hgain hL hfront hdivisor0 hdivisorMax hδtol
    exact hh.trans (div_le_div_of_nonneg_left (by positivity)
      FixedSourcePowers.slack_positive hslack)
  obtain ⟨sigma,hsigma,hsigma1,hbudgets⟩ := RecordBudgets.eventually_native_internal_state_budgets
    N hN hfront hinternal hinternalDisplay hentropy
  refine ⟨sigma,hsigma,hsigma1,?_⟩
  filter_upwards [hbudgets] with k hk
  intro κ source hκone hκN hsource
  exact hk κ source (2*tauOf tune δ₀ L front) hκone hκN hsource (by positivity) htol

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
