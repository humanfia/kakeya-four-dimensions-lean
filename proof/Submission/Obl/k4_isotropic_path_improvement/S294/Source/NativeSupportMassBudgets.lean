-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeSupportMassBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootCosts
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.PostStateMassBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open Parent.Qualification.PhysicalModel (OriginalRootScales)
open scoped ENNReal

noncomputable section

/-- The exact support deletion cost follows from scalar powers. Both
terms are charged in the original full-root reference units. -/
theorem original_root_support_loss_le
    (s : OriginalRootScales) {N h w c t p r target margin : ℝ}
    (hN : 1 ≤ N) (hH : s.H ≤ N^h) (hwidths : (s.W.card:ℝ) ≤ N^w)
    (hcensus : s.Kcensus ≤ N^c) (hsteps : (2:ℝ)^s.steps ≤ N^t)
    (hprior : N^p ≤ s.Hprior) (hrate : s.rate ≤ N^(-r))
    (hconstant : (300*7^8:ℝ) ≤ N^margin)
    (hpriorBudget : h+w+2*margin+target ≤ p)
    (hrateBudget : c+3*t+w+margin+target ≤ r) :
    s.supportLoss ≤ ENNReal.ofReal (N^(-target)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hH0 : 0 ≤ s.H := zero_le_one.trans s.hH
  have hKc0 : 0 ≤ s.Kcensus := zero_le_one.trans s.hKcensus
  have hrate0 : 0 ≤ s.rate := s.hrate.le
  have hfirst : (300*7^8*s.H)*(s.W.card:ℝ)/s.Hprior ≤ N^(-(target+margin)) := by
    calc
      _ ≤ (N^margin*N^h)*N^w/N^p := by gcongr
      _ = N^(margin+h+w-p) := by
        rw [←Real.rpow_add hNp,←Real.rpow_add hNp,←Real.rpow_sub hNp]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hpriorBudget])
  have hsecond : (s.Kcensus*((2:ℝ)^s.steps)^3)*((s.W.card:ℝ)*s.rate) ≤
      N^(-(target+margin)) := by
    have h3 : (N^t)^3=N^(3*t) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
      congr 1
      ring
    calc
      _ ≤ (N^c*(N^t)^3)*(N^w*N^(-r)) := by gcongr
      _ = N^(c+3*t+w-r) := by
        rw [h3,←Real.rpow_add hNp,←Real.rpow_add hNp,←Real.rpow_add hNp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hrateBudget])
  have htwo : (2:ℝ) ≤ N^margin := (by norm_num : (2:ℝ) ≤ 300*7^8).trans hconstant
  unfold Parent.Qualification.PhysicalModel.OriginalRootScales.supportLoss
  calc
    _ ≤ ENNReal.ofReal (N^(-(target+margin)))+ENNReal.ofReal (N^(-(target+margin))) :=
      add_le_add (ENNReal.ofReal_le_ofReal hfirst) (ENNReal.ofReal_le_ofReal hsecond)
    _ = ENNReal.ofReal (2*N^(-(target+margin))) := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      calc
        _ ≤ N^margin*N^(-(target+margin)) :=
          mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hNp.le _)
        _ = _ := by rw [←Real.rpow_add hNp]; congr 1; ring)

/-- The support tail is chosen before every root, row and scale
package. No support selection or retained-mass oracle is required. -/
theorem eventually_original_root_support_loss_le
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {h w c t p r target margin : ℝ} (hmargin : 0 < margin)
    (hpriorBudget : h+w+2*margin+target ≤ p)
    (hrateBudget : c+3*t+w+margin+target ≤ r) :
    ∀ᶠ k in atTop, ∀ s : OriginalRootScales,
      s.H ≤ N k^h → (s.W.card:ℝ) ≤ N k^w → s.Kcensus ≤ N k^c →
      (2:ℝ)^s.steps ≤ N k^t → N k^p ≤ s.Hprior → s.rate ≤ N k^(-r) →
      s.supportLoss ≤ ENNReal.ofReal (N k^(-target)) := by
  have hlarge := ((tendsto_rpow_atTop hmargin).comp hN).eventually
    (eventually_ge_atTop (300*7^8:ℝ))
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  intro s hH hwidths hcensus hsteps hprior hrate
  exact original_root_support_loss_le s hk hH hwidths hcensus hsteps hprior hrate hc
    hpriorBudget hrateBudget

/-- A scalar support bound pays the exact post-state support charge,
including the regularity retention factor and actual path coefficient. -/
theorem original_root_support_charge_le
    (s : OriginalRootScales) {N κ regularity target gap : ℝ}
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hκN : κ ≤ N^gap)
    (hgap : regularity+2*gap ≤ target) (hlarge : (1024:ℝ)*10002 ≤ N^gap)
    (hregularity : s.regularityFactor ≤ ENNReal.ofReal (N^regularity))
    (hsupport : s.supportLoss ≤ ENNReal.ofReal (N^(-target))) :
    s.regularityFactor*s.supportLoss ≤ ENNReal.ofReal (κ⁻¹/1024) := by
  apply le_trans _ (post_state_exception_cost_le hN hκ hκN hgap hgap hlarge hregularity hsupport)
  apply mul_le_mul' le_rfl
  have hh : s.supportLoss ≤ (10000:ENNReal)*s.supportLoss := by
    simpa only [one_mul] using mul_le_mul' (by norm_num : (1:ENNReal) ≤ 10000)
      (le_refl s.supportLoss)
  exact hh.trans (le_add_left le_rfl)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
