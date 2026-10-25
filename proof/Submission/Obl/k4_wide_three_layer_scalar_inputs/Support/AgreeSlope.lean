import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.AgreeMatch

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

namespace ComparedBlock

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H R : ℝ}

/-- Only occupied source cells require a slope bound. One original good
occurrence bounds the reference base point and hence every target slope. -/
theorem occupied_slope_bound (CB : ComparedBlock cfg k s u v χ H) (P : AgreeParams)
    (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k)
    (hχ : 0 < χ) (hχq : χ ≤ CB.frame.q) (hχ1 : χ ≤ 1)
    (hδt : 0 < P.δt) (hδt1 : P.δt ≤ 1) (hδU : 0 ≤ P.δU) (hδU1 : P.δU ≤ 1)
    (sr : CB.Γ × ℤ) (c : ℤ) (γ' : CB.Γ)
    (hsource : CB.lam {p | CB.src p = sr ∧ CB.cell P p = c} ≠ 0) :
    |CB.cδ₁ P sr c γ'| + 2 * |CB.cδ₂ sr γ'| * (cfg.K k + P.δU) ≤ 24 * H * cfg.K k := by
  have hq : 0 < CB.frame.q := by dsimp [frame, blockFrame]; positivity
  have hK0 : 0 ≤ cfg.K k := zero_le_one.trans hK
  have hH : 0 ≤ H := zero_le_one.trans CB.H_one
  have hmass : CB.lam {p | CB.src p = sr ∧ CB.cell P p = c ∧ CB.Good p} =
      CB.lam {p | CB.src p = sr ∧ CB.cell P p = c} := by
    apply measure_congr
    refine Filter.Eventually.set_eq ?_
    filter_upwards [CB.ae_good] with p hp
    simp only [hp, and_true]
  have hne : CB.lam {p | CB.src p = sr ∧ CB.cell P p = c ∧ CB.Good p} ≠ 0 := by
    rw [hmass]
    exact hsource
  obtain ⟨p, hsrc, hcell, hp⟩ := nonempty_of_measure_ne_zero hne
  have hcls : CB.cls p = sr.1 := congrArg Prod.fst hsrc
  have href := CB.good_refZ P hB hN hK CB.hL hχ hδt hp
  rw [hcls, hcell] at href
  obtain ⟨hzt, hzZ, -, -, -⟩ := CB.good_bounds hB hN hK CB.hL hp
  have hzt' : |CB.frame.zt p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hzt.1], hzt.2⟩
  have hx : |refX P c| ≤ 2 := by
    calc _ = |CB.frame.zt p.2 - (CB.frame.zt p.2 - refX P c)| := by congr 1; ring
      _ ≤ |CB.frame.zt p.2| + |CB.frame.zt p.2 - refX P c| := abs_sub _ _
      _ ≤ 2 := by linarith [href.1]
  have hχq' : χ / CB.frame.q ≤ 1 := (div_le_one hq).mpr hχq
  have hprod : P.δt * (2 * cfg.K k + χ) ≤ 2 * cfg.K k + 1 := by
    calc _ ≤ 1 * (2 * cfg.K k + 1) :=
          mul_le_mul hδt1 (by linarith) (by positivity) (by positivity)
      _ = _ := one_mul _
  have hy : |CB.refZ P sr.1 c| ≤ 4 * cfg.K k := by
    calc _ = |CB.frame.zZ (cfg.b k p.1) p.2 -
          (CB.frame.zZ (cfg.b k p.1) p.2 - CB.refZ P sr.1 c)| := by congr 1; ring
      _ ≤ |CB.frame.zZ (cfg.b k p.1) p.2| +
          |CB.frame.zZ (cfg.b k p.1) p.2 - CB.refZ P sr.1 c| := abs_sub _ _
      _ ≤ 4 * cfg.K k := by linarith [href.2]
  have hlin : ∀ γ : CB.Γ, |lin1 (CB.tc γ) (refX P c) (CB.refZ P sr.1 c)| ≤ 7 * H * cfg.K k := by
    intro γ
    unfold lin1
    calc _ ≤ |CB.tc γ 0| + |CB.tc γ 1| * |refX P c| + |CB.tc γ 2| * |CB.refZ P sr.1 c| := by
          simpa only [abs_mul] using abs_add_three (CB.tc γ 0) (CB.tc γ 1 * refX P c)
            (CB.tc γ 2 * CB.refZ P sr.1 c)
      _ ≤ H + H * 2 + H * (4 * cfg.K k) := by gcongr <;> exact CB.tc_bd _ _
      _ ≤ 7 * H * cfg.K k := by nlinarith [mul_le_mul_of_nonneg_left hK hH]
  have h₁ : |CB.cδ₁ P sr c γ'| ≤ 14 * H * cfg.K k := by
    exact (abs_sub _ _).trans (by linarith [hlin sr.1, hlin γ'])
  have h₂ : |CB.cδ₂ sr γ'| ≤ 2 * H :=
    (abs_sub _ _).trans (by linarith [CB.tc_bd sr.1 3, CB.tc_bd γ' 3])
  calc _ ≤ 14 * H * cfg.K k + 2 * (2 * H) * (cfg.K k + 1) := by gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hK hH]

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
