/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, DerivativeListPreparation.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.CoefficientCount
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.SplitInterfaces

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

/-- A deletion estimate retains mass in the original measure, without normalization. -/
theorem restrict_mass_after_deletion {β : Type*} [MeasurableSpace β]
    (μ : Measure β) {E G : Set β} (hE : MeasurableSet E) (hG : MeasurableSet G)
    (hGE : G ⊆ E) (hfull : μ Eᶜ = 0) {target bad lower : ℝ}
    (htarget : 0 ≤ target) (hbad : 0 ≤ bad)
    (hlower : ENNReal.ofReal lower ≤ μ univ)
    (hdelete : μ (E \ G) ≤ ENNReal.ofReal bad) (hbudget : target + bad ≤ lower) :
    ENNReal.ofReal target ≤ (μ.restrict G) univ := by
  rw [Measure.restrict_apply_univ]
  have htotal : μ E = μ univ := by
    simpa only [hfull, add_zero] using measure_add_measure_compl (μ := μ) hE
  have hsplit : μ G + μ (E \ G) = μ univ := by
    simpa only [union_eq_right.mpr hGE, htotal] using
      measure_add_sdiff (μ := μ) hG.nullMeasurableSet E
  apply ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top
  calc
    ENNReal.ofReal target + ENNReal.ofReal bad = ENNReal.ofReal (target + bad) :=
      (ENNReal.ofReal_add htarget hbad).symm
    _ ≤ ENNReal.ofReal lower := ENNReal.ofReal_le_ofReal hbudget
    _ ≤ μ univ := hlower
    _ = μ G + μ (E \ G) := hsplit.symm
    _ ≤ μ G + ENNReal.ofReal bad := add_le_add le_rfl hdelete

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The per-label coefficient lists retain a power-sized part of the original residual. -/
theorem Valid.eventually_evaluation_lists (h : cfg.Valid) {s : ℝ} (hs : 0 < s)
    (hsU : s ≤ cfg.U) (hse : s < cfg.e₀) (hs1 : s < 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, cfg.EvaluationListsAt k s η := by
  obtain ⟨θ, hθ, hlists⟩ := h.eventually_label_derivative_lists hs hsU hse hs1
    (show 2 * s ≤ 200 * s by linarith) hη
  have hnum := Submission.Obl.k4_profile_density_bounds.eventually_sum_lt_inv
    (fun k => le_trans (by norm_num) (h.scale k)) h.scale_limit
    h.subpower.1 h.subpower.2 0 hη hθ (show (0 : ℝ) ≤ 1 by norm_num)
  filter_upwards [hlists, h.eventually_goodSet_full hs hsU,
    h.eventually_B_measurable hs hsU, hnum] with k hk hfull hBm hbudget
  obtain ⟨G, Λ, hGm, hGsub, hdelete, hcard, hmem⟩ := hk
  have hρμ := (h.basic k).2.2.2.2.1
  have hρfull : cfg.ρ k (cfg.goodSet k s)ᶜ = 0 :=
    le_antisymm ((hρμ _).trans_eq hfull) bot_le
  have hGd := cfg.measurableSet_goodSet k (h.basic k).1 s hBm
  have hmass : ENNReal.ofReal (cfg.N k ^ (-η)) ≤ ((cfg.ρ k).restrict G) univ := by
    apply restrict_mass_after_deletion (cfg.ρ k) hGd hGm hGsub hρfull
      (Real.rpow_nonneg (by linarith [h.scale k]) _)
      (Real.rpow_nonneg (by linarith [h.scale k]) _)
      (h.basic k).2.2.2.2.2.2.1 hdelete
    simpa only [pow_zero, mul_one, one_mul] using hbudget.le
  refine ⟨(cfg.ρ k).restrict G, Λ, Measure.restrict_le_self, hmass, hcard, ?_⟩
  intro i
  filter_upwards [ae_restrict_mem hGm] with p hp
  exact hmem i p hp

end Data

/-- A fixed sufficiently small depth works for every requested list loss. -/
theorem derivative_list_preparation : DerivativeListPreparation := by
  intro _hRow _hMatch α inst cfg h
  let s := min (min cfg.U cfg.e₀) 1 / 2000
  have hs : 0 < s := div_pos (lt_min (lt_min h.depth_pos h.defect_pos) zero_lt_one)
    (by norm_num)
  have hU : 2000 * s ≤ cfg.U := by
    dsimp [s]
    linarith [min_le_left (min cfg.U cfg.e₀) (1 : ℝ), min_le_left cfg.U cfg.e₀]
  have he : 2000 * s ≤ cfg.e₀ := by
    dsimp [s]
    linarith [min_le_left (min cfg.U cfg.e₀) (1 : ℝ), min_le_right cfg.U cfg.e₀]
  have h1 : 2000 * s ≤ 1 := by
    dsimp [s]
    linarith [min_le_right (min cfg.U cfg.e₀) (1 : ℝ)]
  have hsU : 1000 * s < cfg.U := by linarith
  have hse : 1000 * s < cfg.e₀ := by linarith
  have hs1 : s < 1 := by linarith
  refine ⟨s, hs, hsU, hse, hs1, ?_⟩
  intro η hη
  exact (h.eventually_evaluation_lists hs (by linarith) (by linarith) hs1 hη).frequently

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
