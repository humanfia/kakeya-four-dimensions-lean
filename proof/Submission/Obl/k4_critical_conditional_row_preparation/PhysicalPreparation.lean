import Submission.Obl.k4_critical_conditional_row_preparation.PhysicalSupport

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
local instance {ι : Type*} : MeasurableSpace (Option ι) := ⊤
local instance {ι : Type*} : DiscreteMeasurableSpace (Option ι) := ⟨fun _ => trivial⟩
namespace Data
variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Original-reference light-cell deletion supplies a genuine physical
continuous row law at every late sample and every positive loss. -/
theorem Valid.eventually_physical_preparation (h : cfg.Valid) (s η : ℝ)
    (hs : 0 < s) (hU : 1000 * s < cfg.U) (he₀ : 1000 * s < cfg.e₀) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ source : Measure (α × ℝ), source ≤ cfg.ρ k →
      ENNReal.ofReal (cfg.N k ^ (-(η / 100))) ≤ source univ →
      Nonempty (cfg.PhysicalPreparation k s η source) := by
  have h3s : 0 < 3 * s := by positivity
  have h3U : 3 * s ≤ cfg.U := by linarith
  obtain ⟨r, hr, hmesh⟩ := h.eventually_native_joint_inputs (3 * s) (200 * s) η
    h3s (by positivity) hη
  filter_upwards [h.eventually_history_data s hs h3U,
    h.eventually_assignment_level hs (by linarith), h.eventually_assignment_level h3s h3U,
    h.eventually_frozen_margins s hs (by linarith), h.eventually_pruning_losses η hη, hmesh]
    with k hD a deep hmarg hcost hgrid
  intro source hsource hmass
  obtain ⟨D⟩ := hD
  have hn : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
  let ξ := cfg.N k ^ (-(200 * s))
  let δ := cfg.N k ^ (-r)
  let cutoff : ENNReal := ENNReal.ofReal (cfg.N k ^ (-(η / 10)))
  let C : ENNReal := ENNReal.ofReal (27648 * cfg.K k ^ 11)
  let weights := historyReference (D.options ξ) (fun _ => ENNReal.ofReal (D.capReference ξ))
  let bin : ℝ → ℤ := fun w => ⌊w / ξ⌋
  let palette := (cfg.π k).map bin
  let control : α × ℝ → ℤ := fun p => ⌊cfg.b k p.1 3 / ξ⌋
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hn _
  have hδ : 0 < δ := Real.rpow_pos_of_pos hn _
  have hcut : 0 < cfg.N k ^ (-(η / 10)) := Real.rpow_pos_of_pos hn _
  have hcm := hmarg a deep
  have hgm := hgrid.2.2 deep
  have hsourceμ := hsource.trans (h.basic k).2.2.2.2.1
  have hb := (h.basic k).1
  have hbin : Measurable bin := Int.measurable_floor.comp (measurable_id.div_const ξ)
  have hcontrol : Measurable control := Int.measurable_floor.comp
    ((((measurable_pi_apply 3).comp hb).comp measurable_fst).div_const ξ)
  have hcap := D.original_history_bin_cap h deep source hsourceμ ξ δ hξ hδ
    (hgm.1.trans (mul_le_mul_of_nonneg_right hcm.2.1 hξ.le)) hgm.2.1 hgm.2.2 hgrid.1
  obtain ⟨τ, hτσ, hbudget, hconditional⟩ := prune_and_forget source (D.state ξ)
    (D.measurable_state h deep ξ) control hcontrol palette weights C cutoff
    (by exact ne_of_gt (ENNReal.ofReal_pos.mpr hcut)) ENNReal.ofReal_ne_top
    (D.forget (cfg.N k ^ (-s))) (measurable_of_countable _) hcap
  have hw : ∑' u, weights u ≤ ENNReal.ofReal (36 * cfg.K k ^ 4) :=
    D.reference_budget h deep ξ hξ hcm.1
  let loss : ℝ := 36 * cfg.K k ^ 4 * cfg.N k ^ (-(η / 10))
  have hloss : cutoff * ∑' u, weights u ≤ ENNReal.ofReal loss := by
    calc
      _ ≤ cutoff * ENNReal.ofReal (36 * cfg.K k ^ 4) := mul_le_mul_of_nonneg_left hw (zero_le : (0 : ENNReal) ≤ cutoff)
      _ = _ := by
        rw [← ENNReal.ofReal_mul hcut.le]
        congr 1
        dsimp [loss]
        ring
  have hbudget' : ENNReal.ofReal (cfg.N k ^ (-(η / 100))) ≤ τ univ + ENNReal.ofReal loss :=
    hmass.trans (hbudget.trans (add_le_add le_rfl hloss))
  have hsmall : ENNReal.ofReal (cfg.N k ^ (-η)) + ENNReal.ofReal loss <
      ENNReal.ofReal (cfg.N k ^ (-(η / 100))) := by
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg hn.le _) (by dsimp [loss]; positivity)]
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hn _)).mpr
    simpa only [loss, add_comm] using hcost.2.2.2
  have hτmass : ENNReal.ofReal (cfg.N k ^ (-η)) < τ univ := by
    by_contra! hnτ
    exact (not_lt_of_ge (hbudget'.trans (add_le_add hnτ le_rfl))) hsmall
  have hCc : C / cutoff ≤ ENNReal.ofReal (cfg.N k ^ η) := by
    change ENNReal.ofReal (27648 * cfg.K k ^ 11) /
      ENNReal.ofReal (cfg.N k ^ (-(η / 10))) ≤ _
    rw [← ENNReal.ofReal_div_of_pos hcut]
    exact ENNReal.ofReal_le_ofReal hcost.2.2.1
  have hpalette (v : ℤ) : palette {v} =
      cfg.π k (Ico ((v : ℝ) * ξ) (((v : ℝ) + 1) * ξ)) := by
    calc
      _ = cfg.π k {w | ⌊w / ξ⌋ = v} := by
        rw [Measure.map_apply hbin (measurableSet_singleton v)]
        congr 1
      _ = _ := congrArg (cfg.π k) (floor_bin_eq_Ico ξ v hξ)
  have hconditional' : ∀ u (v : ℤ), τ {p | D.forget (cfg.N k ^ (-s)) (D.state ξ p) = u ∧
        ⌊cfg.b k p.1 3 / ξ⌋ = v} ≤
      ENNReal.ofReal (cfg.N k ^ η) * cfg.π k (Ico ((v : ℝ) * ξ) (((v : ℝ) + 1) * ξ)) *
        τ {p | D.forget (cfg.N k ^ (-s)) (D.state ξ p) = u} := by
    intro u v
    have hc := hconditional u v
    rw [hpalette v] at hc
    apply hc.trans
    gcongr <;> exact hCc
  have hτρ : τ ≤ cfg.ρ k := hτσ.trans hsource
  have hτμ := hτρ.trans (h.basic k).2.2.2.2.1
  obtain ⟨i, hi⟩ := D.exists_parentCurrent_heavy h a deep τ hτμ (cfg.N k ^ (-η))
    (Real.rpow_nonneg hn.le _) hτmass
  refine ⟨{
    index := i
    current := D.parentCurrent τ i
    row := D.row
    measurable_row := D.measurable_row deep
    current_le_source := Measure.restrict_le_self.trans hτσ
    current_le_parent := D.parentCurrent_le_original h a deep τ hτρ i
    mass_lower := hi
    row_constraint := D.parentCurrent_row_constraint h a deep τ hτρ i η hη.le hcost.1 hcm.2.2
    conditional_cap := D.parentCurrent_conditional_cap h deep τ (ENNReal.ofReal (cfg.N k ^ η)) hconditional' i
  }⟩

end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
