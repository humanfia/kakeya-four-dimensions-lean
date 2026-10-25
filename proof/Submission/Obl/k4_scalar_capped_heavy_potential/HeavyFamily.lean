import Submission.Obl.k4_scalar_capped_heavy_potential.GroupPruning
import Submission.Obl.k4_scalar_capped_heavy_potential.EfficientSelection
import Submission.Lib.K4ScalarActualSwitching.OriginalBaseArea

namespace Submission.Obl.k4_scalar_capped_heavy_potential

open MeasureTheory Set
open Submission.Lib.K4ScalarActualSwitching

noncomputable section

/-- The complete original-measure bookkeeping for the heavy-group
selection. Only the geometric occupied-area floor and joint-cell budget
remain as inputs. Every selected measure is a restriction of the original
incidence law, and its prior is the unchanged trajectory prior. -/
theorem select_heavy_original_group {α Q B : Type*}
    [MeasurableSpace α] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (ν : Measure α) [IsFiniteMeasure ν]
    (μ : Measure (α × ℝ)) [IsFiniteMeasure μ]
    (state : α × ℝ → Q) (hs : Measurable state)
    (group : α → ℤ) (hg : Measurable group)
    (lists : Q → Finset ℤ) (hlist : ∀ q, ((lists q).card : ENNReal) ≤ 7)
    (F : Finset ℤ) (hglobal : ∀ᵐ p ∂μ, group p.1 ∈ F)
    (cells : ℤ → Finset B)
    {H C ξ h R β : ℝ} (hH : 1 ≤ H) (hC : 0 < C) (hξ : 0 < ξ)
    (hh : 0 < h) (hR : 0 < R) (hβ : 0 < β) (hν : 0 < (ν univ).toReal)
    (hmass : h * (ν univ).toReal / H ≤ (μ univ).toReal)
    (hfloor : ∀ c ∈ F,
      let σ := retainedGroup μ state (fun p => group p.1) lists (ENNReal.ofReal (1 / 1000 : ℝ)) c
      0 < (σ univ).toReal →
      h / (4 * H) * (ν (group ⁻¹' {c})).toReal ≤ (σ univ).toReal →
      β / (28800 * C * H ^ 4 * ξ ^ 2) ≤ (cells c).card)
    (hbudget : (∑ c ∈ F, ((cells c).card : ℝ)) ≤ 117 * H / ξ ^ 2 * R) :
    ∃ c ∈ F,
      let σ := retainedGroup μ state (fun p => group p.1) lists (ENNReal.ofReal (1 / 1000 : ℝ)) c
      0 < (σ univ).toReal ∧
      h / (4 * H) * (ν (group ⁻¹' {c})).toReal ≤ (σ univ).toReal ∧
      ENNReal.ofReal (h * (ν univ).toReal * β / (13478400 * C * H ^ 6 * R)) ≤ σ univ ∧
      σ ≤ μ := by
  let δ := ENNReal.ofReal (1 / 1000 : ℝ)
  let g : α × ℝ → ℤ := fun p => group p.1
  have hgm : Measurable g := hg.comp measurable_fst
  let μ₁ := μ.restrict (groupStateKeep μ state g lists δ)
  letI (c : ℤ) : IsFiniteMeasure (retainedGroup μ state g lists δ c) := by
    unfold retainedGroup
    infer_instance
  let m : ℤ → ℝ := fun c => (retainedGroup μ state g lists δ c univ).toReal
  let p : ℤ → ℝ := fun c => (ν (group ⁻¹' {c})).toReal
  have hpriorsum : ∑ c ∈ F, p c ≤ (ν univ).toReal := by
    have ht := sum_measure_preimage_singleton (μ := ν) F
      (fun c _ => hg (measurableSet_singleton c))
    have hb : (∑ c ∈ F, ν (group ⁻¹' {c})) ≤ ν univ :=
      ht.le.trans (measure_mono (subset_univ _))
    have hr := ENNReal.toReal_mono (measure_ne_top ν univ) hb
    rw [ENNReal.toReal_sum (fun c hc => measure_ne_top _ _)] at hr
    exact hr
  have hpartition : ∑ c ∈ F, m c = (μ₁ univ).toReal := by
    have ht := retained_group_mass_partition μ state g hgm lists δ F hglobal
    have hr := congrArg ENNReal.toReal ht
    rw [ENNReal.toReal_sum (fun c hc => measure_ne_top _ _)] at hr
    exact hr
  have hretained : (μ univ).toReal / 2 ≤ (μ₁ univ).toReal := by
    have hb := group_state_pruning_mass_budget μ state hs g hgm lists δ 7 hlist
    have hδ : δ * 7 ≤ 1 / 2 := by
      dsimp [δ]
      rw [show (7 : ENNReal) = ENNReal.ofReal (7 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 1000),
        show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]
          norm_num]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    have hsmall := half_mass_of_small_relative_loss (μ univ) (μ₁ univ) (δ * 7)
      (measure_ne_top _ _) hδ (by simpa only [mul_assoc] using hb)
    have hr := ENNReal.toReal_mono (measure_ne_top _ _) hsmall
    simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using hr
  have hmass' : h * (ν univ).toReal / (2 * H) ≤ ∑ c ∈ F, m c := by
    rw [hpartition]
    have ht := div_le_div_of_nonneg_right hmass (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ = (h * (ν univ).toReal / H) / 2 := by ring
      _ ≤ (μ univ).toReal / 2 := ht
      _ ≤ _ := hretained
  obtain ⟨c, hc, hmc, heff, hheavy⟩ := heavy_intercept_group_selection F m p cells
    hH hC hξ hh hν hR hβ (fun c hc => ENNReal.toReal_nonneg)
    (fun c hc => ENNReal.toReal_nonneg) hpriorsum hmass' hfloor hbudget
  refine ⟨c, hc, hmc, heff, ?_, ?_⟩
  · exact (ENNReal.ofReal_le_ofReal hheavy).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _))
  · exact Measure.restrict_le_self.trans Measure.restrict_le_self

end
end Submission.Obl.k4_scalar_capped_heavy_potential
