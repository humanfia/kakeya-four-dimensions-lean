/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PriorIntersectionCut.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ParameterRefinement
import Submission.Obl.k4_scalar_graph_residual_discovery.Model

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice

noncomputable section

/-- The full original priors of all selected fine boxes retain a floor
inside their actual coarse coefficient world. This cut is made globally
and charges the original prior once per selected scale. -/
theorem exists_simultaneous_prior_intersection_cut {σ : Type*} [Fintype σ]
    (θ : Measure ScalarLine) [SFinite θ] (μ : Measure ScalarIncidence)
    {c : ℝ≥0∞} (hdom : μ ≤ c • θ.prod volume)
    {ρ : ℝ} (β : σ → ℝ) (hβ : ∀ s, 0 < β s) (hβρ : ∀ s, β s ≤ ρ)
    (η : σ → ℝ≥0∞) {E : Set ScalarIncidence} (hE : MeasurableSet E)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1) :
    ∃ R : Set ScalarIncidence, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ c * (32 * ∑ s, η s) * θ univ ∧
      ∀ p ∈ R, ∀ s,
        η s * θ {l | cell (β s) l.2 = cell (β s) p.1.2} ≤
          θ {l | cell ρ l.2 = cell ρ p.1.2 ∧ cell (β s) l.2 = cell (β s) p.1.2} := by
  classical
  let bad (s : σ) : Set ScalarLine := {l |
    θ {l' | cell ρ l'.2 = cell ρ l.2 ∧ cell (β s) l'.2 = cell (β s) l.2} <
      η s * θ {l' | cell (β s) l'.2 = cell (β s) l.2}}
  have hbad (s : σ) : MeasurableSet (bad s) := by
    have hpair : Measurable (fun l : ScalarLine => (cell ρ l.2, cell (β s) l.2)) :=
      (measurable_cell ρ measurable_snd).prodMk (measurable_cell (β s) measurable_snd)
    have hpart := (measurable_of_countable (fun q : (Fin 5 → ℤ) × (Fin 5 → ℤ) =>
      θ {l : ScalarLine | cell ρ l.2 = q.1 ∧ cell (β s) l.2 = q.2})).comp hpair
    have hfull : Measurable (fun l : ScalarLine =>
        θ {l' : ScalarLine | cell (β s) l'.2 = cell (β s) l.2}) :=
      (measurable_of_countable (fun q : Fin 5 → ℤ => θ {l : ScalarLine | cell (β s) l.2 = q})).comp
        (measurable_cell (β s) measurable_snd)
    exact measurableSet_lt hpart (measurable_const.mul hfull)
  have hprior (s : σ) : θ (bad s) ≤ η s * 32 * θ univ :=
    coefficient_intersection_light_mass_le θ (fun l : ScalarLine => l.2) measurable_snd
      (hβ s) (hβρ s) (η s)
  let badInc (s : σ) : Set ScalarIncidence := E ∩ (bad s ×ˢ univ)
  have hbadInc (s : σ) : MeasurableSet (badInc s) := hE.inter ((hbad s).prod MeasurableSet.univ)
  have hcost (s : σ) : μ (badInc s) ≤ c * (η s * 32 * θ univ) := by
    calc
      _ ≤ μ (bad s ×ˢ Icc (0 : ℝ) 1) := measure_mono
        (fun p hp => ⟨hp.2.1, htime p hp.1⟩)
      _ ≤ (c • θ.prod volume) (bad s ×ˢ Icc (0 : ℝ) 1) := hdom _
      _ = c * θ (bad s) := by
        rw [Measure.smul_apply, Measure.prod_prod, Real.volume_Icc]
        norm_num [smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hprior s) zero_le
  let R := E \ ⋃ s, badInc s
  refine ⟨R, hE.diff (MeasurableSet.iUnion hbadInc), sdiff_subset, ?_, ?_⟩
  · calc
      μ (E \ R) ≤ μ (⋃ s, badInc s) := by
        apply measure_mono
        intro p hp
        exact not_not.mp (fun h => hp.2 ⟨hp.1, h⟩)
      _ ≤ ∑' s, μ (badInc s) := measure_iUnion_le _
      _ = ∑ s, μ (badInc s) := tsum_fintype _
      _ ≤ ∑ s, c * (η s * 32 * θ univ) := Finset.sum_le_sum (fun s _ => hcost s)
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s _
        ring
  · intro p hp s
    apply le_of_not_gt
    intro hlight
    have hb : p ∈ badInc s := ⟨hp.1, hlight, mem_univ _⟩
    exact hp.2 (mem_iUnion.mpr ⟨s, hb⟩)

end

end Submission.Obl.k4_scalar_graph_residual_discovery
