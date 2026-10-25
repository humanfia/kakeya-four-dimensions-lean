import Submission.Obl.k4_fixed_menu_density_pruning.Interface
import Submission.Lib.K4ListedExceptions.ObservationCaps
import Submission.Lib.K4ExactProblemOps.Coarsening

namespace Submission.Obl.k4_fixed_menu_density_pruning

open MeasureTheory Set Finset
open scoped ENNReal

/-- Intersect finitely many density caps on the unchanged source laws. -/
theorem finite_density_cut {X Y I Γ : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype I] [Fintype Γ]
    (μ : Γ → Measure X) (w : Γ → ENNReal) (ref : Measure Y)
    (o : I → Γ → X → Y) (g : I → Γ → Y → ENNReal) (H : I → ENNReal)
    (ho : ∀ i a, Measurable (o i a)) (hg : ∀ i a, Measurable (g i a))
    (hlaw : ∀ i a, (μ a).map (o i a) = ref.withDensity (g i a)) :
    ∃ Good : Γ → Set X,
      (∀ a, MeasurableSet (Good a)) ∧
      (∑ a, w a * μ a (Good a)ᶜ) ≤
        ∑ i, ∑ a, w a * μ a {p | H i < g i a (o i a p)} ∧
      ∀ i a, ((μ a).restrict (Good a)).map (o i a) ≤ H i • ref := by
  classical
  let Good : Γ → Set X := fun a => ⋂ i, {p | g i a (o i a p) ≤ H i}
  have hGood (a : Γ) : MeasurableSet (Good a) :=
    MeasurableSet.iInter (fun i => measurableSet_le ((hg i a).comp (ho i a)) measurable_const)
  refine ⟨Good, hGood, ?_, ?_⟩
  · have hc (a : Γ) : (Good a)ᶜ = ⋃ i, {p | H i < g i a (o i a p)} := by
      ext p
      simp only [Good, mem_compl_iff, mem_iInter, mem_setOf_eq, not_forall,
        not_le, mem_iUnion]
    calc
      _ ≤ ∑ a, w a * ∑ i, μ a {p | H i < g i a (o i a p)} := by
        gcongr with a
        rw [hc]
        exact measure_iUnion_fintype_le _ _
      _ = _ := by simp_rw [mul_sum]; exact sum_comm
  · intro i a
    apply le_trans ?_
      (Submission.Lib.K4ListedExceptions.map_restrict_observation_cap_le
        (μ a) ref (o i a) (ho i a) (g i a) (hg i a) (hlaw i a) (H i))
    exact Measure.map_mono (Measure.restrict_mono
      (show Good a ⊆ {p | g i a (o i a p) ≤ H i} from
        fun p hp => mem_iInter.mp hp i) le_rfl) (ho i a)

lemma measurable_obs (B a : ℝ) : Measurable (obs B a) := by
  exact Submission.Lib.K4ExactProblemOps.measurable_obs B a

lemma menuDepth_bounds {L s h δ₀ : ℝ} (hL : 0 ≤ L) :
    0 ≤ menuDepth L s h δ₀ ∧ menuDepth L s h δ₀ ≤ L :=
  ⟨le_min hL (le_max_left _ _), min_le_left _ _⟩

end Submission.Obl.k4_fixed_menu_density_pruning
