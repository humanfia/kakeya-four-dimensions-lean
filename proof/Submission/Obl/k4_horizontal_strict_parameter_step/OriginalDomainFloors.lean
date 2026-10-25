/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at c4765076c45bb6cb7fbc53c5859035579f22a4b1, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalDomainFloors.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.CountingLosses

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- The cutoff for a current incidence is evaluated on the entire earlier
original domain, with its unchanged reference weight. -/
def originalDomainKeep {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ι → Set Ω) (label : Ω → ι) (w : ι → ℝ) (δ : ℝ) : Set Ω :=
  {p | ENNReal.ofReal (δ * w (label p)) ≤ μ (E (label p))}

theorem measurableSet_originalDomainKeep {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) (E : ι → Set Ω) (label : Ω → ι) (hl : Measurable label)
    (w : ι → ℝ) (δ : ℝ) : MeasurableSet (originalDomainKeep μ E label w δ) := by
  exact hl ((Set.to_countable {i | ENNReal.ofReal (δ * w i) ≤ μ (E i)}).measurableSet)

/-- Deleting current points of light original domains is charged to the
summed original reference budget, even when those domains overlap. -/
theorem original_domain_floor_loss {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ lam : Measure Ω) (hdom : lam ≤ μ) (E : ι → Set Ω) (label : Ω → ι)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcover : ∀ᵐ p ∂lam, p ∈ E (label p)) :
    lam (originalDomainKeep μ E label w δ)ᶜ ≤ ENNReal.ofReal (δ * ∑ i, w i) := by
  classical
  have hlight :=
    Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.light_entry_loss
      μ Finset.univ (fun _ : ι => ({()} : Finset Unit)) ({()} : Finset Unit)
      (fun i _ _ => E i) (fun i => δ * w i) (fun i => mul_nonneg hδ (hw i))
  have hb : μ {p | ∃ i, μ (E i) < ENNReal.ofReal (δ * w i) ∧ p ∈ E i} ≤
      ENNReal.ofReal (δ * ∑ i, w i) := by
    have hset : {p | ∃ i, μ (E i) < ENNReal.ofReal (δ * w i) ∧ p ∈ E i} =
        (⋃ i ∈ (Finset.univ : Finset ι), ⋃ _q ∈ ({()} : Finset Unit),
          ⋃ _θ ∈ ({()} : Finset Unit).filter
            (fun _ => μ (E i) < ENNReal.ofReal (δ * w i)), E i) := by
      ext p
      simp only [mem_setOf_eq, mem_iUnion, Finset.mem_univ, Finset.mem_singleton,
        Finset.mem_filter]
      aesop
    rw [hset]
    simpa [Finset.mul_sum] using hlight
  apply (le_trans (measure_mono_ae ?_) ((hdom _).trans hb))
  filter_upwards [hcover] with p hp hbad
  exact ⟨label p, lt_of_not_ge hbad, hp⟩

end

end Submission.Obl.k4_horizontal_strict_parameter_step
