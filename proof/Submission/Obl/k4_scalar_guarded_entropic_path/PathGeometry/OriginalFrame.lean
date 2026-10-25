/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/OriginalFrame.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RefinementWitness

/-!
Composed original-law frames for a finite path of literal refinements.
Full trajectory assignments and selected incidence masks are distinct
fields, and only the former enter the prior normalizers.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_dyadic_crop_affine_laws.Framework

/-- A path's actual original sample, world and full assigned prior,
together with its separately retained selected incidence law. -/
structure OriginalFrame (p q : Code) where
  sample : ℕ → ℕ
  world : (k : ℕ) → Fin (W q k) → Fin (W p (sample k))
  duration : ℕ → ℝ
  assignment : (k : ℕ) → Fin (W q k) → Set (ℕ × ScalarCoeff)
  selected : (k : ℕ) → Fin (W q k) → Set ((ℕ × ScalarCoeff) × ℝ)
  coefficient : (k : ℕ) → Fin (W q k) → (ℕ × ScalarCoeff) ≃ᵐ (ℕ × ScalarCoeff)
  incidence : (k : ℕ) → Fin (W q k) →
    ((ℕ × ScalarCoeff) × ℝ) ≃ᵐ ((ℕ × ScalarCoeff) × ℝ)
  normalizer : ℕ → ℝ
  sample_strictMono : StrictMono sample
  resolution : ∀ k, N q k = N p (sample k)
  duration_pos : ∀ k, 0 < duration k
  normalizer_pos : ∀ k, 0 < normalizer k
  assignment_measurable : ∀ k i, MeasurableSet (assignment k i)
  selected_measurable : ∀ k i, MeasurableSet (selected k i)
  assignment_mass_pos : ∀ k i, 0 < ν p (sample k) (world k i) (assignment k i)
  assignment_mass_ne_top : ∀ k i, ν p (sample k) (world k i) (assignment k i) ≠ ∞
  prior : ∀ k i, ν q k i = conditionedPrior
    (ν p (sample k) (world k i)) (assignment k i) (coefficient k i)
  incidence_law : ∀ k i, mu q k i =
    (ENNReal.ofReal (duration k) * ν p (sample k) (world k i) (assignment k i))⁻¹ •
      Measure.map (incidence k i) ((mu p (sample k) (world k i)).restrict (selected k i))
  weight : ∀ k i, ω q k i =
    ω p (sample k) (world k i) * duration k *
      (ν p (sample k) (world k i) (assignment k i)).toReal / normalizer k

namespace OriginalFrame

noncomputable section

variable {p q z : Code}

/-- Every literal refinement supplies an original-law frame. -/
def ofRefinement {r b h : ℝ} (w : RefinementWitness p q r b h) (hp : Exact p) :
    OriginalFrame p q where
  sample := w.sample
  world := w.world
  duration := w.toRefinementData.duration
  assignment := w.assignment
  selected := w.selected
  coefficient := w.coefficientEquiv hp
  incidence := w.incidenceEquiv hp
  normalizer k := ∑ i : Fin (W q k), ω p (w.sample k) (w.world k i) *
    w.toRefinementData.duration k * (ν p (w.sample k) (w.world k i) (w.assignment k i)).toReal
  sample_strictMono := w.sample_strictMono
  resolution k := (w.charts k).1
  duration_pos := w.duration_pos
  normalizer_pos k := (w.weights k).1
  assignment_measurable k i := (((w.charts k).2.2.2.1) i).1
  selected_measurable k i := (((w.charts k).2.2.2.1) i).2
  assignment_mass_pos := w.assignment_mass_pos
  assignment_mass_ne_top := w.assignment_mass_ne_top hp
  prior := w.prior_eq hp
  incidence_law := w.incidence_eq hp
  weight k i := (w.weights k).2 i

/-- The identity frame keeps the whole original prior and incidence law. -/
def refl (p : Code) (hp : Exact p) : OriginalFrame p p where
  sample := id
  world _ := id
  duration _ := 1
  assignment _ _ := univ
  selected _ _ := univ
  coefficient _ _ := MeasurableEquiv.refl _
  incidence _ _ := MeasurableEquiv.refl _
  normalizer _ := 1
  sample_strictMono := strictMono_id
  resolution _ := rfl
  duration_pos _ := zero_lt_one
  normalizer_pos _ := zero_lt_one
  assignment_measurable _ _ := MeasurableSet.univ
  selected_measurable _ _ := MeasurableSet.univ
  assignment_mass_pos k i := by
    have : IsProbabilityMeasure (ν p k i) := ((hp.2.1 k).2.2.2.1 i).1
    simp
  assignment_mass_ne_top k i := by
    change ν p k i univ ≠ ∞
    have : IsProbabilityMeasure (ν p k i) := ((hp.2.1 k).2.2.2.1 i).1
    exact measure_ne_top _ _
  prior k i := by
    have : IsProbabilityMeasure (ν p k i) := ((hp.2.1 k).2.2.2.1 i).1
    simp [conditionedPrior]
    change ν p k i = Measure.map id (ν p k i)
    rw [Measure.map_id]
  incidence_law k i := by
    have : IsProbabilityMeasure (ν p k i) := ((hp.2.1 k).2.2.2.1 i).1
    simp
    change mu p k i = Measure.map id (mu p k i)
    rw [Measure.map_id]
  weight k i := by
    have : IsProbabilityMeasure (ν p k i) := ((hp.2.1 k).2.2.2.1 i).1
    simp

/-- The original mass of a nested full assignment is the product of the
parent full mass and its conditional child mass. -/
theorem nested_mass (parent : OriginalFrame p q) (child : OriginalFrame q z)
    (k : ℕ) (i : Fin (W z k)) :
    ν p (parent.sample (child.sample k)) (parent.world (child.sample k) (child.world k i))
      (parent.assignment (child.sample k) (child.world k i) ∩
        (parent.coefficient (child.sample k) (child.world k i)) ⁻¹' child.assignment k i) =
      ν p (parent.sample (child.sample k)) (parent.world (child.sample k) (child.world k i))
        (parent.assignment (child.sample k) (child.world k i)) *
          ν q (child.sample k) (child.world k i) (child.assignment k i) := by
  rw [parent.prior]
  exact (RefinementLaws.assignment_mass_mul _ _ _ (child.assignment_measurable k i)
    (parent.assignment_mass_pos _ _).ne' (parent.assignment_mass_ne_top _ _)).symm

/-- Frames compose on the original laws. Actual durations multiply; the
prior uses full assignment intersections and incidence restrictions use
their separate selected-mask intersections. -/
def comp (parent : OriginalFrame p q) (child : OriginalFrame q z) : OriginalFrame p z where
  sample := parent.sample ∘ child.sample
  world k i := parent.world (child.sample k) (child.world k i)
  duration k := parent.duration (child.sample k) * child.duration k
  assignment k i := parent.assignment (child.sample k) (child.world k i) ∩
    (parent.coefficient (child.sample k) (child.world k i)) ⁻¹' child.assignment k i
  selected k i := parent.selected (child.sample k) (child.world k i) ∩
    (parent.incidence (child.sample k) (child.world k i)) ⁻¹' child.selected k i
  coefficient k i := (parent.coefficient (child.sample k) (child.world k i)).trans
    (child.coefficient k i)
  incidence k i := (parent.incidence (child.sample k) (child.world k i)).trans
    (child.incidence k i)
  normalizer k := parent.normalizer (child.sample k) * child.normalizer k
  sample_strictMono := parent.sample_strictMono.comp child.sample_strictMono
  resolution k := (child.resolution k).trans (parent.resolution (child.sample k))
  duration_pos k := mul_pos (parent.duration_pos _) (child.duration_pos _)
  normalizer_pos k := mul_pos (parent.normalizer_pos _) (child.normalizer_pos _)
  assignment_measurable k i := (parent.assignment_measurable _ _).inter
    ((child.assignment_measurable k i).preimage (parent.coefficient _ _).measurable)
  selected_measurable k i := (parent.selected_measurable _ _).inter
    ((child.selected_measurable k i).preimage (parent.incidence _ _).measurable)
  assignment_mass_pos k i := by
    simp only [Function.comp_apply]
    rw [parent.nested_mass child]
    exact ENNReal.mul_pos_iff.2
      ⟨parent.assignment_mass_pos _ _, child.assignment_mass_pos _ _⟩
  assignment_mass_ne_top k i := by
    simp only [Function.comp_apply]
    rw [parent.nested_mass child]
    exact ENNReal.mul_ne_top (parent.assignment_mass_ne_top _ _)
      (child.assignment_mass_ne_top _ _)
  prior k i := by
    rw [child.prior, parent.prior]
    exact RefinementLaws.conditionedPrior_comp _ _ _ _ (child.assignment_measurable k i)
      (parent.assignment_mass_pos _ _).ne' (parent.assignment_mass_ne_top _ _)
  incidence_law k i := by
    rw [child.incidence_law, parent.incidence_law, parent.prior,
      ENNReal.ofReal_mul (parent.duration_pos _).le]
    exact RefinementLaws.normalized_incidence_comp _ _ _ _ (child.selected_measurable k i)
      _ _ _ (child.assignment_measurable k i) _ _
      (parent.assignment_mass_pos _ _).ne' (parent.assignment_mass_ne_top _ _)
      (ENNReal.ofReal_pos.mpr (parent.duration_pos _)).ne' ENNReal.ofReal_ne_top
  weight k i := by
    simp only [Function.comp_apply]
    rw [child.weight, parent.weight]
    apply RefinementLaws.mixture_weight_comp
    rw [← ENNReal.toReal_mul, ← parent.nested_mass child]

/-- The common normalizer is exactly the sum of original-world budgets
once the final world's weights are known to sum to one. -/
theorem normalizer_eq_original_budget (frame : OriginalFrame p q) (hq : Exact q) (k : ℕ) :
    frame.normalizer k = ∑ i : Fin (W q k),
      ω p (frame.sample k) (frame.world k i) * frame.duration k *
        (ν p (frame.sample k) (frame.world k i) (frame.assignment k i)).toReal := by
  have hsum : (∑ i : Fin (W q k), ω q k i) = 1 := (hq.2.1 k).2.2.1
  have ht := congrArg (fun t : ℝ => t * frame.normalizer k) hsum
  rw [Finset.sum_mul, one_mul] at ht
  have hterms : (∑ i : Fin (W q k), ω q k i * frame.normalizer k) =
      ∑ i : Fin (W q k), ω p (frame.sample k) (frame.world k i) * frame.duration k *
        (ν p (frame.sample k) (frame.world k i) (frame.assignment k i)).toReal := by
    apply Finset.sum_congr rfl
    intro i _
    rw [frame.weight, div_mul_cancel₀ _ (frame.normalizer_pos k).ne']
  exact ht.symm.trans hterms

end

end OriginalFrame

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
