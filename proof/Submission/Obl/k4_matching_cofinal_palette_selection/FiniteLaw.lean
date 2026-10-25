/- Adapted from this LOT tree, o040, session x0115, commit 9f7e9a910e7de423611a55b624313eab3641558f,
   Submission/Obl/k4_matching_refinement_exponent/FiniteLaw.lean. -/
import Submission.Obl.k4_matching_palette_likelihood.Basic

open MeasureTheory Set

namespace Submission.Obl.k4_matching_cofinal_palette_selection

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- The probability vector obtained by pushing an event law to a finite code. -/
noncomputable def atomMass (μ : Measure Ω) (X : Ω → Fin n) (i : Fin n) : ℝ :=
  μ.real (X ⁻¹' {i})

theorem atomMass_nonneg (μ : Measure Ω) (X : Ω → Fin n) (i : Fin n) :
    0 ≤ atomMass μ X i := ENNReal.toReal_nonneg

/-- Finite sums of code masses agree with the mass of the associated event. -/
theorem sum_atomMass (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → Fin n) (hX : Measurable X) (s : Finset (Fin n)) :
    (∑ i ∈ s, atomMass μ X i) = μ.real (X ⁻¹' (s : Set (Fin n))) := by
  exact sum_measureReal_preimage_singleton s
    (fun i _ => hX (measurableSet_singleton i))

theorem sum_atomMass_eq_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n) (hX : Measurable X) :
    (∑ i, atomMass μ X i) = 1 := by
  simpa using sum_atomMass μ X hX Finset.univ

/-- Integrals of functions of a finite code are finite probability sums. -/
theorem integral_atomMass (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → Fin n) (hX : Measurable X) (g : Fin n → ℝ) :
    (∫ ω, g (X ω) ∂μ) = ∑ i, atomMass μ X i * g i := by
  have hg : Integrable g (μ.map X) := Integrable.of_finite
  rw [← integral_map hX.aemeasurable hg.aestronglyMeasurable, integral_fintype hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_eq_mul, atomMass, measureReal_def,
    Measure.map_apply hX (measurableSet_singleton i)]

/-- Conditional palette likelihood, with arbitrary values on zero-mass records. -/
noncomputable def likelihood (p : Fin n → ℝ) (F : ℕ → Fin n → ℕ)
    (Z : Fin n → ℕ) (k : ℕ) (x : Fin n) : ℝ :=
  Submission.Obl.k4_matching_palette_likelihood.posterior p (F k) Z x

/-- The same likelihood expressed directly using the original event measure. -/
noncomputable def eventLikelihood (μ : Measure Ω) (X : Ω → Fin n)
    (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ) (k : ℕ) (ω : Ω) : ℝ :=
  μ.real {ω' | F k (X ω') = F k (X ω) ∧ Z (X ω') = Z (X ω)} /
    μ.real {ω' | F k (X ω') = F k (X ω)}

/-- Passing to the finite joint code preserves every conditional likelihood. -/
theorem eventLikelihood_eq (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → Fin n) (hX : Measurable X)
    (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ) (k : ℕ) (ω : Ω) :
    eventLikelihood μ X F Z k ω = likelihood (atomMass μ X) F Z k (X ω) := by
  unfold eventLikelihood likelihood
    Submission.Obl.k4_matching_palette_likelihood.posterior
    Submission.Obl.k4_matching_palette_likelihood.colorMass
    Submission.Obl.k4_matching_palette_likelihood.fiberMass
  rw [sum_atomMass μ X hX, sum_atomMass μ X hX]
  congr 2 <;> ext ω' <;> simp

end Submission.Obl.k4_matching_cofinal_palette_selection
