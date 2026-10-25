import Submission.Obl.k4_scalar_guarded_tangent_preparation.WeightedTruncation
import Submission.Obl.k4_scalar_guarded_tangent_preparation.OriginalCode

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open Submission.Obl.k4_matching_cofinal_palette_selection
open scoped ENNReal

noncomputable section

/-- The exact finite original-law preparation: signed velocity labels,
original world weights, and at least half their original weighted mass. -/
theorem exists_weighted_signed_original_truncation
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (σ : ι → Measure Ω) [∀ i, IsFiniteMeasure (σ i)]
    (ω : ι → ℝ) (hω : ∀ i, 0 ≤ ω i) (n : ι → ℕ)
    (X : ∀ i, Ω → Fin (n i)) (hX : ∀ i, Measurable (X i))
    (Y : ∀ i, Fin (n i) → ℕ) (Z : ∀ i, Fin (n i) → ℤ) {R : ℝ} (hR : 1 < R)
    (hbudget : (∑ g, ω g * ∑ i : Fin (n g),
        (σ g {x | X g x = i}).toReal * max 0 (Real.log
          (((σ g {x | Y g (X g x) = Y g i ∧ Z g (X g x) = Z g i}).toReal *
              (σ g univ).toReal) /
            ((σ g {x | Y g (X g x) = Y g i}).toReal *
              (σ g {x | Z g (X g x) = Z g i}).toReal)))) ≤
      ((∑ g, ENNReal.ofReal (ω g) * σ g univ).toReal / 2) * Real.log R) :
    ∃ ρ : ι → Measure Ω, (∀ g, ρ g ≤ σ g) ∧
      ENNReal.ofReal (1 / 2 : ℝ) * (∑ g, ENNReal.ofReal (ω g) * σ g univ) ≤
        ∑ g, ENNReal.ofReal (ω g) * ρ g univ ∧
      ∀ g (τ : Measure Ω), τ ≤ ρ g → ∀ (e : ℕ) (z : ℤ),
        τ.real {x | Y g (X g x) = e ∧ Z g (X g x) = z} * (σ g).real univ ≤
          R * (σ g).real {x | Y g (X g x) = e} *
            (σ g).real {x | Z g (X g x) = z} := by
  classical
  have htotal : (∑ g, ENNReal.ofReal (ω g) * σ g univ).toReal =
      ∑ g, ω g * (σ g).real univ := by
    rw [ENNReal.toReal_sum (fun g _ => by finiteness)]
    apply Finset.sum_congr rfl
    intro g _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hω g)]
    rfl
  have hb : (∑ g, ω g * ∑ i, atomMass (σ g) (X g) i * max 0 (Real.log
      (originalLikelihood (atomMass (σ g) (X g)) (Y g) (fun i => Encodable.encode (Z g i)) i))) ≤
      ((∑ g, ω g * (σ g).real univ) / 2) * Real.log R := by
    simp_rw [originalLikelihood_eq_signed_event (σ _) (X _) (hX _)]
    rw [htotal] at hbudget
    exact hbudget
  obtain ⟨G, ρ, hG, heq, hρ, hmass, hcap⟩ := exists_weighted_original_truncation
    σ ω hω n X hX Y (fun g i => Encodable.encode (Z g i)) hR hb
  refine ⟨ρ, hρ, ?_, ?_⟩
  · letI (g : ι) : IsFiniteMeasure (ρ g) := isFiniteMeasure_of_le (σ g) (hρ g)
    have hcurrent : (∑ g, ENNReal.ofReal (ω g) * ρ g univ).toReal =
        ∑ g, ω g * (ρ g).real univ := by
      rw [ENNReal.toReal_sum (fun g _ => by finiteness)]
      apply Finset.sum_congr rfl
      intro g _
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hω g)]
      rfl
    have hσfinite : (∑ g, ENNReal.ofReal (ω g) * σ g univ) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun g _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    have hρfinite : (∑ g, ENNReal.ofReal (ω g) * ρ g univ) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun g _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hσfinite) hρfinite).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), htotal, hcurrent]
    convert hmass using 1 <;> ring
  · intro g τ hτ e z
    simpa only [Encodable.encode_injective.eq_iff] using hcap g τ hτ e (Encodable.encode z)

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
