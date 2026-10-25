import Submission.Obl.k4_scalar_guarded_tangent_preparation.UnnormalizedMeasured

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open Submission.Obl.k4_matching_cofinal_palette_selection
open PaletteTruncation

/-- The finite likelihood is exactly the original measured-event ratio,
including its original total mass and all zero atoms. -/
theorem originalLikelihood_eq_event
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : Measure Ω) [IsFiniteMeasure σ] (X : Ω → Fin n) (hX : Measurable X)
    (Y Z : Fin n → ℕ) (i : Fin n) :
    originalLikelihood (atomMass σ X) Y Z i =
      (σ.real {x | Y (X x) = Y i ∧ Z (X x) = Z i} * σ.real univ) /
        (σ.real {x | Y (X x) = Y i} * σ.real {x | Z (X x) = Z i}) := by
  classical
  unfold originalLikelihood
  rw [code_joint_mass σ X hX Y Z, code_fiber_mass σ X hX Y, code_fiber_mass σ X hX Z]
  have htotal : (∑ i, atomMass σ X i) = σ.real univ := by
    simpa using sum_atomMass σ X hX Finset.univ
  rw [htotal]

/-- Integer floor-bin labels can be encoded without changing any
original likelihood or palette fiber. -/
theorem originalLikelihood_eq_signed_event
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : Measure Ω) [IsFiniteMeasure σ] (X : Ω → Fin n) (hX : Measurable X)
    (Y : Fin n → ℕ) (Z : Fin n → ℤ) (i : Fin n) :
    originalLikelihood (atomMass σ X) Y (fun j => Encodable.encode (Z j)) i =
      (σ.real {x | Y (X x) = Y i ∧ Z (X x) = Z i} * σ.real univ) /
        (σ.real {x | Y (X x) = Y i} * σ.real {x | Z (X x) = Z i}) := by
  rw [originalLikelihood_eq_event σ X hX]
  simp only [Encodable.encode_injective.eq_iff]

/-- Signed velocity labels retain the exact original fiber caps. -/
theorem exists_signed_measurable_truncation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : Measure Ω) [IsFiniteMeasure σ] (X : Ω → Fin n) (hX : Measurable X)
    (Y : Fin n → ℕ) (Z : Fin n → ℤ) {R : ℝ} (hR : 1 < R) :
    ∃ G : Set Ω, MeasurableSet G ∧
      σ.real Gᶜ ≤ (∑ i, atomMass σ X i * max 0 (Real.log
        ((σ.real {x | Y (X x) = Y i ∧ Z (X x) = Z i} * σ.real univ) /
          (σ.real {x | Y (X x) = Y i} * σ.real {x | Z (X x) = Z i})))) / Real.log R ∧
      ∀ (ρ : Measure Ω), ρ ≤ σ.restrict G → ∀ (e : ℕ) (z : ℤ),
        ρ.real {x | Y (X x) = e ∧ Z (X x) = z} * σ.real univ ≤
          R * σ.real {x | Y (X x) = e} * σ.real {x | Z (X x) = z} := by
  obtain ⟨G, hG, hloss, hcap⟩ := exists_unnormalized_measurable_truncation
    σ X hX Y (fun j => Encodable.encode (Z j)) hR
  refine ⟨G, hG, ?_, ?_⟩
  · simpa only [originalLikelihood_eq_signed_event σ X hX Y Z] using hloss
  · intro ρ hρ e z
    simpa only [Encodable.encode_injective.eq_iff] using hcap ρ hρ e (Encodable.encode z)

end Submission.Obl.k4_scalar_guarded_tangent_preparation
