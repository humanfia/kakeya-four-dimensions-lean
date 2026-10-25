import Submission.Obl.k4_scalar_guarded_tangent_preparation.UnnormalizedTruncation
import Submission.Obl.k4_scalar_guarded_tangent_preparation.MeasuredPalette

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open Submission.Obl.k4_matching_palette_likelihood
open Submission.Obl.k4_matching_cofinal_palette_selection
open PaletteTruncation

noncomputable section

/-- One original unnormalized finite reference law yields a measurable
likelihood mask, with its lost original mass charged directly to the
positive-score budget. All denominators and palette masses precede G. -/
theorem exists_unnormalized_measurable_truncation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : Measure Ω) [IsFiniteMeasure σ] (X : Ω → Fin n) (hX : Measurable X)
    (Y Z : Fin n → ℕ) {R : ℝ} (hR : 1 < R) :
    ∃ G : Set Ω, MeasurableSet G ∧
      σ.real Gᶜ ≤ (∑ i, atomMass σ X i * max 0
        (Real.log (originalLikelihood (atomMass σ X) Y Z i))) / Real.log R ∧
      ∀ (ρ : Measure Ω), ρ ≤ σ.restrict G → ∀ e z : ℕ,
        ρ.real {ω | Y (X ω) = e ∧ Z (X ω) = z} * σ.real univ ≤
          R * σ.real {ω | Y (X ω) = e} * σ.real {ω | Z (X ω) = z} := by
  classical
  let p := atomMass σ X
  let s : Finset (Fin n) := Finset.univ.filter (fun i =>
    colorMass p Y Z (Y i) (Z i) * (∑ j, p j) ≤
      R * fiberMass p Y (Y i) * fiberMass p Z (Z i))
  let G : Set Ω := X ⁻¹' (s : Set (Fin n))
  have hp : ∀ i, 0 ≤ p i := atomMass_nonneg σ X
  have htotal : ∑ i, p i = σ.real univ := by
    simpa [p] using sum_atomMass σ X hX Finset.univ
  have hG : MeasurableSet G := hX s.finite_toSet.measurableSet
  have hatom : atomMass (σ.restrict G) X = originalRetained p Y Z R := by
    funext i
    rw [atomMass_restrict_codes σ X hX s i]
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, originalRetained]
    rfl
  refine ⟨G, hG, ?_, ?_⟩
  · let bad := Finset.univ.filter (fun i => i ∉ s)
    have hbad : X ⁻¹' (bad : Set (Fin n)) = Gᶜ := by
      ext ω
      simp only [bad, G, Set.mem_preimage, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and, Set.mem_compl_iff]
    have hmass : σ.real Gᶜ = ∑ i, (p i - originalRetained p Y Z R i) := by
      calc
        σ.real Gᶜ = ∑ i ∈ bad, p i := by
          simpa only [hbad] using (sum_atomMass σ X hX bad).symm
        _ = _ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i ∈ s
          · have hgood : colorMass p Y Z (Y i) (Z i) * (∑ j, p j) ≤
                R * fiberMass p Y (Y i) * fiberMass p Z (Z i) := by
              simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi
            simp only [hi, not_true_eq_false, ite_false, originalRetained, ite_eq_left hgood, sub_self]
          · have hbad : ¬colorMass p Y Z (Y i) (Z i) * (∑ j, p j) ≤
                R * fiberMass p Y (Y i) * fiberMass p Z (Z i) := by
              simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi
            simp only [hi, not_false_eq_true, ite_true, originalRetained, ite_eq_right hbad, sub_zero]
    rw [hmass]
    exact original_removed_mass_le_score p Y Z hp hR
  · intro ρ hρ e z
    have hmono : ρ.real {ω | Y (X ω) = e ∧ Z (X ω) = z} ≤
        (σ.restrict G).real {ω | Y (X ω) = e ∧ Z (X ω) = z} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (hρ _)
    apply (mul_le_mul_of_nonneg_right hmono ENNReal.toReal_nonneg).trans
    rw [← code_joint_mass (σ.restrict G) X hX Y Z e z, hatom,
      ← code_fiber_mass σ X hX Y e, ← code_fiber_mass σ X hX Z z]
    change colorMass (originalRetained p Y Z R) Y Z e z * σ.real univ ≤
      R * fiberMass p Y e * fiberMass p Z z
    rw [← htotal]
    exact originalRetained_joint_le p Y Z hp (by linarith) e z

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
