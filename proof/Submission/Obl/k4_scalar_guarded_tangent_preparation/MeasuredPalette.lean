/-
Adapted from this LOT tree, o134, session x0438, branch x0438,
file Submission/Obl/k4_scalar_guarded_tangent_obstruction/MeasuredPalette.lean.
The reference-law and palette constructions retain their original denominators.
-/

import Submission.Obl.k4_scalar_guarded_tangent_preparation.PaletteTruncation
import Submission.Obl.k4_matching_cofinal_palette_selection.FiniteLaw

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation.PaletteTruncation

open MeasureTheory Set
open Submission.Obl.k4_matching_palette_likelihood
open Submission.Obl.k4_matching_cofinal_palette_selection

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

theorem code_fiber_mass (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → Fin n) (hX : Measurable X) (E : Fin n → ℕ) (e : ℕ) :
    fiberMass (atomMass μ X) E e = μ.real {ω | E (X ω) = e} := by
  classical
  simpa only [fiberMass, Set.preimage, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_univ, true_and] using
    sum_atomMass μ X hX (Finset.univ.filter (fun i => E i = e))

theorem code_joint_mass (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → Fin n) (hX : Measurable X) (E Z : Fin n → ℕ) (e z : ℕ) :
    colorMass (atomMass μ X) E Z e z = μ.real {ω | E (X ω) = e ∧ Z (X ω) = z} := by
  classical
  simpa only [colorMass, Set.preimage, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_univ, true_and] using
    sum_atomMass μ X hX (Finset.univ.filter (fun i => E i = e ∧ Z i = z))

/-- Restricting to a set of finite codes deletes exactly those atoms,
without any change of normalization. -/
theorem atomMass_restrict_codes (μ : Measure Ω) (X : Ω → Fin n) (hX : Measurable X)
    (s : Finset (Fin n)) (i : Fin n) :
    atomMass (μ.restrict (X ⁻¹' (s : Set (Fin n)))) X i =
      if i ∈ s then atomMass μ X i else 0 := by
  classical
  simp only [atomMass, measureReal_def]
  rw [Measure.restrict_apply (hX (measurableSet_singleton i))]
  by_cases hi : i ∈ s
  · have hsub : X ⁻¹' {i} ⊆ X ⁻¹' (s : Set (Fin n)) := by
      intro ω hω
      have hx : X ω = i := hω
      simpa only [Set.mem_preimage, hx, Finset.mem_coe] using hi
    rw [Set.inter_eq_left.mpr hsub, ite_eq_left hi]
  · have hzero : X ⁻¹' {i} ∩ X ⁻¹' (s : Set (Fin n)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hx : X ω = i := hω.1
      exact hi (hx ▸ hω.2)
    rw [hzero, measure_empty, ENNReal.toReal_zero, ite_eq_right hi]

/-- Measurable reference-law palette truncation on any event space with a
finite joint code. Its palette and parent law remain the original ones. -/
theorem exists_measurable_truncation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n) (hX : Measurable X) (E Z : Fin n → ℕ) {R : ℝ} (hR : 1 < R) :
    ∃ G : Set Ω, MeasurableSet G ∧
      μ.real Gᶜ ≤ (entropy (atomMass μ X) (fun _ => 0) Z -
        entropy (atomMass μ X) E Z + 1) / Real.log R ∧
      ∀ e z : ℕ,
        (μ.restrict G).real {ω | E (X ω) = e ∧ Z (X ω) = z} ≤
          R * μ.real {ω | E (X ω) = e} * μ.real {ω | Z (X ω) = z} := by
  classical
  let p := atomMass μ X
  let s : Finset (Fin n) := Finset.univ.filter (fun i => colorMass p E Z (E i) (Z i) ≤
    R * fiberMass p E (E i) * colorMass p (fun _ => 0) Z 0 (Z i))
  let G : Set Ω := X ⁻¹' (s : Set (Fin n))
  have hp : ∀ i, 0 ≤ p i := atomMass_nonneg μ X
  have hp1 : ∑ i, p i = 1 := sum_atomMass_eq_one μ X hX
  have hG : MeasurableSet G := hX s.finite_toSet.measurableSet
  have hatom : atomMass (μ.restrict G) X = retained p E Z R := by
    funext i
    rw [atomMass_restrict_codes μ X hX s i]
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, retained]
    rfl
  refine ⟨G, hG, ?_, ?_⟩
  · let bad := Finset.univ.filter (fun i => i ∉ s)
    have hbad : X ⁻¹' (bad : Set (Fin n)) = Gᶜ := by
      ext ω
      simp only [bad, G, Set.mem_preimage, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and, Set.mem_compl_iff]
    have hmass : μ.real Gᶜ = ∑ i, (p i - retained p E Z R i) := by
      calc
        μ.real Gᶜ = ∑ i ∈ bad, p i := by
          simpa only [hbad] using (sum_atomMass μ X hX bad).symm
        _ = _ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i ∈ s
          · have hgood : colorMass p E Z (E i) (Z i) ≤
                R * fiberMass p E (E i) * colorMass p (fun _ => 0) Z 0 (Z i) := by
              simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi
            simp only [hi, not_true_eq_false, ite_false, retained, ite_eq_left hgood, sub_self]
          · have hbad : ¬colorMass p E Z (E i) (Z i) ≤
                R * fiberMass p E (E i) * colorMass p (fun _ => 0) Z 0 (Z i) := by
              simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi
            simp only [hi, not_false_eq_true, ite_true, retained, ite_eq_right hbad, sub_zero]
    rw [hmass]
    exact removed_mass_le p E Z hp hp1 hR
  · intro e z
    rw [← code_joint_mass (μ.restrict G) X hX E Z e z, hatom,
      ← code_fiber_mass μ X hX E e, ← code_fiber_mass μ X hX Z z]
    have hcap := retained_joint_le p E Z hp (by linarith : 0 ≤ R) e z
    simpa only [colorMass, fiberMass, true_and] using hcap

/-- Combining a pure state ceiling with likelihood truncation gives
joint caps for every later submeasure, using the original palette. -/
theorem exists_measurable_truncation_with_caps (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n) (hX : Measurable X) (E Z : Fin n → ℕ)
    (cap : ℕ → ℝ) (hcap : ∀ e, μ.real {ω | E (X ω) = e} ≤ cap e)
    {R : ℝ} (hR : 1 < R) :
    ∃ G : Set Ω, MeasurableSet G ∧
      μ.real Gᶜ ≤ (entropy (atomMass μ X) (fun _ => 0) Z -
        entropy (atomMass μ X) E Z + 1) / Real.log R ∧
      ∀ ρ : Measure Ω, ρ ≤ μ.restrict G → ∀ e z : ℕ,
        ρ.real {ω | E (X ω) = e ∧ Z (X ω) = z} ≤
          R * cap e * μ.real {ω | Z (X ω) = z} := by
  obtain ⟨G, hG, hloss, hjoint⟩ := exists_measurable_truncation μ X hX E Z hR
  refine ⟨G, hG, hloss, ?_⟩
  intro ρ hρ e z
  have hmono : ρ.real {ω | E (X ω) = e ∧ Z (X ω) = z} ≤
      (μ.restrict G).real {ω | E (X ω) = e ∧ Z (X ω) = z} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (hρ _)
  calc
    _ ≤ (μ.restrict G).real {ω | E (X ω) = e ∧ Z (X ω) = z} := hmono
    _ ≤ R * μ.real {ω | E (X ω) = e} * μ.real {ω | Z (X ω) = z} := hjoint e z
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcap e) (by linarith)) ENNReal.toReal_nonneg

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation.PaletteTruncation
