-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit cc2492748f08.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/FiniteCodeTransport.lean.
import Submission.Obl.k4_matching_cofinal_palette_selection.FiniteCode
import Submission.Obl.k4_matching_cofinal_palette_selection.FiniteLaw
import Submission.Obl.k4_finite_affine_parent_sources.FiniteNormalization

/-! Exact finite-code mass transport and representatives on positive-mass cells. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

open Finset Classical Set MeasureTheory
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-- Representatives of positive-mass code cells can satisfy every given
almost-everywhere source property. Zero-mass representatives are arbitrary. -/
theorem exists_positive_code_representatives
    {Y : Type*} [MeasurableSpace Y] {n : ℕ} (μ : Measure Y) (code : Y → Fin n)
    (y₀ : Y) (Good : Y → Prop) (hGood : ∀ᵐ y ∂μ, Good y) :
    ∃ rep : Fin n → Y, ∀ i, 0 < μ.real (code ⁻¹' {i}) → Good (rep i) ∧ code (rep i) = i := by
  have hex (i : Fin n) (hi : 0 < μ.real (code ⁻¹' {i})) : ∃ y, Good y ∧ code y = i := by
    by_contra hn
    have hAE : ∀ᵐ y ∂μ, code y ≠ i := hGood.mono fun y hy hcode => hn ⟨y, hy, hcode⟩
    have hz : μ (code ⁻¹' {i}) = 0 := by
      rw [show code ⁻¹' {i} = {y | code y = i} by ext y; simp [eq_comm]]
      simpa using ae_iff.mp hAE
    have hr : μ.real (code ⁻¹' {i}) = 0 := by
      rw [measureReal_def, hz, ENNReal.toReal_zero]
    exact (ne_of_gt hi) hr
  refine ⟨fun i => if h : 0 < μ.real (code ⁻¹' {i}) then Classical.choose (hex i h) else y₀, ?_⟩
  intro i hi
  simp only [dite_eq_left hi]
  exact Classical.choose_spec (hex i hi)

/-- Reuse the accepted finite-code mass identity for any decoded label. -/
theorem finite_code_fiber_mass
    {Y A : Type*} [MeasurableSpace Y] [DecidableEq A] {n : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ] (code : Y → Fin n) (hcode : Measurable code)
    (label : Fin n → A) (a : A) :
    fiberMass (fun i => μ.real (code ⁻¹' {i})) label a = μ.real {y | label (code y) = a} := by
  have h := Submission.Obl.k4_matching_cofinal_palette_selection.sum_atomMass μ code hcode
    (univ.filter (fun i => label i = a))
  simpa [fiberMass, Submission.Obl.k4_matching_cofinal_palette_selection.atomMass] using h

theorem finite_code_fiber_mass_ae
    {Y A : Type*} [MeasurableSpace Y] [DecidableEq A] {n : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ] (code : Y → Fin n) (hcode : Measurable code)
    (label : Fin n → A) (original : Y → A)
    (hcompat : ∀ᵐ y ∂μ, label (code y) = original y) (a : A) :
    fiberMass (fun i => μ.real (code ⁻¹' {i})) label a = μ.real {y | original y = a} := by
  rw [finite_code_fiber_mass μ code hcode label a]
  apply measureReal_congr
  filter_upwards [hcompat] with y hy
  simp only [hy]

/-- Restricting a finite table selects exactly the corresponding original
event. The original source measure and the actual code cells are unchanged. -/
theorem finite_restricted_code_fiber_mass
    {Y A : Type*} [MeasurableSpace Y] [DecidableEq A] {n : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ] (code : Y → Fin n) (hcode : Measurable code)
    (S : Finset (Fin n)) (label : Fin n → A) (a : A) :
    fiberMass (fun i => if i ∈ S then μ.real (code ⁻¹' {i}) else 0) label a =
      μ.real {y | code y ∈ S ∧ label (code y) = a} := by
  change (∑ i ∈ univ.filter (fun i => label i = a),
    if i ∈ S then Submission.Obl.k4_matching_cofinal_palette_selection.atomMass μ code i else 0) = _
  rw [← sum_filter]
  have h := Submission.Obl.k4_matching_cofinal_palette_selection.sum_atomMass μ code hcode
    ((univ.filter (fun i => label i = a)).filter (fun i => i ∈ S))
  refine h.trans ?_
  congr 1
  ext y
  simp [and_comm]

/-- A heavy bin of the normalized retained table restores to a counted mass
in the original measure, including its actual retained source support. -/
theorem finite_code_selected_mass_restore
    {Y A : Type*} [MeasurableSpace Y] [DecidableEq A] {n : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ] (code : Y → Fin n) (hcode : Measurable code)
    (S : Finset (Fin n)) (label : Fin n → A) (a : A) (M q : ℝ) (hM : 0 < M)
    (hmass : q ≤ ∑ i ∈ univ.filter (fun i => label i = a),
      M⁻¹ * (if i ∈ S then μ.real (code ⁻¹' {i}) else 0)) :
    ENNReal.ofReal (M * q) ≤ μ {y | code y ∈ S ∧ label (code y) = a} := by
  have h := finite_selected_mass_restore (univ.filter (fun i => label i = a))
    (fun i => if i ∈ S then μ.real (code ⁻¹' {i}) else 0) M q hM hmass
  change M * q ≤ fiberMass (fun i => if i ∈ S then μ.real (code ⁻¹' {i}) else 0) label a at h
  rw [finite_restricted_code_fiber_mass μ code hcode S label a] at h
  have h' := ENNReal.ofReal_le_ofReal h
  rwa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h'

end

end Submission.Obl.k4_finite_affine_parent_sources
