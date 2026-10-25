import Submission.Obl.k4_scalar_grid_parameter_preparation.Statement
import Submission.Obl.k4_scalar_grid_parameter_preparation.CoefficientPriorCaps
import Submission.Obl.k4_scalar_grid_parameter_preparation.WeightedPruning

/-!
# Bookkeeping for the final assembly

Density bounds pass to submasks, the weighted mass survives a chain of five deletions, and the
coefficient and physical tags of the kernels agree with those of the frozen statement.
-/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

/-- A density bound between two measures restricted to `E` holds on every measurable `E' ⊆ E`. -/
theorem smul_restrict_le_of_subset {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    {E E' : Set α} (hE' : MeasurableSet E') (hsub : E' ⊆ E) (c : ℝ≥0∞)
    (h : c • μ.restrict E ≤ ν.restrict E) : c • μ.restrict E' ≤ ν.restrict E' := by
  have h1 := Measure.restrict_mono (le_refl E') h
  rwa [Measure.restrict_smul, Measure.restrict_restrict hE', Measure.restrict_restrict hE',
    Set.inter_eq_left.mpr hsub] at h1

theorem restrict_le_smul_of_subset {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    {E E' : Set α} (hE' : MeasurableSet E') (hsub : E' ⊆ E) (c : ℝ≥0∞)
    (h : ν.restrict E ≤ c • μ.restrict E) : ν.restrict E' ≤ c • μ.restrict E' := by
  have h1 := Measure.restrict_mono (le_refl E') h
  rwa [Measure.restrict_smul, Measure.restrict_restrict hE', Measure.restrict_restrict hE',
    Set.inter_eq_left.mpr hsub] at h1

/-- Five successive deletions, of costs `5, 2, 1, 1, 1` hundredths of `1 / K`, leave a set whose
complement costs at most `1 / (10 K)`. -/
theorem compl_le_of_chain {α : Type*} [MeasurableSpace α] (μ : Measure α) {K : ℝ} (hK : 0 < K)
    {E₁ E₂ E₃ E₄ E₅ : Set α}
    (l₁ : μ E₁ᶜ ≤ ENNReal.ofReal (5 / (100 * K)))
    (l₂ : μ (E₁ \ E₂) ≤ ENNReal.ofReal (2 / (100 * K)))
    (l₃ : μ (E₂ \ E₃) ≤ ENNReal.ofReal (1 / (100 * K)))
    (l₄ : μ (E₃ \ E₄) ≤ ENNReal.ofReal (1 / (100 * K)))
    (l₅ : μ (E₄ \ E₅) ≤ ENNReal.ofReal (1 / (100 * K))) :
    μ E₅ᶜ ≤ ENNReal.ofReal (10 / (100 * K)) := by
  have hcover : E₅ᶜ ⊆ E₁ᶜ ∪ (E₁ \ E₂) ∪ (E₂ \ E₃) ∪ (E₃ \ E₄) ∪ (E₄ \ E₅) := by
    intro p hp
    by_cases p1 : p ∈ E₁
    · by_cases p2 : p ∈ E₂
      · by_cases p3 : p ∈ E₃
        · by_cases p4 : p ∈ E₄
          · exact Or.inr ⟨p4, hp⟩
          · exact Or.inl (Or.inr ⟨p3, p4⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨p2, p3⟩))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨p1, p2⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl p1)))
  have hpos : ∀ a : ℝ, 0 ≤ a → 0 ≤ a / (100 * K) := fun a ha => div_nonneg ha (by positivity)
  calc
    μ E₅ᶜ ≤ μ E₁ᶜ + μ (E₁ \ E₂) + μ (E₂ \ E₃) + μ (E₃ \ E₄) + μ (E₄ \ E₅) := by
      refine (measure_mono hcover).trans ?_
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (5 / (100 * K)) + ENNReal.ofReal (2 / (100 * K)) +
        ENNReal.ofReal (1 / (100 * K)) + ENNReal.ofReal (1 / (100 * K)) +
        ENNReal.ofReal (1 / (100 * K)) := by gcongr
    _ = ENNReal.ofReal (10 / (100 * K)) := by
      rw [← ENNReal.ofReal_add (hpos 5 (by norm_num)) (hpos 2 (by norm_num)),
        ← ENNReal.ofReal_add (by positivity) (hpos 1 (by norm_num)),
        ← ENNReal.ofReal_add (by positivity) (hpos 1 (by norm_num)),
        ← ENNReal.ofReal_add (by positivity) (hpos 1 (by norm_num))]
      congr 1
      ring

/-- The weighted mass left after losing at most `1 / (10 K)` in every world. -/
theorem retained_weighted_mass {α : Type*} [MeasurableSpace α] {W : ℕ}
    (μ : Fin W → Measure α) (ω : Fin W → ℝ) (E : Fin W → Set α) {K : ℝ} (hK : 0 < K)
    (hω : ∀ g, 0 ≤ ω g) (hsum : (∑ g, ω g) = 1)
    (hmass : ENNReal.ofReal K⁻¹ ≤ ∑ g, ENNReal.ofReal (ω g) * μ g Set.univ)
    (hloss : ∀ g, μ g (E g)ᶜ ≤ ENNReal.ofReal (10 / (100 * K))) :
    ENNReal.ofReal (1 / (2 * K)) ≤ ∑ g, ENNReal.ofReal (ω g) * (μ g).restrict (E g) Set.univ := by
  have hw : (∑ g, ENNReal.ofReal (ω g)) ≤ 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => hω g), hsum, ENNReal.ofReal_one]
  have h := weighted_retained_mass_of_uniform_loss μ (fun g => ENNReal.ofReal (ω g)) E
    (1 / K) (10 / (100 * K)) (by positivity) (by positivity)
    (by
      have e : (10 : ℝ) / (100 * K) = (1 / K / 2) * (1 / 5) := by field_simp; ring
      rw [e]
      exact mul_le_of_le_one_right (by positivity) (by norm_num)) hw
    (by rwa [one_div]) hloss
  simp only [Measure.restrict_apply_univ]
  convert h using 2
  field_simp

/-- The mixed coefficient tag with equal widths is the coefficient tag of the frozen statement. -/
theorem scalarMixedCoefficientTag_self (N r : ℝ) (l : ℕ × (Fin 5 → ℝ)) :
    scalarMixedCoefficientTag (N ^ (-r)) (N ^ (-r)) l.2 = coeffTag N r l := by
  funext e
  simp only [scalarMixedCoefficientTag, coeffTag, ite_self]

/-- A set with positive restricted measure meets the restricting set. -/
theorem exists_mem_of_restrict_ne_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E S : Set α} (hE : MeasurableSet E) (h : μ.restrict E S ≠ 0) : ∃ p ∈ E, p ∈ S := by
  rw [Measure.restrict_apply' hE] at h
  obtain ⟨p, hpS, hpE⟩ := (Set.nonempty_iff_ne_empty (s := S ∩ E)).mpr
    (fun he => h (by rw [he, measure_empty]))
  exact ⟨p, hpE, hpS⟩

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
