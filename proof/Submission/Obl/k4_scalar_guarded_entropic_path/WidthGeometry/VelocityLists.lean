/-
Adapted from this LOT tree, obligation o134, session x0438, commit 2e990309978b,
Submission/Obl/k4_scalar_guarded_tangent_obstruction/VelocityLists.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.ScalarGeometry
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.CountedLists

namespace Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

noncomputable def velocityList (Λ : X → Finset ι) (v : ι → ℝ) (δ : ℝ) (x : X) : Finset ℤ :=
  (Λ x).biUnion (fun i => neighboringVelocityBins δ (v i))

theorem measurable_velocityList (Λ : X → Finset ι) (v : ι → ℝ) (δ : ℝ)
    (hΛ : ∀ i, MeasurableSet {x | i ∈ Λ x}) (b : ℤ) :
    MeasurableSet {x | b ∈ velocityList Λ v δ x} := by
  classical
  have heq : {x | b ∈ velocityList Λ v δ x} =
      ⋃ i : ι, {x | i ∈ Λ x} ∩ {x | b ∈ neighboringVelocityBins δ (v i)} := by
    ext x
    simp only [velocityList, Finset.mem_biUnion, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  apply (hΛ i).inter
  by_cases hb : b ∈ neighboringVelocityBins δ (v i) <;> simp only [hb] <;> simp

omit [MeasurableSpace X] [Fintype ι] in
theorem card_velocityList_le (Λ : X → Finset ι) (v : ι → ℝ) (δ : ℝ) (x : X) :
    (velocityList Λ v δ x).card ≤ 3 * (Λ x).card := by
  calc
    _ ≤ ∑ i ∈ Λ x, (neighboringVelocityBins δ (v i)).card := Finset.card_biUnion_le
    _ = 3 * (Λ x).card := by simp only [card_neighboringVelocityBins, Finset.sum_const,
      smul_eq_mul, mul_comm]

omit [MeasurableSpace X] [Fintype ι] in
theorem velocity_bin_mem_list (Λ : X → Finset ι) (v : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (x : X) (i : ι) (hi : i ∈ Λ x) (velocity : ℝ)
    (hclose : |velocity - v i| ≤ δ) :
    (⌊velocity / δ⌋ : ℤ) ∈ velocityList Λ v δ x :=
  Finset.mem_biUnion.mpr ⟨i, hi, mem_neighboringVelocityBins hδ hclose⟩

/-- A short chart list, narrow velocity ranges and an angular joint
ceiling bound mass in the unchanged original observation law. -/
theorem mass_le_velocity_list_budget
    (σ : MeasureTheory.Measure X) [MeasureTheory.SFinite σ]
    (ξ : MeasureTheory.Measure (X × ℤ)) (Λ : X → Finset ι) (v : ι → ℝ) (δ : ℝ)
    (hΛ : ∀ i, MeasurableSet {x | i ∈ Λ x}) (c D : ENNReal)
    (hcard : ∀ x, ((Λ x).card : ENNReal) ≤ D)
    (hdom : ξ ≤ c • (σ.prod MeasureTheory.Measure.count))
    (hcover : ∀ᵐ z ∂ξ, ∃ i ∈ Λ z.1, z.2 ∈ neighboringVelocityBins δ (v i)) :
    ξ Set.univ ≤ (3 * c * D) * σ Set.univ := by
  have hcard' (x : X) : ((velocityList Λ v δ x).card : ENNReal) ≤ 3 * D := by
    calc
      _ ≤ ((3 * (Λ x).card : ℕ) : ENNReal) := by exact_mod_cast card_velocityList_le Λ v δ x
      _ = 3 * ((Λ x).card : ENNReal) := by simp only [Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ 3 * D := by gcongr; exact hcard x
  have hmem : ∀ᵐ z ∂ξ, z.2 ∈ velocityList Λ v δ z.1 := by
    filter_upwards [hcover] with z hz
    exact Finset.mem_biUnion.mpr hz
  have hsupport : ξ (countedListEvent (velocityList Λ v δ))ᶜ = 0 :=
    MeasureTheory.ae_iff.mp hmem
  calc
    _ ≤ (c * (3 * D)) * σ Set.univ :=
      mass_le_counted_list_budget σ ξ (velocityList Λ v δ)
        (measurable_velocityList Λ v δ hΛ) c (3 * D) hcard' hdom hsupport
    _ = _ := by ring

end Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry
