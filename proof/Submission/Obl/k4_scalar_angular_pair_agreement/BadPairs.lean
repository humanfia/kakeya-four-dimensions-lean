import Mathlib
import Submission.Obl.k4_scalar_angular_pair_agreement.AllPairs
import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic

/-!
# Generic measure estimates for bad pairs

* A two-time set whose source part lies in `A ×ˢ J` has pair measure at most `|J|` times
  the one-time measure of the witness part over `A`.
* Sets that are disjoint within each fibre of a labelling and lie in a fixed set `Z` have
  total measure at most the number of fibres times the measure of `Z`.
* The closed coarse blocks `I T₁ b` overlap in null sets for `ν ⊗ vol` and its
  restrictions, so the measures of the pieces of a set over the coarse blocks add up to at
  most its measure.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

section Generic

variable {X : Type*} [MeasurableSpace X]

/-- The pair measure of `C ⋈ G` with `C ⊆ A ×ˢ J` is at most `|J|` times the measure of
the part of `G` over `A`. -/
lemma pairSet_le_witness (ν : Measure X) [SFinite ν] {Cs G : Set (X × ℝ)} {As : Set X}
    {Js : Set ℝ} {q0 : ℝ} (hC : MeasurableSet Cs) (hG : MeasurableSet G)
    (hA : MeasurableSet As) (hCsub : Cs ⊆ As ×ˢ Js) (hJ : volume Js ≤ ENNReal.ofReal q0) :
    (ν.prod (volume.prod volume)) (pairSet Cs G) ≤
      ENNReal.ofReal q0 * (ν.prod volume) (G ∩ As ×ˢ univ) := by
  rw [pairSet_measure ν hC hG, Measure.prod_apply (hG.inter (hA.prod MeasurableSet.univ)),
    ← lintegral_const_mul _ (measurable_measure_prodMk_left
      (hG.inter (hA.prod MeasurableSet.univ)))]
  apply lintegral_mono
  intro l
  dsimp only
  by_cases hl : l ∈ As
  · have h1 : volume (Prod.mk l ⁻¹' Cs) ≤ ENNReal.ofReal q0 := by
      refine le_trans (measure_mono ?_) hJ
      intro s hs
      exact (hCsub hs).2
    have h2 : Prod.mk l ⁻¹' (G ∩ As ×ˢ univ) = Prod.mk l ⁻¹' G := by
      ext s; simp [hl]
    rw [h2]
    gcongr
  · have h1 : Prod.mk l ⁻¹' Cs = ∅ := by
      ext s
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      intro hs
      exact hl (hCsub hs).1
    rw [h1, measure_empty, zero_mul]
    exact zero_le

end Generic

/-- Sets disjoint within each fibre of `jj` and contained in `Z` have total measure at most
the number of fibres times `μ Z`. -/
lemma sum_le_card_image_mul {α ι κ : Type*} [MeasurableSpace α] [DecidableEq κ]
    (μ : Measure α) (S : Finset ι) (jj : ι → κ) (Y : ι → Set α) (Z : Set α)
    (hY : ∀ i ∈ S, MeasurableSet (Y i))
    (hdisj : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → jj i = jj i' → Disjoint (Y i) (Y i'))
    (hsub : ∀ i ∈ S, Y i ⊆ Z) :
    ∑ i ∈ S, μ (Y i) ≤ ((S.image jj).card : ℝ≥0∞) * μ Z := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image jj) (g := jj)
    (fun i hi => Finset.mem_image_of_mem jj hi)]
  calc ∑ c ∈ S.image jj, ∑ i ∈ S with jj i = c, μ (Y i)
      ≤ ∑ c ∈ S.image jj, μ Z := by
        apply Finset.sum_le_sum
        intro c _
        rw [← measure_biUnion_finset]
        · apply measure_mono
          intro z hz
          simp only [mem_iUnion] at hz
          obtain ⟨i, hi, hz⟩ := hz
          exact hsub i (Finset.mem_filter.mp hi).1 hz
        · intro i hi i' hi' hne
          simp only [Finset.coe_filter, mem_ofPred_eq] at hi hi'
          exact hdisj i hi.1 i' hi'.1 hne (hi.2.trans hi'.2.symm)
        · intro i hi
          exact hY i (Finset.mem_filter.mp hi).1
    _ = ((S.image jj).card : ℝ≥0∞) * μ Z := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The coarse blocks overlap in `ν ⊗ vol`-null sets, so the pieces of `Z` over them have
total measure at most `μ Z` for any `μ ≤ ν ⊗ vol`. -/
lemma sum_coarse_le {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν]
    (μ : Measure (X × ℝ)) (hμ : μ ≤ ν.prod volume) (Z : Set (X × ℝ)) (hZ : MeasurableSet Z)
    (T₁ : ℕ) :
    ∑ b : Fin (2 ^ T₁), μ (Z ∩ univ ×ˢ I T₁ b) ≤ μ Z := by
  rw [← measure_biUnion_finset₀]
  · apply measure_mono
    intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨b, _, hz⟩ := hz
    exact hz.1
  · intro b _ b' _ hne
    show μ ((Z ∩ univ ×ˢ I T₁ b) ∩ (Z ∩ univ ×ˢ I T₁ b')) = 0
    apply le_antisymm _ zero_le
    calc μ ((Z ∩ univ ×ˢ I T₁ b) ∩ (Z ∩ univ ×ˢ I T₁ b'))
        ≤ (ν.prod volume) (univ ×ˢ (I T₁ b ∩ I T₁ b')) := by
          refine (hμ _).trans (measure_mono ?_)
          intro z hz
          exact ⟨trivial, hz.1.2.2, hz.2.2.2⟩
      _ = 0 := by
          rw [Measure.prod_prod, volume_I_inter T₁ hne, mul_zero]
  · intro b _
    exact (hZ.inter (MeasurableSet.univ.prod (measurableSet_I T₁ b))).nullMeasurableSet

end Submission.Obl.k4_scalar_angular_pair_agreement
