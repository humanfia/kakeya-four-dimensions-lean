/- Adapted from: here:o254 (session x0898).
Original source pair restrictions and their exact base marginals. -/
import Mathlib

namespace Submission.Lib.K4MeshJitter

open MeasureTheory Set

noncomputable section

/-- A finite disjoint cover decomposes the entire original source law. -/
theorem partition_restrict_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : ∀ᵐ ω ∂μ, ∃ i, ω ∈ E i) :
    (∑ i, μ.restrict (E i)) = μ := by
  have hfull : μ.restrict (⋃ i, E i) = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [hcover] with ω hω
    exact mem_iUnion.mpr hω
  rw [Measure.restrict_iUnion hdisj hE, Measure.sum_fintype] at hfull
  exact hfull

theorem pair_partition_row {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (A : Set Ω) (F : ι → Set Ω)
    (hF : ∀ i, MeasurableSet (F i)) (hdisj : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ∀ᵐ ω ∂μ, ∃ i, ω ∈ F i) :
    (∑ i, μ.restrict (A ∩ F i)) = μ.restrict A := by
  calc
    _ = ∑ i, (μ.restrict A).restrict (F i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Measure.restrict_restrict (hF i), inter_comm]
    _ = _ := partition_restrict_sum (μ.restrict A) F hF hdisj
      (hcover.filter_mono (ae_mono Measure.restrict_le_self))

/-- The actual base law of an original pair entry. No representative point
or current index normalization is introduced. -/
def pairedBaseLaw {Ω B ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (μ : Measure Ω) (E : ι → Set Ω) (F : κ → Set Ω) (Y : Ω → B) (ij : ι × κ) : Measure B :=
  (μ.restrict (E ij.1 ∩ F ij.2)).map Y

theorem pairedBaseLaw_finite {Ω B ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ι → Set Ω) (F : κ → Set Ω)
    (Y : Ω → B) (ij : ι × κ) : IsFiniteMeasure (pairedBaseLaw μ E F Y ij) := by
  unfold pairedBaseLaw
  infer_instance

theorem pairedBaseLaw_row {Ω B ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace B] [Fintype κ]
    (μ : Measure Ω) (E : ι → Set Ω) (F : κ → Set Ω) (Y : Ω → B) (hY : Measurable Y)
    (hF : ∀ j, MeasurableSet (F j)) (hdisj : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ∀ᵐ ω ∂μ, ∃ j, ω ∈ F j) (i : ι) :
    (∑ j, pairedBaseLaw μ E F Y (i, j)) = (μ.restrict (E i)).map Y := by
  have hm := congrArg (fun ν : Measure Ω => ν.map Y) (pair_partition_row μ (E i) F hF hdisj hcover)
  rw [Measure.map_finset_sum' hY.aemeasurable] at hm
  exact hm

theorem pairedBaseLaw_column {Ω B ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace B] [Fintype ι]
    (μ : Measure Ω) (E : ι → Set Ω) (F : κ → Set Ω) (Y : Ω → B) (hY : Measurable Y)
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : ∀ᵐ ω ∂μ, ∃ i, ω ∈ E i) (j : κ) :
    (∑ i, pairedBaseLaw μ E F Y (i, j)) = (μ.restrict (F j)).map Y := by
  simpa only [pairedBaseLaw, inter_comm] using pairedBaseLaw_row μ F E Y hY hE hdisj hcover j

theorem pairedBaseLaw_total {Ω B ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [Fintype ι] [Fintype κ]
    (μ : Measure Ω) (E : ι → Set Ω) (F : κ → Set Ω) (Y : Ω → B) (hY : Measurable Y)
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ j, MeasurableSet (F j))
    (hdisjE : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hdisjF : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcoverE : ∀ᵐ ω ∂μ, ∃ i, ω ∈ E i) (hcoverF : ∀ᵐ ω ∂μ, ∃ j, ω ∈ F j) :
    (∑ i, ∑ j, pairedBaseLaw μ E F Y (i, j)) = μ.map Y := by
  simp_rw [pairedBaseLaw_row μ E F Y hY hF hdisjF hcoverF]
  have hm := congrArg (fun ν : Measure Ω => ν.map Y) (partition_restrict_sum μ E hE hdisjE hcoverE)
  rw [Measure.map_finset_sum' hY.aemeasurable] at hm
  exact hm

theorem pairedBaseLaw_ae {Ω B ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (μ : Measure Ω) (E : ι → Set Ω) (F : κ → Set Ω) (Y : Ω → B) (hY : Measurable Y)
    (i : ι) (j : κ) (hE : MeasurableSet (E i)) (hF : MeasurableSet (F j))
    {P : B → Prop} (hP : MeasurableSet {y | P y})
    (hsource : ∀ᵐ ω ∂μ, ω ∈ E i → ω ∈ F j → P (Y ω)) :
    ∀ᵐ y ∂pairedBaseLaw μ E F Y (i, j), P y := by
  apply (ae_map_iff hY.aemeasurable hP).mpr
  filter_upwards [ae_restrict_mem (hE.inter hF),
    hsource.filter_mono (ae_mono Measure.restrict_le_self)] with ω hω hp
  exact hp hω.1 hω.2

end
end Submission.Lib.K4MeshJitter
