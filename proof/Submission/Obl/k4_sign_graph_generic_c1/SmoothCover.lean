import Mathlib
import LeanPool.SardMoreira.MainTheorem

noncomputable section

open Set Filter MeasureTheory Module
open scoped Topology ContDiff NNReal ENNReal

namespace Submission.Obl.k4_sign_graph_generic_c1

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The open locus where the graph is a `C¹` graph over an open part of its domain. -/
def smoothLocus (Sigma : Set Space) (b : Space → Space) : Set Space :=
  interior (Sigma ∩ {s | ContDiffAt ℝ 1 b s})

theorem isOpen_smoothLocus (Sigma : Set Space) (b : Space → Space) :
    IsOpen (smoothLocus Sigma b) := isOpen_interior

theorem smoothLocus_subset (Sigma : Set Space) (b : Space → Space) :
    smoothLocus Sigma b ⊆ Sigma := fun _ hx => (interior_subset hx).1

theorem contDiffOn_smoothLocus (Sigma : Set Space) (b : Space → Space) :
    ContDiffOn ℝ 1 b (smoothLocus Sigma b) :=
  (isOpen_smoothLocus Sigma b).contDiffOn_iff.mpr fun _ hx => (interior_subset hx).2

theorem mem_smoothLocus {Sigma : Set Space} {b : Space → Space} {s : Space}
    (hSigma : Sigma ∈ 𝓝 s) (hb : ContDiffAt ℝ 1 b s) : s ∈ smoothLocus Sigma b := by
  apply mem_interior_iff_mem_nhds.mpr
  exact inter_mem hSigma (hb.eventually (by simp))

/-- A smooth parametrization in a graph gives a smooth graph wherever its base projection is
surjective on tangent spaces. The parameter dimension can be arbitrary. -/
theorem mem_smoothLocus_of_surjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : E → Space} {U : Set E} {a : E} {Sigma : Set Space} {b : Space → Space}
    (hU : U ∈ 𝓝 a) (hf : ContDiffAt ℝ 1 f a) (hg : ContDiffAt ℝ 1 g a)
    (hgraph : ∀ x ∈ U, f x ∈ Sigma ∧ b (f x) = g x)
    (hsurj : Function.Surjective (fderiv ℝ f a)) : f a ∈ smoothLocus Sigma b := by
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hsurj
  let A : Space → E := fun z => a + L z
  have hA : A 0 = a := by simp [A]
  have hAd : HasFDerivAt A L 0 := by
    simpa [A] using (L.hasFDerivAt (x := (0 : Space))).const_add a
  have hAc : ContDiff ℝ 1 A := by fun_prop
  have hfA : ContDiffAt ℝ 1 f (A 0) := by simpa only [hA] using hf
  have hfc : ContDiffAt ℝ 1 (f ∘ A) 0 := hfA.comp 0 hAc.contDiffAt
  have hfd : HasFDerivAt (f ∘ A) (ContinuousLinearEquiv.refl ℝ Space : Space →L[ℝ] Space) 0 := by
    convert (hfA.differentiableAt (by norm_num)).hasFDerivAt.comp 0 hAd using 1
    apply ContinuousLinearMap.ext
    intro z
    simpa only [hA, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.refl_apply,
      ContinuousLinearEquiv.coe_coe] using (hL z).symm
  let v : Space → Space := hfc.localInverse hfd (by simp)
  have hv0 : v (f a) = 0 := by
    simpa [v, hA] using hfc.localInverse_apply_image hfd (by simp)
  have hvc : ContDiffAt ℝ 1 v (f a) := by
    simpa [v, hA] using hfc.to_localInverse hfd (by simp)
  have hv_right : ∀ᶠ s in 𝓝 (f a), f (A (v s)) = s := by
    simpa [v, hA, ContDiffAt.localInverse] using
      (hfc.hasStrictFDerivAt' hfd (by simp)).eventually_right_inverse
  have hsec : ContinuousAt (A ∘ v) (f a) := hAc.continuous.continuousAt.comp hvc.continuousAt
  have hsec0 : (A ∘ v) (f a) = a := by simp [hv0, hA]
  have hsecU : ∀ᶠ s in 𝓝 (f a), A (v s) ∈ U := by
    apply hsec.preimage_mem_nhds
    rwa [hsec0]
  have hSigma : Sigma ∈ 𝓝 (f a) := by
    filter_upwards [hsecU, hv_right] with s hs heq
    simpa [heq] using (hgraph _ hs).1
  have hbeq : b =ᶠ[𝓝 (f a)] g ∘ A ∘ v := by
    filter_upwards [hsecU, hv_right] with s hs heq
    simpa [heq] using (hgraph _ hs).2
  have hgc : ContDiffAt ℝ 1 (g ∘ A ∘ v) (f a) := by
    have hg' : ContDiffAt ℝ 1 g ((A ∘ v) (f a)) := by simpa only [hsec0] using hg
    exact hg'.comp _ (hAc.contDiffAt.comp _ hvc)
  exact mem_smoothLocus hSigma (hgc.congr_of_eventuallyEq hbeq)


/-- A smooth map into three-space sends the points where its derivative is not surjective to a
Lebesgue-null set. This includes maps whose parameter dimension is less than three. -/
theorem critical_image_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → Space} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  let C : Set E := {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}
  have hAbs : (volume : Measure Space) ≪ μH[3] := by
    have h : (volume : Measure Space) ≪ μH[(finrank ℝ Space : ℝ)] :=
      Measure.absolutelyContinuous_isAddHaarMeasure _ _
    simpa [Space] using h
  apply measure_zero_of_dimH_lt (d := 3) hAbs
  by_cases hd : 2 < finrank ℝ E
  · have hrank : ∀ x ∈ C, finrank ℝ (fderiv ℝ f x).range ≤ 2 := by
      intro x hx
      have hlt := Submodule.finrank_lt (mt LinearMap.range_eq_top.mp hx.2)
      have hdim : finrank ℝ Space = 3 := by simp [Space]
      rw [hdim] at hlt
      omega
    have hmoreira : dimH (f '' C) ≤ sardMoreiraBound (finrank ℝ E) (finrank ℝ E + 1) 0 2 := by
      apply dimH_image_le_sardMoreiraBound_of_finrank_le hd (Nat.succ_ne_zero _) _ hrank
      intro x hx
      exact (hf.contDiffAt (hU.mem_nhds hx.1)).contDiffMoreiraHolderAt
        (by exact WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top _)) 0
    apply hmoreira.trans_lt
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
    change (2 : ℝ) + (finrank ℝ E - 2 : ℕ) / ((finrank ℝ E + 1 : ℕ) + (0 : ℝ)) < 3
    have hpos : (0 : ℝ) < finrank ℝ E + 1 := by positivity
    rw [Nat.cast_add, Nat.cast_one, add_zero, Nat.cast_sub (by omega)]
    have hsmall : ((finrank ℝ E : ℝ) - 2) / (finrank ℝ E + 1) < 1 := by
      rw [div_lt_one hpos]
      linarith
    linarith
  · have hle : dimH (f '' C) ≤ (finrank ℝ E : ℝ≥0∞) := by
      calc
        dimH (f '' C) ≤ dimH C :=
          ((hf.differentiableOn (by simp)).mono fun _ hx => hx.1).dimH_image_le
        _ ≤ dimH (univ : Set E) := dimH_mono (subset_univ _)
        _ = finrank ℝ E := Real.dimH_univ_eq_finrank E
    apply hle.trans_lt
    have : finrank ℝ E < 3 := by omega
    exact_mod_cast this


/-- Countably many smooth parametrizations contained in a graph imply generic `C¹` regularity.
No injectivity of the parametrizations and no dimension bound on their domains is required. -/
theorem exists_open_c1_of_countable_smooth_graph_cover
    {ι : Type*} [Countable ι] (d : ι → ℕ)
    (U : ∀ i, Set (Fin (d i) → ℝ))
    (f g : ∀ i, (Fin (d i) → ℝ) → Space)
    (Sigma : Set Space) (b : Space → Space)
    (hU : ∀ i, IsOpen (U i))
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    (hgraph : ∀ i x, x ∈ U i → f i x ∈ Sigma ∧ b (f i x) = g i x)
    (hcover : Sigma ⊆ ⋃ i, f i '' U i) :
    ∃ S : Set Space, IsOpen S ∧ ContDiffOn ℝ 1 b S ∧ S ⊆ Sigma ∧
      volume (Sigma \ S) = 0 := by
  refine ⟨smoothLocus Sigma b, isOpen_smoothLocus _ _, contDiffOn_smoothLocus _ _,
    smoothLocus_subset _ _, ?_⟩
  have hnull : volume (⋃ i, f i '' {x | x ∈ U i ∧
      ¬ Function.Surjective (fderiv ℝ (f i) x)}) = 0 := by
    apply measure_iUnion_null
    intro i
    exact critical_image_null (hU i) (hf i)
  apply measure_mono_null _ hnull
  intro s hs
  obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp (hcover hs.1)
  apply mem_iUnion.mpr
  refine ⟨i, x, ⟨hx, ?_⟩, rfl⟩
  intro hsurj
  apply hs.2
  exact mem_smoothLocus_of_surjective ((hU i).mem_nhds hx)
    (((hf i).contDiffAt ((hU i).mem_nhds hx)).of_le (by decide))
    (((hg i).contDiffAt ((hU i).mem_nhds hx)).of_le (by decide))
    (hgraph i) hsurj

end Submission.Obl.k4_sign_graph_generic_c1
