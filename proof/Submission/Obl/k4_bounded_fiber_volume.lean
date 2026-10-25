import Mathlib
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Regularize

namespace Submission.Obl.k4_bounded_fiber_volume

open Set MeasureTheory
open scoped ENNReal Function

/-- A locally injective map has a countable disjoint measurable partition of its
measurable domain into injective pieces. -/
theorem exists_injective_measurable_partition
    {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (S : Set E) (hS : MeasurableSet S) (f : E → E)
    (hlocal : ∀ x ∈ S, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ InjOn f V) :
    ∃ pieces : ℕ → Set E, (∀ n, MeasurableSet (pieces n)) ∧
      Pairwise (Disjoint on pieces) ∧ S = ⋃ n, pieces n ∧
      (∀ n, pieces n ⊆ S) ∧ ∀ n, InjOn f (pieces n) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · refine ⟨fun _ => ∅, by simp, ?_, by simp, by simp, by simp⟩
    intro i j hij
    simp
  have : Nonempty S := hSne.to_subtype
  choose V hVo hVmem hVinj using fun x : S => hlocal x x.2
  have hcover : S ⊆ ⋃ x : S, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hVmem ⟨x, hx⟩⟩
  obtain ⟨seq, hseq⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover V hVo hcover
  let U : ℕ → Set E := disjointed (fun n => V (seq n))
  let pieces : ℕ → Set E := fun n => S ∩ U n
  refine ⟨pieces, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hS.inter ((MeasurableSet.disjointed fun n => (hVo (seq n)).measurableSet) n)
  · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right
  · dsimp [pieces]
    rw [← inter_iUnion, iUnion_disjointed]
    exact (inter_eq_left.mpr hseq).symm
  · intro n
    exact inter_subset_left
  · intro n
    exact (hVinj (seq n)).mono (inter_subset_right.trans (disjointed_subset _ _))

open Classical in
/-- Disjoint pieces have image overlap bounded by the cardinality of a fiber. -/
theorem image_overlap_le_of_finite_fiber {E : Type*}
    (S : Set E) (f : E → E) (pieces : ℕ → Set E)
    (hdisj : Pairwise (Disjoint on pieces)) (hsub : ∀ n, pieces n ⊆ S)
    (y : E) (M : ℕ) (hfin : {x : E | x ∈ S ∧ f x = y}.Finite)
    (hcard : {x : E | x ∈ S ∧ f x = y}.ncard ≤ M) (F : Finset ℕ) :
    (F.filter (fun n => y ∈ f '' pieces n)).card ≤ M := by
  classical
  let I := F.filter (fun n => y ∈ f '' pieces n)
  have hex : ∀ n ∈ I, ∃ x, x ∈ pieces n ∧ f x = y := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  choose g hgmem hgy using hex
  let g' : ℕ → E := fun n => if hn : n ∈ I then g n hn else y
  have hgmem' (n : ℕ) (hn : n ∈ I) : g' n ∈ pieces n := by
    simpa only [g', dite_eq_left hn] using hgmem n hn
  have hgy' (n : ℕ) (hn : n ∈ I) : f (g' n) = y := by
    simpa only [g', dite_eq_left hn] using hgy n hn
  have hinj : InjOn g' (I : Set ℕ) := by
    intro n hn m hm hnm
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (hgmem' n hn) (hnm.symm ▸ hgmem' m hm)
  have hmap : ∀ n ∈ (I : Set ℕ), g' n ∈ {x : E | x ∈ S ∧ f x = y} := by
    intro n hn
    exact ⟨hsub n (hgmem' n hn), hgy' n hn⟩
  have h := Set.ncard_le_ncard_of_injOn g' hmap hinj hfin
  rw [Set.ncard_coe_finset] at h
  exact h.trans hcard

/-- The multiplicity area inequality follows from local injectivity and a
uniform finite bound on the fibers. -/
theorem lintegral_abs_det_le_of_local_inj_finite_fibers
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Set E) (hS : MeasurableSet S) (f : E → E) (f' : E → E →L[ℝ] E)
    (hderiv : ∀ x ∈ S, HasFDerivWithinAt f (f' x) S x)
    (hlocal : ∀ x ∈ S, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ InjOn f V)
    (T : Set E) (hT : MeasurableSet T) (hmaps : MapsTo f S T) (M : ℕ)
    (hfiber : ∀ y ∈ T, {x : E | x ∈ S ∧ f x = y}.Finite ∧
      {x : E | x ∈ S ∧ f x = y}.ncard ≤ M) :
    (∫⁻ x in S, ENNReal.ofReal |(f' x).det| ∂μ) ≤ (M : ℝ≥0∞) * μ T := by
  classical
  obtain ⟨pieces, hmeas, hdisj, hcover, hsub, hinj⟩ :=
    exists_injective_measurable_partition S hS f hlocal
  have himage (n : ℕ) : MeasurableSet (f '' pieces n) :=
    measurable_image_of_fderivWithin (hmeas n)
      (fun x hx => (hderiv x (hsub n hx)).mono (hsub n)) (hinj n)
  have himsub (n : ℕ) : f '' pieces n ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps (hsub n hx)
  have heq (n : ℕ) : T ∩ (f '' pieces n) = f '' pieces n :=
    inter_eq_right.mpr (himsub n)
  have hsum : (∑' n, μ (f '' pieces n)) ≤ (M : ℝ≥0∞) * μ T := by
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    have hover : ∀ y ∈ T, (F.filter (fun n => y ∈ f '' pieces n)).card ≤ M := by
      intro y hy
      exact image_overlap_le_of_finite_fiber S f pieces hdisj hsub y M
        (hfiber y hy).1 (hfiber y hy).2 F
    have h := WangZahlLot.Obl.wz_regular_transverse_affine_cells.sum_inter_measure_le_of_overlap
      μ T hT (fun n => f '' pieces n) F (fun n hn => himage n) M hover
    simpa only [heq] using h
  calc
    (∫⁻ x in S, ENNReal.ofReal |(f' x).det| ∂μ) =
        ∑' n, ∫⁻ x in pieces n, ENNReal.ofReal |(f' x).det| ∂μ := by
      rw [hcover, lintegral_iUnion hmeas hdisj]
    _ = ∑' n, μ (f '' pieces n) := by
      congr 1
      funext n
      exact lintegral_abs_det_fderiv_eq_addHaar_image μ (hmeas n)
        (fun x hx => (hderiv x (hsub n hx)).mono (hsub n)) (hinj n)
    _ ≤ (M : ℝ≥0∞) * μ T := hsum

/-- A nonsingular derivative of a `C¹` map gives an injective open neighborhood. -/
theorem exists_open_injOn_of_contDiffAt_det_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] (f : E → E) (x : E)
    (hf : ContDiffAt ℝ 1 f x) (hdet : (fderiv ℝ f x).det ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ InjOn f V := by
  let e := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hdet
  have hderiv : HasFDerivAt f (e : E →L[ℝ] E) x := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  let p := hf.toOpenPartialHomeomorph f hderiv (by norm_num)
  refine ⟨p.source, p.open_source, ?_, ?_⟩
  · exact hf.mem_toOpenPartialHomeomorph_source hderiv (by norm_num)
  · have hcoe : (p : E → E) = f := hf.toOpenPartialHomeomorph_coe hderiv (by norm_num)
    simpa only [hcoe] using p.injOn

/-- A differentiable map which is locally injective on a measurable set has a
measurable image of that set. -/
theorem measurable_image_of_local_inj
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (S : Set E) (hS : MeasurableSet S) (f : E → E) (f' : E → E →L[ℝ] E)
    (hderiv : ∀ x ∈ S, HasFDerivWithinAt f (f' x) S x)
    (hlocal : ∀ x ∈ S, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ InjOn f V) :
    MeasurableSet (f '' S) := by
  obtain ⟨pieces, hmeas, hdisj, hcover, hsub, hinj⟩ :=
    exists_injective_measurable_partition S hS f hlocal
  rw [hcover, image_iUnion]
  apply MeasurableSet.iUnion
  intro n
  exact measurable_image_of_fderivWithin (hmeas n)
    (fun x hx => (hderiv x (hsub n hx)).mono (hsub n)) (hinj n)

/-- The general bounded-fiber volume inequality needed by the slope-volume
reduction. It counts fibers only on the measurable set being integrated. -/
theorem bounded_fiber_volume
    (N : ℕ) (U T : Set (EuclideanSpace ℝ (Fin 3)))
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (J : ℝ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hT : MeasurableSet T) (hTU : T ⊆ U)
    (hJ : 0 < J) (hjac : ∀ s ∈ T, J ≤ |(fderiv ℝ f s).det|)
    (hfiber : ∀ x : EuclideanSpace ℝ (Fin 3),
      {s : EuclideanSpace ℝ (Fin 3) | s ∈ T ∧ f s = x}.Finite ∧
      {s : EuclideanSpace ℝ (Fin 3) | s ∈ T ∧ f s = x}.ncard ≤ N) :
    ENNReal.ofReal J * volume T ≤ (N : ENNReal) * volume (f '' T) := by
  have hcont (x) (hx : x ∈ T) : ContDiffAt ℝ 1 f x :=
    hf.contDiffAt (hU.mem_nhds (hTU hx))
  have hderiv (x) (hx : x ∈ T) : HasFDerivWithinAt f (fderiv ℝ f x) T x :=
    ((hcont x hx).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have hlocal (x) (hx : x ∈ T) :
      ∃ V : Set (EuclideanSpace ℝ (Fin 3)), IsOpen V ∧ x ∈ V ∧ InjOn f V := by
    apply exists_open_injOn_of_contDiffAt_det_ne_zero f x (hcont x hx)
    exact abs_pos.mp (hJ.trans_le (hjac x hx))
  have himage := measurable_image_of_local_inj T hT f (fderiv ℝ f) hderiv hlocal
  calc
    ENNReal.ofReal J * volume T ≤ ∫⁻ x in T, ENNReal.ofReal |(fderiv ℝ f x).det| := by
      rw [← setLIntegral_const T]
      apply setLIntegral_mono' hT
      intro x hx
      exact ENNReal.ofReal_le_ofReal (hjac x hx)
    _ ≤ (N : ENNReal) * volume (f '' T) :=
      lintegral_abs_det_le_of_local_inj_finite_fibers volume T hT f (fderiv ℝ f)
        hderiv hlocal (f '' T) himage (mapsTo_image f T) N (fun x hx => hfiber x)

end Submission.Obl.k4_bounded_fiber_volume

theorem Submission.k4_bounded_fiber_volume
    (N : ℕ) (U T : Set (EuclideanSpace ℝ (Fin 3)))
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (J : ℝ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hT : MeasurableSet T) (hTU : T ⊆ U)
    (hJ : 0 < J) (hjac : ∀ s ∈ T, J ≤ |(fderiv ℝ f s).det|)
    (hfiber : ∀ x : EuclideanSpace ℝ (Fin 3),
      {s : EuclideanSpace ℝ (Fin 3) | s ∈ T ∧ f s = x}.Finite ∧
      {s : EuclideanSpace ℝ (Fin 3) | s ∈ T ∧ f s = x}.ncard ≤ N) :
    ENNReal.ofReal J * MeasureTheory.volume T ≤ (N : ENNReal) * MeasureTheory.volume (f '' T) := by
  exact Submission.Obl.k4_bounded_fiber_volume.bounded_fiber_volume N U T f J hU hf hT hTU hJ hjac hfiber
