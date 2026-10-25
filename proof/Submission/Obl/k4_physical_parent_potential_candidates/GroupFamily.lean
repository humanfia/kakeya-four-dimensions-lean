import Submission.Obl.k4_physical_parent_potential_candidates.GroupRetention

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory
open scoped ENNReal

noncomputable section

def lineBin {Λ : Type*} (A : Set Λ) (bin : Λ → ℤ) (g : ℤ) : Set Λ :=
  A ∩ bin ⁻¹' {g}

theorem measurableSet_lineBin {Λ : Type*} [MeasurableSpace Λ]
    {A : Set Λ} (hA : MeasurableSet A) {bin : Λ → ℤ} (hbin : Measurable bin) (g : ℤ) :
    MeasurableSet (lineBin A bin g) := hA.inter (hbin (measurableSet_singleton g))

theorem lineBin_prior_sum_le {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] {A Aold : Set Λ} (hA : MeasurableSet A)
    (hsub : A ⊆ Aold) {bin : Λ → ℤ} (hbin : Measurable bin) (groups : Finset ℤ) :
    (∑ g ∈ groups, ν.real (lineBin A bin g)) ≤ ν.real Aold := by
  have hENN : (∑ g ∈ groups, ν (lineBin A bin g)) ≤ ν Aold := by
    rw [← measure_biUnion_finset]
    · exact measure_mono (iUnion₂_subset fun g hg => inter_subset_left.trans hsub)
    · intro g hg g' hg' hne
      exact ((Set.disjoint_singleton.mpr hne).preimage bin).mono inter_subset_right inter_subset_right
    · exact fun g _ => measurableSet_lineBin hA hbin g
  have hr := ENNReal.toReal_mono (measure_ne_top ν Aold) hENN
  simpa only [measureReal_def, ENNReal.toReal_sum (fun _ _ => measure_ne_top ν _)] using hr

/-- A source inside one old block has finite mass under the original prior. -/
theorem original_block_mass_le {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A : Set Λ) (t0 h : ℝ)
    (S : Set (Λ × ℝ)) (hS : S ⊆ A ×ˢ Icc t0 (t0+h)) :
    ((ν.prod volume).restrict S) univ ≤ ENNReal.ofReal h * ν A := by
  simp only [Measure.restrict_apply_univ]
  exact (measure_mono hS).trans_eq (by
    rw [Measure.prod_prod, Real.volume_Icc, add_sub_cancel_left, mul_comm])

/-- Coarse state ratios for a retained group are estimates of the original
product restriction, and remain so after displaying its original line set. -/
theorem original_retained_group_coarse_ratio
    {Λ I B : Type*} [MeasurableSpace Λ] [MeasurableSpace I] [Countable I]
    [MeasurableSingletonClass I]
    (ν : Measure Λ) (S : Set (Λ × ℝ)) (state : (Λ × ℝ) → I)
    (hstate : Measurable state) (T : Set (Λ × ℝ)) (hT : MeasurableSet T)
    (hTS : T ⊆ S) (A : Set Λ) (hA : MeasurableSet A)
    (hTA : ∀ e ∈ T, e.1 ∈ A)
    (f : ENNReal) (hf0 : f ≠ 0) (hftop : f ≠ ⊤)
    (coarse : I → B) (b : B) (Q : Set (Λ × ℝ)) (hQ : MeasurableSet Q) (η : ENNReal)
    (hη : ∀ i, ((ν.prod volume).restrict S) (state ⁻¹' {i} ∩ Q) ≤
      η * ((ν.prod volume).restrict S) (state ⁻¹' {i})) :
    let G := Submission.Lib.K4StateFractionKeep.fractionKeep
      ((ν.prod volume).restrict S) state T f
    (((ν.prod volume).restrict G).restrict
      {e | e.1 ∈ A ∧ coarse (state e) = b}) Q ≤
      (η/f) * ((ν.prod volume).restrict G)
        {e | e.1 ∈ A ∧ coarse (state e) = b} := by
  dsimp only
  let μ := (ν.prod volume).restrict S
  let G := Submission.Lib.K4StateFractionKeep.fractionKeep μ state T f
  have hGm : MeasurableSet G :=
    Submission.Lib.K4StateFractionKeep.measurableSet_fractionKeep hstate hT f
  have hGT : G ⊆ T := inter_subset_left
  have hGS : G ⊆ S := hGT.trans hTS
  have hGline : ∀ e ∈ G, e.1 ∈ A := fun e he => hTA e (hGT he)
  have hraw : μ.restrict G = (ν.prod volume).restrict G :=
    Measure.restrict_restrict_of_subset hGS
  have hr := fraction_keep_coarse_event_ratio μ state hstate T hT hf0 hftop
    coarse b Q hQ η hη
  rw [hraw] at hr
  rw [Measure.restrict_apply hQ, Measure.restrict_apply' hGm, Measure.restrict_apply' hGm]
  rw [Measure.restrict_apply' hGm, Measure.restrict_apply' hGm] at hr
  have hleft : Q ∩ {e : Λ × ℝ | e.1 ∈ A ∧ coarse (state e) = b} ∩ G =
      {e | coarse (state e) = b ∧ e ∈ Q} ∩ G := by
    ext e
    simp only [mem_inter_iff, mem_setOf_eq]
    constructor
    · exact fun he => ⟨⟨he.1.2.2, he.1.1⟩, he.2⟩
    · exact fun he => ⟨⟨he.1.2, hGline e he.2, he.1.1⟩, he.2⟩
  have hright : {e : Λ × ℝ | e.1 ∈ A ∧ coarse (state e) = b} ∩ G =
      {e | coarse (state e) = b} ∩ G := by
    ext e
    simp only [mem_inter_iff, mem_setOf_eq]
    constructor
    · exact fun he => ⟨he.1.2, he.2⟩
    · exact fun he => ⟨⟨hGline e he.2, he.1⟩, he.2⟩
  rw [hleft, hright]
  exact hr

end

end Submission.Obl.k4_physical_parent_potential_candidates
