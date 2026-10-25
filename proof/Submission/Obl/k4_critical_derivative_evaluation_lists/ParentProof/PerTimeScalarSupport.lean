/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, PerTimeScalarSupport.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.GroupScalarSupport
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.FullLabelTimeCount

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open Finset MeasureTheory Set
open scoped Classical ENNReal

/-- In one fine time bin, B contacted affine entries give only O(K²B)
scalar bins. This counts the entire source set, independently of its law. -/
theorem group_scalar_range_in_time_bin
    {Y I : Type*} [DecidableEq I] (U : Set Y)
    (point : Y → Fin 3 → ℝ) (value : Y → ℝ) (label : Y → I)
    (A : I → Fin 4 → ℝ) (allowed : Finset I) (p : Fin 3 → ℝ)
    (D a K B R : ℝ) (n : ℤ) (hD : 0 ≤ D) (ha : 0 < a)
    (hDa : D ≤ a) (hK : 1 ≤ K) (hB : 0 ≤ B)
    (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K)
    (hA : ∀ i, ∀ j : Fin 3, |A i j.succ| ≤ K)
    (hvalue : ∀ y ∈ U, |value y| ≤ R)
    (htime : ∀ y ∈ U, ⌊point y 0 / a⌋ = n)
    (hZ : ∀ y ∈ U, |point y 1 - referenceZ p (point y 0)| ≤ 2 * D)
    (hY : ∀ y ∈ U, |point y 2 - referenceY p (point y 0)| ≤ 3 * D)
    (hfit : ∀ y ∈ U, |value y - affineBaseEval (A (label y)) (point y)| ≤ K * a)
    (hallowed : (allowed.card : ℝ) ≤ B) (hcover : ∀ y ∈ U, label y ∈ allowed) :
    ∃ F : Finset ℤ, (F.card : ℝ) ≤ 1024 * K ^ 2 * B ∧
      ∀ y ∈ U, ⌊value y / a⌋ ∈ F := by
  have hfinite : ((fun y => ⌊value y / a⌋) '' U).Finite := by
    have hh := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
      (fun y : U => fun _ : Fin 1 => value y) R (fun y _ => hvalue y y.property) ha
    apply (hh.image (fun q => q 0)).subset
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(fun _ : Fin 1 => ⌊value y / a⌋), ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  let F := hfinite.toFinset
  have hw (z : F) : ∃ y ∈ U, ⌊value y / a⌋ = (z : ℤ) := hfinite.mem_toFinset.mp z.property
  let rep : F → Y := fun z => Classical.choose (hw z)
  have hrep (z : F) : rep z ∈ U ∧ ⌊value (rep z) / a⌋ = (z : ℤ) :=
    Classical.choose_spec (hw z)
  have hlabels : ((Finset.univ.image (fun z : F => label (rep z))).card : ℝ) ≤ B := by
    apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hallowed
    rintro _ hz
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hz
    exact hcover _ (hrep z).1
  have hbins := Submission.Obl.k4_finite_row_graph_assembly.card_image_le_of_fiber_images
    (Finset.univ : Finset F) (fun z => label (rep z)) (fun z => ⌊value (rep z) / a⌋)
    (C := 1024 * K ^ 2) (by
      intro i hi
      apply group_scalar_bins_per_affine_entry
        (Finset.univ.filter (fun z : F => label (rep z) = i))
        (fun z => point (rep z)) (fun z => value (rep z)) (A i) p D a K n
        hD ha hDa hK hp₀ hp₂ (hA i)
      · exact fun z _ => htime _ (hrep z).1
      · exact fun z _ => hZ _ (hrep z).1
      · exact fun z _ => hY _ (hrep z).1
      · intro z hz
        have hh := hfit _ (hrep z).1
        rwa [(Finset.mem_filter.mp hz).2] at hh)
  have heq : (Finset.univ.image (fun z : F => ⌊value (rep z) / a⌋)) = F := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
      rw [(hrep w).2]
      exact w.property
    · intro hz
      exact Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, (hrep ⟨z, hz⟩).2⟩
  rw [heq] at hbins
  refine ⟨F, ?_, ?_⟩
  · exact hbins.trans ((mul_le_mul_of_nonneg_right hlabels (by positivity)).trans_eq (mul_comm _ _))
  · intro y hy
    exact hfinite.mem_toFinset.mpr ⟨y, hy, rfl⟩

/-- Original full witnesses bound scalar support in every individual fine
time bin, with no reciprocal-time-bin factor. -/
theorem original_full_label_group_scalar_bins
    {Y I : Type*} [MeasurableSpace Y] [Fintype I] [DecidableEq I]
    (μ₀ : Measure Y) [IsFiniteMeasure μ₀]
    (U : Set Y) (point : Y → Fin 3 → ℝ) (value frozenValue : Y → ℝ) (label : Y → I)
    (hpointm : Measurable point) (hfrozenm : Measurable frozenValue)
    (witness : I → Set Y) (c : I → Fin 5 → ℝ) (A : I → Fin 4 → ℝ)
    (block : I → ℤ) (p : Fin 3 → ℝ) (h K D a d R δ C : ℝ) (n : ℤ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hK : 3 ≤ K) (ha : 0 < a)
    (hah : a ≤ h) (hD : 0 ≤ D) (hDa : D ≤ a) (hDcontact : 3 * D ≤ K * h ^ 2)
    (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hδh2 : δ ≤ h ^ 2) (hδ1 : 3 * δ ≤ 1)
    (hm : ∀ i, |((block i : ℝ) + 1 / 2) * h| ≤ 1)
    (hdisj : ∀ i j, i ≠ j → block i = block j → Disjoint (witness i) (witness j))
    (hmeas : ∀ i, MeasurableSet (witness i))
    (hfloor : ∀ i, ENNReal.ofReal (h ^ 4 * a ^ d / K) ≤ μ₀ (witness i))
    (hfrozen : ∀ i, ∀ y ∈ witness i, |frozenValue y| ≤ K)
    (hcap : ∀ (j : Fin 3 → ℤ) (n : ℤ),
      μ₀ {y | baseGridCode δ (point y) = j ∧ ⌊frozenValue y⌋ = n} ≤
        ENNReal.ofReal (C * δ ^ 3))
    (hpoint : ∀ i, ∀ y ∈ witness i,
      point y ∈ horizontalTrueBox (c i) (((block i : ℝ) + 1 / 2) * h) h K)
    (hc : ∀ i, |c i 1| ≤ K)
    (hcenter : ∀ i, |c i 3 + c i 0 + (((block i : ℝ) + 1 / 2) * h) * c i 1| ≤ K * h)
    (htilt : ∀ i, |c i 4 - (((block i : ℝ) + 1 / 2) * h)| ≤ K * h)
    (hA : ∀ i, ∀ j : Fin 3, |A i j.succ| ≤ K)
    (hvalue : ∀ y ∈ U, |value y| ≤ R)
    (htime : ∀ y ∈ U, ⌊point y 0 / a⌋ = n)
    (hZ : ∀ y ∈ U, |point y 1 - referenceZ p (point y 0)| ≤ 2 * D)
    (hY : ∀ y ∈ U, |point y 2 - referenceY p (point y 0)| ≤ 3 * D)
    (hcurrent : ∀ y ∈ U,
      point y ∈ horizontalTrueBox (c (label y)) (((block (label y) : ℝ) + 1 / 2) * h) h K)
    (hfit : ∀ y ∈ U, |value y - affineBaseEval (A (label y)) (point y)| ≤ K * a) :
    ∃ F : Finset ℤ, (F.card : ℝ) ≤ 347892350976 * C * K ^ 9 / a ^ d ∧
      ∀ y ∈ U, ⌊value y / a⌋ ∈ F := by
  have hK1 : 1 ≤ K := by linarith
  let allowed : Finset I := Finset.univ.filter (fun i => ∃ y ∈ U, label y = i)
  have hallowed : (allowed.card : ℝ) ≤ 339738624 * C * K ^ 7 / a ^ d := by
    apply full_true_labels_in_fine_time_bin μ₀ point frozenValue hpointm hfrozenm allowed witness c block p
      h K (h ^ 2) a d δ C n hh hh1 hK1 ha hah le_rfl hp₀ hp₂ hδ hC hδh2 hδ1
      (fun i _ => hm i) (fun i _ j _ hij hblock => hdisj i j hij hblock)
      (fun i _ => hmeas i) (fun i _ => hfloor i) (fun i _ y hy => hfrozen i y hy)
      hcap (fun i _ y hy => hpoint i y hy) (fun i _ => hc i)
      (fun i _ => hcenter i) (fun i _ => htilt i)
    intro i hi
    obtain ⟨y, hy, hlabel⟩ := (Finset.mem_filter.mp hi).2
    refine ⟨point y, ?_, (hZ y hy).trans (by linarith), (hY y hy).trans hDcontact, htime y hy⟩
    simpa only [hlabel] using hcurrent y hy
  obtain ⟨F, hF, hcover⟩ := group_scalar_range_in_time_bin U point value label A allowed p
    D a K (339738624 * C * K ^ 7 / a ^ d) R n hD ha hDa hK1 (by positivity)
    hp₀ hp₂ hA hvalue htime hZ hY hfit hallowed (by
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hy, rfl⟩)
  refine ⟨F, hF.trans_eq ?_, hcover⟩
  ring

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
