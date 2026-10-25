/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, FullLabelSpacetimeCover.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.FullLabelTimeCount
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.GroupScalarSupport
/-! Adapted from this LOT tree, obligation o107, session x0353,
`Submission/Obl/k4_finite_narrowness_path_improvement/HorizontalJointSpacetimeCover.lean`
(commit 2d33b59a). -/


/-! Small scalar spacetime support from original whole-domain witnesses and
finite joint caps. The frozen hidden coordinate may differ from the current
scalar residual. No global base-density ceiling is assumed. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal Classical

theorem original_full_label_group_spacetime_cover
    {Y I : Type*} [MeasurableSpace Y] [Fintype I] [DecidableEq I]
    (μ₀ : Measure Y) [IsFiniteMeasure μ₀] (μ : Measure Y)
    (U : Set Y) (hU : MeasurableSet U) (hfull : μ Uᶜ = 0)
    (point : Y → Fin 3 → ℝ) (value frozenValue : Y → ℝ) (label : Y → I)
    (hpointm : Measurable point) (hvaluem : Measurable value) (hfrozenm : Measurable frozenValue)
    (witness : I → Set Y) (c : I → Fin 5 → ℝ) (A : I → Fin 4 → ℝ)
    (block : I → ℤ) (p : Fin 3 → ℝ) (h K D a d R δ C : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hK : 3 ≤ K) (ha : 0 < a) (ha1 : a ≤ 1)
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
    (hunit : ∀ y ∈ U, point y 0 ∈ Set.Icc (0 : ℝ) 1)
    (hvalue : ∀ y ∈ U, |value y| ≤ R)
    (hZ : ∀ y ∈ U, |point y 1 - referenceZ p (point y 0)| ≤ 2 * D)
    (hY : ∀ y ∈ U, |point y 2 - referenceY p (point y 0)| ≤ 3 * D)
    (hcurrent : ∀ y ∈ U,
      point y ∈ horizontalTrueBox (c (label y)) (((block (label y) : ℝ) + 1 / 2) * h) h K)
    (hfit : ∀ y ∈ U, |value y - affineBaseEval (A (label y)) (point y)| ≤ K * a) :
    ∃ F : Finset (ℤ × ℤ), (F.card : ℝ) ≤ 33397665693696 * C * K ^ 9 / (a * a ^ d) ∧
      ∀ᵐ y ∂μ, (⌊point y 0 / a⌋, ⌊value y / a⌋) ∈ F := by
  have hK1 : 1 ≤ K := by linarith
  let allowed : ℤ → Finset I := fun n => Finset.univ.filter (fun i =>
    ∃ y ∈ U, label y = i ∧ ⌊point y 0 / a⌋ = n)
  have hallowed (n : ℤ) : ((allowed n).card : ℝ) ≤ 339738624 * C * K ^ 7 / a ^ d := by
    apply full_true_labels_in_fine_time_bin μ₀ point frozenValue hpointm hfrozenm (allowed n) witness c block p
      h K (h ^ 2) a d δ C n hh hh1 hK1 ha hah le_rfl hp₀ hp₂ hδ hC hδh2 hδ1
    · exact fun i _ => hm i
    · exact fun i _ j _ hij hblock => hdisj i j hij hblock
    · exact fun i _ => hmeas i
    · exact fun i _ => hfloor i
    · exact fun i _ y hy => hfrozen i y hy
    · exact hcap
    · exact fun i _ y hy => hpoint i y hy
    · exact fun i _ => hc i
    · exact fun i _ => hcenter i
    · exact fun i _ => htilt i
    · intro i hi
      obtain ⟨y, hy, hlabel, htime⟩ := (Finset.mem_filter.mp hi).2
      refine ⟨point y, ?_, ?_, ?_, htime⟩
      · simpa only [hlabel] using hcurrent y hy
      · exact (hZ y hy).trans (by linarith)
      · exact (hY y hy).trans hDcontact
  obtain ⟨F, hF, hsupport⟩ := original_group_scalar_support_cover μ U hU hfull point value label
    hpointm hvaluem A allowed p D a K (339738624 * C * K ^ 7 / a ^ d) R hD ha ha1 hDa hK1
    (by positivity) hp₀ hp₂ hA hunit hvalue hZ hY hfit hallowed (by
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hy, rfl, rfl⟩)
  refine ⟨F, hF.trans_eq ?_, hsupport⟩
  ring

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
