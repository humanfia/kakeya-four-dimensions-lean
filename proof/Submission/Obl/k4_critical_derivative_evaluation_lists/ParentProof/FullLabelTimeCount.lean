/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, FullLabelTimeCount.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.FullLabelCount
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.TrueTimeBlockCount
/-! Adapted from this LOT tree, obligation o107, session x0353,
`Submission/Obl/k4_finite_narrowness_path_improvement/TrueLabelJointTimeCover.lean`
(commit 2d33b59a). -/


/-! Count labels in each fine time bin using only frozen witnesses and
one finite-mesh joint cap, including closed old time-block overlaps. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal Classical

theorem full_true_labels_in_fine_time_bin
    {Y I : Type*} [MeasurableSpace Y] [DecidableEq I]
    (μ : Measure Y) [IsFiniteMeasure μ] (point : Y → Fin 3 → ℝ) (value : Y → ℝ)
    (_hpointm : Measurable point) (_hvaluem : Measurable value)
    (S : Finset I) (witness : I → Set Y) (c : I → Fin 5 → ℝ) (block : I → ℤ)
    (p : Fin 3 → ℝ) (h K D a d δ C : ℝ) (n : ℤ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hK : 1 ≤ K) (ha : 0 < a) (hah : a ≤ h)
    (hD : D ≤ h ^ 2) (hp₀ : |p 0| ≤ K) (hv : |p 2| ≤ K)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hδh2 : δ ≤ h ^ 2) (hδ1 : 3 * δ ≤ 1)
    (hm : ∀ i ∈ S, |((block i : ℝ) + 1 / 2) * h| ≤ 1)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → block i = block j → Disjoint (witness i) (witness j))
    (hmeas : ∀ i ∈ S, MeasurableSet (witness i))
    (hfloor : ∀ i ∈ S, ENNReal.ofReal (h ^ 4 * a ^ d / K) ≤ μ (witness i))
    (hvalue : ∀ i ∈ S, ∀ y ∈ witness i, |value y| ≤ K)
    (hcap : ∀ (j : Fin 3 → ℤ) (n : ℤ),
      μ {y | baseGridCode δ (point y) = j ∧ ⌊value y⌋ = n} ≤
        ENNReal.ofReal (C * δ ^ 3))
    (hpoint : ∀ i ∈ S, ∀ y ∈ witness i,
      point y ∈ horizontalTrueBox (c i) (((block i : ℝ) + 1 / 2) * h) h K)
    (hc : ∀ i ∈ S, |c i 1| ≤ K)
    (hcenter : ∀ i ∈ S, |c i 3 + c i 0 + (((block i : ℝ) + 1 / 2) * h) * c i 1| ≤ K * h)
    (htilt : ∀ i ∈ S, |c i 4 - (((block i : ℝ) + 1 / 2) * h)| ≤ K * h)
    (hcontact : ∀ i ∈ S, ∃ q ∈ horizontalTrueBox (c i) (((block i : ℝ) + 1 / 2) * h) h K,
      |q 1 - referenceZ p (q 0)| ≤ K * D ∧ |q 2 - referenceY p (q 0)| ≤ K * D ∧ ⌊q 0 / a⌋ = n) :
    (S.card : ℝ) ≤ 339738624 * C * K ^ 7 / a ^ d := by
  let q : I → Fin 3 → ℝ := fun i => if hi : i ∈ S then Classical.choose (hcontact i hi) else 0
  have hq (i : I) (hi : i ∈ S) :
      q i ∈ horizontalTrueBox (c i) (((block i : ℝ) + 1 / 2) * h) h K ∧
      |q i 1 - referenceZ p (q i 0)| ≤ K * D ∧
      |q i 2 - referenceY p (q i 0)| ≤ K * D ∧ ⌊q i 0 / a⌋ = n := by
    dsimp only [q]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hcontact i hi)
  have hcount (k : ℤ) : ((S.filter (fun i => block i = k)).card : ℝ) ≤ 56623104 * C * K ^ 7 / a ^ d := by
    by_cases hne : (S.filter (fun i => block i = k)).Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    obtain ⟨i₀, hi₀⟩ := hne
    have hmid : |((k : ℝ) + 1 / 2) * h| ≤ 1 := by
      simpa only [(Finset.mem_filter.mp hi₀).2] using hm i₀ (Finset.mem_filter.mp hi₀).1
    apply full_true_label_contact_count μ point value (S.filter (fun i => block i = k))
      witness c p (((k : ℝ) + 1 / 2) * h) h K D a d δ C hh hh1 hK ha hδ hC hδh2 hδ1 hD hmid hp₀ hv
    · intro i hi j hj hij
      exact hdisj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    · exact fun i hi => hmeas i (Finset.mem_filter.mp hi).1
    · exact fun i hi => hfloor i (Finset.mem_filter.mp hi).1
    · exact fun i hi y hy => hvalue i (Finset.mem_filter.mp hi).1 y hy
    · exact hcap
    · intro i hi y hy
      simpa only [(Finset.mem_filter.mp hi).2] using hpoint i (Finset.mem_filter.mp hi).1 y hy
    · exact fun i hi => hc i (Finset.mem_filter.mp hi).1
    · intro i hi
      simpa only [(Finset.mem_filter.mp hi).2] using hcenter i (Finset.mem_filter.mp hi).1
    · intro i hi
      simpa only [(Finset.mem_filter.mp hi).2] using htilt i (Finset.mem_filter.mp hi).1
    · intro i hi
      refine ⟨q i, ?_, (hq i (Finset.mem_filter.mp hi).1).2.1,
        (hq i (Finset.mem_filter.mp hi).1).2.2.1⟩
      simpa only [(Finset.mem_filter.mp hi).2] using (hq i (Finset.mem_filter.mp hi).1).1
  have htotal := true_labels_across_fine_time_bin S block (fun i => q i 0) h a
    (56623104 * C * K ^ 7 / a ^ d) n hh ha hah (by positivity) (by
      intro i hi
      have ht := abs_le.mp (hq i hi).1.1
      constructor <;> nlinarith only [ht.1, ht.2])
    (fun i hi => (hq i hi).2.2.2) hcount
  convert htotal using 1
  ring

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
