/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/PairLists.lean.
   This file retains the source's own provenance comments below. -/
import Mathlib

/-!
Analytical candidate/deep-label pairs are known through the deeper original
label and the finite candidate family over its ancestor. Their multiplicity
is used only in the angular discard estimate; output labels use the smaller
parameter/midpoint code lists.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

noncomputable section

def analyticalPairList {A D P : Type*} [Fintype A]
    (parent : A → P) (ancestor : D → P) (S : Finset D) : Finset (A × D) := by
  classical
  exact S.biUnion fun d =>
    (Finset.univ.filter (fun a => parent a = ancestor d)).image (fun a => (a, d))

theorem mem_analyticalPairList {A D P : Type*} [Fintype A]
    (parent : A → P) (ancestor : D → P) (S : Finset D) (a : A) (d : D) :
    (a, d) ∈ analyticalPairList parent ancestor S ↔ d ∈ S ∧ parent a = ancestor d := by
  classical
  simp [analyticalPairList, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]

open Classical in
/-- The original known-list budget is multiplied only by the per-ancestor
candidate multiplicity, without charging the total number of old charts. -/
theorem card_analyticalPairList_le {A D P : Type*} [Fintype A]
    (parent : A → P) (ancestor : D → P) (S : Finset D) {K R : ℝ}
    (hS : (S.card : ℝ) ≤ K) (hR : 0 ≤ R)
    (hfiber : ∀ d ∈ S,
      ((Finset.univ.filter (fun a => parent a = ancestor d)).card : ℝ) ≤ R) :
    ((analyticalPairList parent ancestor S).card : ℝ) ≤ K * R := by
  classical
  have hcount : (analyticalPairList parent ancestor S).card ≤
      ∑ d ∈ S, (Finset.univ.filter (fun a => parent a = ancestor d)).card := by
    unfold analyticalPairList
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro d _
    exact Finset.card_image_le
      (s := Finset.univ.filter (fun a => parent a = ancestor d)) (f := fun a : A => (a, d))
  calc
    _ ≤ ∑ d ∈ S, ((Finset.univ.filter (fun a => parent a = ancestor d)).card : ℝ) := by
      exact_mod_cast hcount
    _ ≤ ∑ _d ∈ S, R := Finset.sum_le_sum hfiber
    _ = (S.card : ℝ) * R := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hS hR

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
