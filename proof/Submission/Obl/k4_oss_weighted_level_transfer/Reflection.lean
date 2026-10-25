import Submission.Obl.k4_oss_weighted_level_transfer.AtomicLevels

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace Submission.Obl.k4_oss_weighted_level_transfer

attribute [local instance] Classical.propDecidable
attribute [local instance] counting_finite atomic_finite ofReal_dirac_finite

noncomputable def reflectSet (S : Finset ℝ) : Finset ℝ := S.image (fun x => -2 * x)

lemma reflect_injective : Function.Injective (fun x : ℝ => -2 * x) := by
  intro x y h
  linarith

lemma reflectSet_card (S : Finset ℝ) : (reflectSet S).card = S.card :=
  Finset.card_image_of_injective S reflect_injective

lemma reflect_dist (x y : ℝ) : dist (-2 * x) (-2 * y) = 2 * dist x y := by
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
  norm_num

lemma reflectSet_separated {S : Finset ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) :
    ∀ x ∈ reflectSet S, ∀ y ∈ reflectSet S, x ≠ y → δ ≤ dist x y := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := by intro h; exact hxy (congrArg (fun x : ℝ => -2 * x) h)
  rw [reflect_dist]
  linarith [hsep a ha b hb hab]

lemma reflectSet_local_card (S : Finset ℝ) (x u : ℝ) :
    ((reflectSet S).filter (fun y => dist y x ≤ u)).card ≤
      (S.filter (fun y => dist y (-x / 2) ≤ u)).card := by
  have hsub : (reflectSet S).filter (fun y => dist y x ≤ u) ⊆
      (S.filter (fun y => dist y (-x / 2) ≤ u)).image (fun y => -2 * y) := by
    intro y hy
    obtain ⟨hyS, hyu⟩ := Finset.mem_filter.mp hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hyS
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_filter.mpr ⟨hz, ?_⟩, rfl⟩
    have heq : dist (-2 * z) x = 2 * dist z (-x / 2) := by
      rw [Real.dist_eq, Real.dist_eq,
        show -2 * z - x = -2 * (z - -x / 2) by ring, abs_mul]
      norm_num
    rw [heq] at hyu
    have hn : 0 ≤ dist z (-x / 2) := dist_nonneg
    linarith
  exact (Finset.card_le_card hsub).trans_eq
    (Finset.card_image_of_injective _ reflect_injective)

lemma reflectSet_frostman {S : Finset ℝ} {δ C b : ℝ}
    (hcap : ∀ x u : ℝ, δ ≤ u → ((S.filter (fun y => dist y x ≤ u)).card : ℝ) ≤
      C * u ^ b * S.card) :
    ∀ x u : ℝ, δ ≤ u → (((reflectSet S).filter (fun y => dist y x ≤ u)).card : ℝ) ≤
      C * u ^ b * (reflectSet S).card := by
  intro x u hδu
  rw [reflectSet_card]
  exact (show (((reflectSet S).filter (fun y => dist y x ≤ u)).card : ℝ) ≤
      ((S.filter (fun y => dist y (-x / 2) ≤ u)).card : ℝ) by
    exact_mod_cast reflectSet_local_card S x u).trans (hcap (-x / 2) u hδu)

lemma map_reflect_counting (S : Finset ℝ) :
    (counting S).map (fun x : ℝ => -2 * x) = counting (reflectSet S) :=
  map_counting S _ (by fun_prop) reflect_injective

lemma map_reflect_level_sum {I : Type*} [Fintype I] (A : I → Finset ℝ) (w : I → ℝ) :
    (∑ i, ENNReal.ofReal (w i) • counting (A i)).map (fun x : ℝ => -2 * x) =
      ∑ i, ENNReal.ofReal (w i) • counting (reflectSet (A i)) := by
  rw [map_finset _ _ _ (by fun_prop)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.map_smul _ (by fun_prop), map_reflect_counting]

end Submission.Obl.k4_oss_weighted_level_transfer
