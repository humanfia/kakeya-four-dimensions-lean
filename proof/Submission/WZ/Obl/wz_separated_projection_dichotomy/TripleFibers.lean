-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.TripleFibers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Parameters

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable def tripleFiber (F : Finset Plane) (H : Finset Triple) (b x : Plane) : Finset Plane :=
  F.filter (fun a => (a, b, x) ∈ H)

theorem sum_tripleFiber_card {F G₁ G₂ : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G₁ ×ˢ G₂)) :
    ∑ b ∈ G₁, ∑ x ∈ G₂, (tripleFiber F H b x).card = H.card := by
  classical
  have heq : (F ×ˢ (G₁ ×ˢ G₂)).filter (fun p => p ∈ H) = H := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hp => ⟨hH hp, hp⟩⟩
  calc ∑ b ∈ G₁, ∑ x ∈ G₂, (tripleFiber F H b x).card =
      ∑ b ∈ G₁, ∑ x ∈ G₂, ∑ a ∈ F, if (a, b, x) ∈ H then 1 else 0 := by
        simp only [tripleFiber, Finset.card_eq_sum_ones, Finset.sum_filter]
        congr 1 <;> ext b <;> congr 1 <;> ext x <;> congr 1 <;> ext a <;> simp
    _ = ∑ a ∈ F, ∑ b ∈ G₁, ∑ x ∈ G₂, if (a, b, x) ∈ H then 1 else 0 := by
        simp_rw [Finset.sum_comm (s := G₂) (t := F)]
        rw [Finset.sum_comm]
    _ = ((F ×ˢ (G₁ ×ˢ G₂)).filter (fun p => p ∈ H)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
        congr 1 <;> ext a <;> congr 1 <;> ext b <;> congr 1 <;> ext x <;> simp
    _ = H.card := congrArg Finset.card heq

theorem sum_tripleFiber_card_real {F G₁ G₂ : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G₁ ×ˢ G₂)) :
    ∑ b ∈ G₁, ∑ x ∈ G₂, ((tripleFiber F H b x).card : ℝ) = (H.card : ℝ) := by
  exact_mod_cast sum_tripleFiber_card hH

theorem tripleFiber_dot_subset (F : Finset Plane) (H : Finset Triple) (b x : Plane) :
    (fun a => inner ℝ a (b - x)) '' (↑(tripleFiber F H b x) : Set Plane) ⊆
      DotSet (↑H : Set Triple) := by
  rintro t ⟨a, ha, rfl⟩
  exact ⟨(a, b, x), (Finset.mem_filter.mp ha).2, rfl⟩

end WangZahlLot.Obl.wz_separated_projection_dichotomy
