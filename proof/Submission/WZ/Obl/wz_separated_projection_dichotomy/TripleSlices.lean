-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.TripleSlices.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleRefinement
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleFibers

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open scoped BigOperators

noncomputable def secondFiber (G : Finset Plane) (H : Finset Triple) (a b : Plane) : Finset Plane := by
  classical
  exact G.filter (fun x => (a, x, b) ∈ H)

theorem secondFiber_card {F G U : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (a b : Plane) :
    (secondFiber G H a b).card = (H.filter (fun q => q.1 = a ∧ q.2.2 = b)).card := by
  classical
  have himg : H.filter (fun q => q.1 = a ∧ q.2.2 = b) =
      (secondFiber G H a b).image (fun x => (a, x, b)) := by
    ext ⟨v, x, y⟩
    simp only [Finset.mem_filter, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨hp, rfl, rfl⟩
      have hG := (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).1
      exact ⟨x, Finset.mem_filter.mpr ⟨hG, hp⟩, rfl, rfl, rfl⟩
    · rintro ⟨z, hz, rfl, rfl, rfl⟩
      exact ⟨(Finset.mem_filter.mp hz).2, rfl, rfl⟩
  rw [himg, Finset.card_image_of_injective]
  intro x y hxy
  exact congrArg (fun p : Triple => p.2.1) hxy

theorem TripleUniform.secondFiber_dense {d : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) (hH : H ⊆ F ×ˢ (G ×ˢ U))
    {a x b : Plane} (hp : (a, x, b) ∈ H) :
    d * (G.card : ℝ) ≤ ((secondFiber G H a b).card : ℝ) := by
  rw [secondFiber_card hH]
  exact h.fiber_second (a, x, b) hp

theorem sum_tripleFiber_row {F G U : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (b : Plane) :
    ∑ x : G, ((tripleFiber F H x b).card : ℝ) =
      ((H.filter (fun p => p.2.2 = b)).card : ℝ) := by
  classical
  let H' := H.filter (fun p => p.2.2 = b)
  have hsub : H' ⊆ F ×ˢ (G ×ˢ {b}) := by
    intro p hp
    obtain ⟨hpH, hpb⟩ := Finset.mem_filter.mp hp
    have hprod := Finset.mem_product.mp (hH hpH)
    have hprod' := Finset.mem_product.mp hprod.2
    exact Finset.mem_product.mpr ⟨hprod.1, Finset.mem_product.mpr ⟨hprod'.1, Finset.mem_singleton.mpr hpb⟩⟩
  have heq : ∀ x, tripleFiber F H' x b = tripleFiber F H x b := by
    intro x
    ext a
    simp only [tripleFiber, H', Finset.mem_filter, and_true]
  have hsum := sum_tripleFiber_card_real hsub
  simp only [Finset.sum_singleton, heq] at hsum
  exact (Finset.sum_coe_sort G (fun x => ((tripleFiber F H x b).card : ℝ))).trans hsum

theorem TripleUniform.third_row_dense {d : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) (hH : H ⊆ F ×ˢ (G ×ˢ U))
    {a x b : Plane} (hp : (a, x, b) ∈ H) :
    d * (G.card : ℝ) * (F.card : ℝ) ≤ ∑ x : G, ((tripleFiber F H x b).card : ℝ) := by
  rw [sum_tripleFiber_row hH]
  convert h.row_third (a, x, b) hp using 1 <;> ring

end WangZahlLot.Obl.wz_separated_projection_dichotomy
