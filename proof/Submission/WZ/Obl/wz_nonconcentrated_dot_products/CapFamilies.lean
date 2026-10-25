-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.CapFamilies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.CapIntersection

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Common points covered by radial cap families are either near the joining
line or in a small transverse intersection. -/
theorem radial_cap_families_count {J : Type*} [Fintype J] {f : J → Plane}
    (R R' : J → Prop) (D D' : Finset Plane) {b b' : Plane} {δ C q s r B L : ℝ}
    (hF : IndexedFrostman δ C f) (hC : 0 ≤ C) (hq : 0 < q) (hs : 0 < s)
    (hr : 0 ≤ r) (hsmall : r ≤ q * s / 256) (hδrad : δ ≤ 4096 * r / (q * s))
    (hsep : q ≤ ‖b' - b‖)
    (hpoints : ∀ j, b ≠ f j ∧ b' ≠ f j ∧ ‖b - f j‖ ≤ 8 ∧ ‖b' - f j‖ ≤ 8)
    (hunit : ∀ u ∈ D, ‖u‖ = 1) (hunit' : ∀ v ∈ D', ‖v‖ = 1)
    (hD : (D.card : ℝ) ≤ L) (hD' : (D'.card : ℝ) ≤ L)
    (hcover : ∀ j, R j → ∃ u ∈ D, dist (radialDirection b (f j)) u ≤ r)
    (hcover' : ∀ j, R' j → ∃ v ∈ D', dist (radialDirection b' (f j)) v ≤ r)
    (hline : ((Finset.univ.filter (fun j =>
      |area (f j - b) (b' - b)| < s * ‖b' - b‖)).card : ℝ) ≤ B * (Fintype.card J : ℝ)) :
    ((Finset.univ.filter (fun j => R j ∧ R' j)).card : ℝ) ≤
      (B + L ^ 2 * C * (4096 * r / (q * s))) * (Fintype.card J : ℝ) := by
  classical
  let A : Finset J := Finset.univ.filter (fun j => R j ∧ R' j)
  let E : Finset J := Finset.univ.filter (fun j =>
    |area (f j - b) (b' - b)| < s * ‖b' - b‖)
  let T (p : Plane × Plane) : Finset J := Finset.univ.filter (fun j =>
    s * ‖b' - b‖ ≤ |area (f j - b) (b' - b)| ∧
    dist (radialDirection b (f j)) p.1 ≤ r ∧ dist (radialDirection b' (f j)) p.2 ≤ r)
  have hsub : A ⊆ E ∪ (D ×ˢ D').biUnion T := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    by_cases he : |area (f j - b) (b' - b)| < s * ‖b' - b‖
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    · obtain ⟨u, hu, hju⟩ := hcover j hj'.1
      obtain ⟨v, hv, hjv⟩ := hcover' j hj'.2
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt he, hju, hjv⟩⟩
  have hcap (p : Plane × Plane) (hp : p ∈ D ×ˢ D') :
      ((T p).card : ℝ) ≤ C * (4096 * r / (q * s)) * (Fintype.card J : ℝ) :=
    radial_cap_intersection_count hF hC hq hs hr hsmall hδrad hsep
      (hunit p.1 (Finset.mem_product.mp hp).1) (hunit' p.2 (Finset.mem_product.mp hp).2) hpoints
  have hcount : (A.card : ℝ) ≤ (E.card : ℝ) + ∑ p ∈ D ×ˢ D', ((T p).card : ℝ) := by
    have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h' := Finset.card_biUnion_le (s := D ×ˢ D') (t := T)
    exact_mod_cast h.trans (Nat.add_le_add_left h' E.card)
  have hL : 0 ≤ L := (Nat.cast_nonneg D.card).trans hD
  have hprod : ((D ×ˢ D').card : ℝ) ≤ L ^ 2 := by
    rw [Finset.card_product, Nat.cast_mul, pow_two]
    exact mul_le_mul hD hD' (Nat.cast_nonneg _) hL
  calc (A.card : ℝ) ≤ (E.card : ℝ) + ∑ p ∈ D ×ˢ D', ((T p).card : ℝ) := hcount
    _ ≤ B * (Fintype.card J : ℝ) +
        ∑ _p ∈ D ×ˢ D', C * (4096 * r / (q * s)) * (Fintype.card J : ℝ) :=
      add_le_add hline (Finset.sum_le_sum hcap)
    _ = B * (Fintype.card J : ℝ) + ((D ×ˢ D').card : ℝ) *
        (C * (4096 * r / (q * s)) * (Fintype.card J : ℝ)) := by simp
    _ ≤ B * (Fintype.card J : ℝ) + L ^ 2 *
        (C * (4096 * r / (q * s)) * (Fintype.card J : ℝ)) := by gcongr
    _ = _ := by ring

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
