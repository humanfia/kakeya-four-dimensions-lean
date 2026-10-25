-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.ClassMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0720 Columns/ClassMass.lean (758215d).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.ClassPairs
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Classes

/-!
Class assignments and their incidence mass, without fixing the bush exponent.
Only the bound for angular caps of radius `r` enters the loss in passing from
labels to distinct point--class incidences.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open scoped BigOperators

theorem exists_class_map (D : Finset (E2 × E2)) (r : ℝ) :
    ∃ (J : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2),
      J ⊆ D ∧ (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → StripSep r q q') ∧
      ∀ q ∈ D, cls q ∈ J ∧
        (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q) := by
  classical
  obtain ⟨J, hJD, hsep, hmax⟩ := exists_maximal_pairwise D (StripSep r)
  have hex : ∀ q : E2 × E2, ∃ j : E2 × E2,
      q ∈ D → j ∈ J ∧ (q = j ∨ ¬ StripSep r q j ∨ ¬ StripSep r j q) := by
    intro q
    by_cases hq : q ∈ D
    · by_cases hqJ : q ∈ J
      · exact ⟨q, fun _ => ⟨hqJ, Or.inl rfl⟩⟩
      · obtain ⟨j, hj, hbad⟩ := hmax q hq hqJ
        exact ⟨j, fun _ => ⟨hj, Or.inr hbad⟩⟩
    · exact ⟨q, fun h => (hq h).elim⟩
  choose cls hcls using hex
  exact ⟨J, cls, hJD, hsep, hcls⟩

theorem label_mass_lower (P : Finset E2) (D : Finset (E2 × E2))
    (hDP : ∀ q ∈ D, q.1 ∈ P) {M : ℝ}
    (hM : ∀ p ∈ P, M ≤ ((bushOf D p).card : ℝ)) :
    M * P.card ≤ (D.card : ℝ) := by
  classical
  have hsum : (D.card : ℝ) = ∑ p ∈ P, ((D.filter (fun q => q.1 = p)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) hDP]
    push_cast
    rfl
  rw [hsum]
  calc M * P.card = ∑ _p ∈ P, M := by simp [mul_comm]
    _ ≤ ∑ p ∈ P, ((D.filter (fun q => q.1 = p)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      apply (hM p hp).trans
      unfold bushOf
      exact_mod_cast Finset.card_image_le

theorem pinsOf_subset {D : Finset (E2 × E2)} {P : Finset E2}
    (hDP : ∀ q ∈ D, q.1 ∈ P) (cls : E2 × E2 → E2 × E2) (j : E2 × E2) :
    pinsOf D cls j ⊆ P := by
  intro p hp
  obtain ⟨e, he, _⟩ := mem_pinsOf.mp hp
  exact hDP (p, e) he

/-- At most two radius-`r` angular caps contribute labels at one class and pin. -/
theorem class_pin_mass {D : Finset (E2 × E2)} {P : Finset E2}
    {cls : E2 × E2 → E2 × E2} {r B : ℝ}
    (hgeo : ∀ q ∈ D, dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r)
    (hcap : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter (fun e => dist e u ≤ r)).card : ℝ) ≤ B)
    {j : E2 × E2} (hj : ‖j.2‖ = 1) {p : E2} (hp : p ∈ P) :
    ((D.filter (fun q => cls q = j ∧ q.1 = p)).card : ℝ) ≤ 2 * B := by
  classical
  let A := (bushOf D p).filter (fun e => dist e j.2 ≤ r)
  let A' := (bushOf D p).filter (fun e => dist e (-j.2) ≤ r)
  have hsub : D.filter (fun q => cls q = j ∧ q.1 = p) ⊆
      (A ∪ A').image (fun e => (p, e)) := by
    intro q hq
    obtain ⟨hqD, hqj, hqp⟩ := Finset.mem_filter.mp hq
    have hb : q.2 ∈ bushOf D p := by
      rw [mem_bushOf, ← hqp]
      exact hqD
    have hg := hgeo q hqD
    rw [hqj] at hg
    refine Finset.mem_image.mpr ⟨q.2, ?_, Prod.ext hqp.symm rfl⟩
    rcases hg with hg | hg
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, hg.le⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, hg.le⟩)
  have hc : ((D.filter (fun q => cls q = j ∧ q.1 = p)).card : ℝ) ≤
      (A.card : ℝ) + A'.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans
      (Finset.card_image_le.trans (Finset.card_union_le _ _))
  have h₁ := hcap p hp j.2 hj
  have h₂ := hcap p hp (-j.2) (by simpa using hj)
  change (A.card : ℝ) ≤ B at h₁
  change (A'.card : ℝ) ≤ B at h₂
  linarith

/-- Passing from labels to distinct point--class incidences costs at most `2B`. -/
theorem label_mass_le_class_incidence {D J : Finset (E2 × E2)} {P : Finset E2}
    {cls : E2 × E2 → E2 × E2} {r B : ℝ}
    (hDP : ∀ q ∈ D, q.1 ∈ P) (hcls : ∀ q ∈ D, cls q ∈ J)
    (hJ : ∀ j ∈ J, ‖j.2‖ = 1)
    (hgeo : ∀ q ∈ D, dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r)
    (hcap : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter (fun e => dist e u ≤ r)).card : ℝ) ≤ B) :
    (D.card : ℝ) ≤ 2 * B * ∑ j ∈ J, ((pinsOf D cls j).card : ℝ) := by
  classical
  have hpiece : ∀ j ∈ J, ((D.filter (fun q => cls q = j)).card : ℝ) ≤
      2 * B * (pinsOf D cls j).card := by
    intro j hj
    have hm : ∀ q ∈ D.filter (fun q => cls q = j), q.1 ∈ pinsOf D cls j := by
      intro q hq
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have h := cls_card_le_sum hm (fun _ => 2 * B) (fun p hp => ?_)
    · simpa [mul_comm] using h
    have hpP := pinsOf_subset hDP cls j hp
    have heq : (D.filter (fun q => cls q = j)).filter (fun q => q.1 = p) =
        D.filter (fun q => cls q = j ∧ q.1 = p) := by
      ext q
      simp [and_assoc]
    rw [heq]
    exact class_pin_mass hgeo hcap (hJ j hj) hpP
  have hsum : (D.card : ℝ) = ∑ j ∈ J, ((D.filter (fun q => cls q = j)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := cls) hcls]
    push_cast
    rfl
  rw [hsum, Finset.mul_sum]
  exact Finset.sum_le_sum hpiece

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
