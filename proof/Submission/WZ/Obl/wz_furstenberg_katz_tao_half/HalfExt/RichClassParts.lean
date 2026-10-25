-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.RichClassParts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Classes
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.GoodPoints
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.ClassSelect
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.TwoEndsPrune
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.ClassPairs
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.Maximal
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CotFrame

/-!
# Parts of the rich class selection (`half_rich_class`)

* `far_good_pairs`: if every point with fewer than `τ = #Far / (4 #P)` far pairs is called bad,
  at least half of the far same-class pairs have both points good.
* `class_pin_labels_le`: a pin carries at most `2 r ^ (-η)` labels of one class.
* `class_pairs_le_sq`: the good far pairs of one class number at most `(2 r ^ (-η) #H) ^ 2`,
  `H` the good pins of the class.
* `pin_pairs_le_class_pairs`: pairs of pins of a class with along-coordinates `d` apart give
  same-class label pairs at distance `< 20 d` (pins within `9 r` of the class line).
* `along_separated_prune`: a set of pins near a line contains an along-`r`-separated subset
  `A` with `#H ≤ 19 r ^ (-η) #A`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open SP

/-- Far same-class pairs. -/
noncomputable def farPairs (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (d₀ : ℝ) :
    Finset ((E2 × E2) × (E2 × E2)) :=
  (sameClass D cls).filter (fun qq => d₀ ≤ dist qq.1.1 qq.2.1)

theorem farCount_eq (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (d₀ : ℝ) (p : E2) :
    farCount D cls d₀ p = ((farPairs D cls d₀).filter (fun qq => qq.1.1 = p)).card := by
  classical
  unfold farCount farPairs sameClass
  congr 1
  ext qq
  simp only [Finset.mem_filter]
  tauto

/-- At least half of the far pairs have both points good. -/
theorem far_good_pairs (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (d₀ : ℝ)
    (P : Finset E2) (hDP : ∀ q ∈ D, q.1 ∈ P) (hP : P.Nonempty) :
    let τ := ((farPairs D cls d₀).card : ℝ) / (4 * (P.card : ℝ))
    let Good := P.filter (fun p => τ ≤ (farCount D cls d₀ p : ℝ))
    ((farPairs D cls d₀).card : ℝ) / 2 ≤
      (((farPairs D cls d₀).filter (fun qq => qq.1.1 ∈ Good ∧ qq.2.1 ∈ Good)).card : ℝ) := by
  classical
  intro τ Good
  set F := farPairs D cls d₀ with hF
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hP
  have hmemF : ∀ qq ∈ F, qq.1 ∈ D ∧ qq.2 ∈ D ∧ cls qq.1 = cls qq.2 ∧ d₀ ≤ dist qq.1.1 qq.2.1 := by
    intro qq hqq
    rw [hF, farPairs, sameClass, Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hqq
    exact ⟨hqq.1.1.1, hqq.1.1.2, hqq.1.2, hqq.2⟩
  -- pairs whose first point is bad
  have hbad1 : ((F.filter (fun qq => qq.1.1 ∉ Good)).card : ℝ) ≤ (F.card : ℝ) / 4 := by
    have hsplit : (F.filter (fun qq => qq.1.1 ∉ Good)).card =
        ∑ p ∈ P.filter (fun p => p ∉ Good), (F.filter (fun qq => qq.1.1 = p)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun qq => qq.1.1)
        (t := P.filter (fun p => p ∉ Good))]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.filter_filter]
        congr 1
        ext qq
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          refine ⟨h1, ?_, h3⟩
          rw [h3]; exact (Finset.mem_filter.mp hp).2
      · intro qq hqq
        have hqq' := Finset.mem_filter.mp hqq
        exact Finset.mem_filter.mpr ⟨hDP _ (hmemF _ hqq'.1).1, hqq'.2⟩
    have hle : ∀ p ∈ P.filter (fun p => p ∉ Good),
        ((F.filter (fun qq => qq.1.1 = p)).card : ℝ) ≤ τ := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hng : ¬ (τ ≤ (farCount D cls d₀ p : ℝ)) := by
        intro h
        exact hp'.2 (Finset.mem_filter.mpr ⟨hp'.1, h⟩)
      push Not at hng
      rw [farCount_eq] at hng
      exact hng.le
    have h1 : ((F.filter (fun qq => qq.1.1 ∉ Good)).card : ℝ) ≤
        ∑ p ∈ P.filter (fun p => p ∉ Good), τ := by
      rw [hsplit]; push_cast; exact Finset.sum_le_sum hle
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : ((P.filter (fun p => p ∉ Good)).card : ℝ) ≤ P.card := by
      exact_mod_cast Finset.card_filter_le _ _
    have hτ0 : 0 ≤ τ := by positivity
    calc ((F.filter (fun qq => qq.1.1 ∉ Good)).card : ℝ)
        ≤ ((P.filter (fun p => p ∉ Good)).card : ℝ) * τ := h1
      _ ≤ (P.card : ℝ) * τ := mul_le_mul_of_nonneg_right h2 hτ0
      _ = (F.card : ℝ) / 4 := by
          show (P.card : ℝ) * ((F.card : ℝ) / (4 * (P.card : ℝ))) = _
          field_simp
  -- pairs whose second point is bad: swap
  have hbad2 : ((F.filter (fun qq => qq.2.1 ∉ Good)).card : ℝ) ≤ (F.card : ℝ) / 4 := by
    have hswap : (F.filter (fun qq => qq.2.1 ∉ Good)) =
        (F.filter (fun qq => qq.1.1 ∉ Good)).image (fun qq => (qq.2, qq.1)) := by
      ext qq
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hq, hb⟩
        refine ⟨(qq.2, qq.1), ⟨?_, hb⟩, rfl⟩
        have h := hmemF _ hq
        rw [hF, farPairs, sameClass, Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨⟨h.2.1, h.1⟩, h.2.2.1.symm⟩, by rw [dist_comm]; exact h.2.2.2⟩
      · rintro ⟨qq', ⟨hq', hb⟩, rfl⟩
        refine ⟨?_, hb⟩
        have h := hmemF _ hq'
        rw [hF, farPairs, sameClass, Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨⟨h.2.1, h.1⟩, h.2.2.1.symm⟩, by rw [dist_comm]; exact h.2.2.2⟩
    rw [hswap]
    have hci : ((((F.filter (fun qq => qq.1.1 ∉ Good)).image (fun qq => (qq.2, qq.1))).card : ℕ) : ℝ) ≤
        ((F.filter (fun qq => qq.1.1 ∉ Good)).card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    exact hci.trans hbad1
  have hcover : F ⊆ F.filter (fun qq => qq.1.1 ∈ Good ∧ qq.2.1 ∈ Good) ∪
      (F.filter (fun qq => qq.1.1 ∉ Good) ∪ F.filter (fun qq => qq.2.1 ∉ Good)) := by
    intro qq hq
    by_cases h1 : qq.1.1 ∈ Good
    · by_cases h2 : qq.2.1 ∈ Good
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq, h1, h2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq, h2⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq, h1⟩))
  set G1 := F.filter (fun qq => qq.1.1 ∈ Good ∧ qq.2.1 ∈ Good) with hG1
  set B1 := F.filter (fun qq => qq.1.1 ∉ Good) with hB1
  set B2 := F.filter (fun qq => qq.2.1 ∉ Good) with hB2
  have hc : (F.card : ℝ) ≤ ((G1 ∪ (B1 ∪ B2)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hcover
  have hu1 : ((G1 ∪ (B1 ∪ B2)).card : ℝ) ≤ (G1.card : ℝ) + ((B1 ∪ B2).card : ℝ) := by
    exact_mod_cast Finset.card_union_le _ _
  have hu2 : ((B1 ∪ B2).card : ℝ) ≤ (B1.card : ℝ) + (B2.card : ℝ) := by
    exact_mod_cast Finset.card_union_le _ _
  linarith

/-- A pin carries at most `2 r ^ (-η)` labels of one class. -/
theorem class_pin_labels_le {r η : ℝ} (hr : 0 < r) {P : Finset E2} {D : Finset (E2 × E2)}
    {cls : E2 × E2 → E2 × E2}
    (hDkt : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ))
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
        (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    {j : E2 × E2} (hju : ‖j.2‖ = 1) {p : E2} (hp : p ∈ P) :
    (((D.filter (fun q => cls q = j ∧ q.1 = p))).card : ℝ) ≤ 2 * r ^ (-η) := by
  classical
  have hmju : ‖-j.2‖ = 1 := by rw [norm_neg, hju]
  have hsub : (D.filter (fun q => cls q = j ∧ q.1 = p)) ⊆
      (((bushOf D p).filter (fun e => dist e j.2 ≤ r)) ∪
        ((bushOf D p).filter (fun e => dist e (-j.2) ≤ r))).image (fun e => (p, e)) := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    refine Finset.mem_image.mpr ⟨q.2, ?_, Prod.ext hq'.2.2.symm rfl⟩
    have hb : q.2 ∈ bushOf D p := by
      rw [mem_bushOf, ← hq'.2.2]; exact hq'.1
    have h := (hgeo q hq'.1).2
    rw [hq'.2.1] at h
    rcases h with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, h.le⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, h.le⟩)
  have h1 := hDkt p hp j.2 hju r le_rfl
  have h2 := hDkt p hp (-j.2) hmju r le_rfl
  rw [div_self hr.ne', Real.one_rpow, mul_one] at h1 h2
  calc ((D.filter (fun q => cls q = j ∧ q.1 = p)).card : ℝ)
      ≤ (((((bushOf D p).filter (fun e => dist e j.2 ≤ r)) ∪
          ((bushOf D p).filter (fun e => dist e (-j.2) ≤ r))).image (fun e => (p, e))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((((bushOf D p).filter (fun e => dist e j.2 ≤ r)) ∪
          ((bushOf D p).filter (fun e => dist e (-j.2) ≤ r))).card : ℝ) := by
        exact_mod_cast Finset.card_image_le
    _ ≤ (((bushOf D p).filter (fun e => dist e j.2 ≤ r)).card : ℝ) +
          (((bushOf D p).filter (fun e => dist e (-j.2) ≤ r)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ 2 * r ^ (-η) := by linarith

/-- Labels of one class at the pins of a set. -/
theorem class_labels_at_le {r η : ℝ} (hr : 0 < r) {P : Finset E2} {D : Finset (E2 × E2)}
    {cls : E2 × E2 → E2 × E2}
    (hDkt : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ))
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
        (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    {j : E2 × E2} (hju : ‖j.2‖ = 1) {H : Finset E2} (hHP : H ⊆ P) :
    (((D.filter (fun q => cls q = j ∧ q.1 ∈ H))).card : ℝ) ≤ 2 * r ^ (-η) * (H.card : ℝ) := by
  classical
  have hsub : D.filter (fun q => cls q = j ∧ q.1 ∈ H) =
      H.biUnion (fun p => D.filter (fun q => cls q = j ∧ q.1 = p)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hq, hc, hp⟩; exact ⟨q.1, hp, hq, hc, rfl⟩
    · rintro ⟨p, hp, hq, hc, rfl⟩; exact ⟨hq, hc, hp⟩
  rw [hsub]
  calc ((H.biUnion (fun p => D.filter (fun q => cls q = j ∧ q.1 = p))).card : ℝ)
      ≤ ∑ p ∈ H, ((D.filter (fun q => cls q = j ∧ q.1 = p)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ p ∈ H, 2 * r ^ (-η) :=
        Finset.sum_le_sum (fun p hp => class_pin_labels_le hr hDkt hgeo hju (hHP hp))
    _ = 2 * r ^ (-η) * (H.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- An along-`r`-separated subset of a set of pins near a line. -/
theorem along_separated_prune {r η : ℝ} (hr : 0 < r) {P : Finset E2}
    (hPkt : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
      ((P.filter (fun p => dist p x ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r))
    {n p₀ : E2} (hn : ‖n‖ = 1) {H : Finset E2} (hHP : H ⊆ P)
    (hnear : ∀ p ∈ H, |acrossCoord n p₀ p| ≤ 9 * r) :
    ∃ A ⊆ H, (∀ p ∈ A, ∀ p' ∈ A, p ≠ p' → r ≤ |alongCoord n p₀ p - alongCoord n p₀ p'|) ∧
      (H.card : ℝ) ≤ 19 * r ^ (-η) * (A.card : ℝ) := by
  classical
  obtain ⟨A, hAH, hApair, hAmax⟩ := exists_maximal_pairwise H
    (fun p p' => r ≤ |alongCoord n p₀ p - alongCoord n p₀ p'|)
  refine ⟨A, hAH, fun p hp p' hp' hne => hApair p hp p' hp' hne, ?_⟩
  -- every point of `H` is near some point of `A`
  have hcov : H ⊆ A.biUnion (fun a => P.filter (fun p => dist p a ≤ 19 * r)) := by
    intro p hp
    have hclose : ∃ a ∈ A, |alongCoord n p₀ p - alongCoord n p₀ a| < r := by
      by_cases hpA : p ∈ A
      · exact ⟨p, hpA, by simp; exact hr⟩
      · obtain ⟨a, ha, hR⟩ := hAmax p hp hpA
        refine ⟨a, ha, ?_⟩
        rcases hR with h | h
        · exact not_le.mp h
        · rw [abs_sub_comm]; exact not_le.mp h
    obtain ⟨a, ha, hpa⟩ := hclose
    refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨hHP hp, ?_⟩⟩
    have ha' := hnear a (hAH ha)
    have hp' := hnear p hp
    have hframe := inner_frame hn (p - a) (p - a)
    rw [real_inner_self_eq_norm_sq] at hframe
    have halong : |inner ℝ (p - a) (perp n)| < r := by rwa [← alongCoord_sub]
    have hacross : |inner ℝ (p - a) n| ≤ 18 * r := by
      rw [← acrossCoord_sub]
      calc |acrossCoord n p₀ p - acrossCoord n p₀ a| ≤ |acrossCoord n p₀ p| + |acrossCoord n p₀ a| :=
            abs_sub _ _
        _ ≤ 18 * r := by linarith
    have hsq : ‖p - a‖ ^ 2 ≤ (19 * r) ^ 2 := by
      rw [hframe]
      have h1 : inner ℝ (p - a) (perp n) ^ 2 ≤ r ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) halong.le 2
      have h2 : inner ℝ (p - a) n ^ 2 ≤ (18 * r) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hacross 2
      nlinarith
    rw [dist_eq_norm]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq
  have hball : ∀ a ∈ A, ((P.filter (fun p => dist p a ≤ 19 * r)).card : ℝ) ≤ 19 * r ^ (-η) := by
    intro a _
    have h := hPkt a (19 * r) (by linarith)
    rw [show 19 * r / r = 19 by field_simp] at h
    linarith
  calc (H.card : ℝ) ≤ ((A.biUnion (fun a => P.filter (fun p => dist p a ≤ 19 * r))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcov
    _ ≤ ∑ a ∈ A, ((P.filter (fun p => dist p a ≤ 19 * r)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ a ∈ A, 19 * r ^ (-η) := Finset.sum_le_sum hball
    _ = 19 * r ^ (-η) * (A.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
