-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactGridPairs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGrid

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- A monotone derivative gives small diameter on either transverse branch. -/
theorem sublevel_dist_le_of_monotone_deriv_same_sign {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) {a b A c x y : ℝ} (hc : 0 < c)
    (hmono : MonotoneOn (deriv f) (Icc a b) ∨ AntitoneOn (deriv f) (Icc a b))
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hfx : |f x| ≤ A) (hfy : |f y| ≤ A)
    (hsign : (c ≤ deriv f x ∧ c ≤ deriv f y) ∨
      (deriv f x ≤ -c ∧ deriv f y ≤ -c)) :
    dist x y ≤ 2 * A / c := by
  have hbound : ∀ u v : ℝ, u ∈ Icc a b → v ∈ Icc a b →
      ((c ≤ deriv f u ∧ c ≤ deriv f v) ∨
        (deriv f u ≤ -c ∧ deriv f v ≤ -c)) →
      ∀ t ∈ Icc u v, c ≤ |deriv f t| := by
    intro u v hu hv huv t ht
    have ht' : t ∈ Icc a b := ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩
    rcases huv with hp | hn
    · apply le_trans (b := deriv f t) _ (le_abs_self _)
      rcases hmono with hm | hm
      · exact hp.1.trans (hm hu ht' ht.1)
      · exact hp.2.trans (hm ht' hv ht.2)
    · apply le_trans (b := -deriv f t) _ (neg_le_abs _)
      rcases hmono with hm | hm
      · have hh := (hm ht' hv ht.2).trans hn.2
        linarith
      · have hh := (hm hu ht' ht.1).trans hn.1
        linarith
  rcases le_total x y with hxy | hyx
  · exact sublevel_dist_le_of_deriv hf hc (hbound x y hx hy hsign)
      ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hfx hfy
  · rw [dist_comm]
    apply sublevel_dist_le_of_deriv hf hc (hbound y x hy hx ?_)
      ⟨le_rfl, hyx⟩ ⟨hyx, le_rfl⟩ hfy hfx
    rcases hsign with hp | hn
    · exact Or.inl ⟨hp.2, hp.1⟩
    · exact Or.inr ⟨hn.2, hn.1⟩

/-- Bounded diameter of tagged contacts bounds the number of occupied time indices. -/
theorem card_jetCell_of_tag_diam (S : Finset (ℤ × ℤ × ℤ))
    {f f₀ : ℝ → ℝ} {δ s ℓ w R : ℝ} (tag : ℤ × ℤ × ℤ → ℝ)
    (hδ : 0 < δ) (hs : 0 < s) (hℓ : 0 < ℓ) (C L : ℕ)
    (hS : ∀ t ∈ S, JetCell f f₀ δ s ℓ w C t)
    (hnear : ∀ t ∈ S, |tag t - (w + t.1 * ℓ)| ≤ ℓ)
    (hdiam : ∀ t ∈ S, ∀ u ∈ S, dist (tag t) (tag u) ≤ R)
    (hscale : R + 2 * ℓ ≤ L * ℓ) :
    S.card ≤ (4 * C + 1) ^ 2 * (2 * L + 1) := by
  classical
  have hcount : (S.image (fun t => t.1)).card ≤ 2 * L + 1 := by
    apply int_card_le_of_dist_le _ L
    intro j hj k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
    have h1 := abs_sub_le (w + t.1 * ℓ) (tag t) (w + u.1 * ℓ)
    have h2 := abs_sub_le (tag t) (tag u) (w + u.1 * ℓ)
    rw [abs_sub_comm (w + t.1 * ℓ) (tag t)] at h1
    have hd := hdiam t ht u hu
    rw [Real.dist_eq] at hd
    have heq : (w + t.1 * ℓ) - (w + u.1 * ℓ) = (t.1 - u.1 : ℝ) * ℓ := by ring
    rw [heq, abs_mul, abs_of_pos hℓ] at h1
    apply (mul_le_mul_iff_left₀ hℓ).mp
    linarith [hnear t ht, hnear u hu]
  exact (Finset.card_le_mul_card_image S ((4 * C + 1) ^ 2)
    (fun j _ => card_jetCell_time_fiber S hδ hs C hS j)).trans
      (Nat.mul_le_mul_left _ hcount)

/-- A fixed curve pair contributes only boundedly many cells in a transverse
slope band when its relative derivative is monotone. -/
theorem card_jetCell_transverse_pair (S : Finset (ℤ × ℤ × ℤ))
    {f f₀ F : ℝ → ℝ} {δ s ℓ w a b A c : ℝ} (tag : ℤ × ℤ × ℤ → ℝ)
    (hδ : 0 < δ) (hs : 0 < s) (hℓ : 0 < ℓ) (hc : 0 < c) (C L : ℕ)
    (hF : Differentiable ℝ F)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨ AntitoneOn (deriv F) (Icc a b))
    (hS : ∀ t ∈ S, JetCell f f₀ δ s ℓ w C t)
    (hnear : ∀ t ∈ S, |tag t - (w + t.1 * ℓ)| ≤ ℓ)
    (htag : ∀ t ∈ S, tag t ∈ Icc a b ∧ |F (tag t)| ≤ A ∧ c ≤ |deriv F (tag t)|)
    (hscale : 2 * A / c + 2 * ℓ ≤ L * ℓ) :
    S.card ≤ 2 * ((4 * C + 1) ^ 2 * (2 * L + 1)) := by
  classical
  let P := S.filter (fun t => c ≤ deriv F (tag t))
  let N := S.filter (fun t => ¬ c ≤ deriv F (tag t))
  have hP : P.card ≤ (4 * C + 1) ^ 2 * (2 * L + 1) := by
    apply card_jetCell_of_tag_diam P tag hδ hs hℓ C L
      (fun t ht => hS t (Finset.mem_filter.mp ht).1)
      (fun t ht => hnear t (Finset.mem_filter.mp ht).1) ?_ hscale
    intro t ht u hu
    have ht' := Finset.mem_filter.mp ht
    have hu' := Finset.mem_filter.mp hu
    exact sublevel_dist_le_of_monotone_deriv_same_sign hF hc hmono
      (htag t ht'.1).1 (htag u hu'.1).1 (htag t ht'.1).2.1 (htag u hu'.1).2.1
      (Or.inl ⟨ht'.2, hu'.2⟩)
  have hN : N.card ≤ (4 * C + 1) ^ 2 * (2 * L + 1) := by
    apply card_jetCell_of_tag_diam N tag hδ hs hℓ C L
      (fun t ht => hS t (Finset.mem_filter.mp ht).1)
      (fun t ht => hnear t (Finset.mem_filter.mp ht).1) ?_ hscale
    intro t ht u hu
    have ht' := Finset.mem_filter.mp ht
    have hu' := Finset.mem_filter.mp hu
    have hneg : ∀ v ∈ N, deriv F (tag v) ≤ -c := by
      intro v hv
      have hv' := Finset.mem_filter.mp hv
      rcases le_abs.mp (htag v hv'.1).2.2 with hp | hn
      · exact (hv'.2 hp).elim
      · linarith
    exact sublevel_dist_le_of_monotone_deriv_same_sign hF hc hmono
      (htag t ht'.1).1 (htag u hu'.1).1 (htag t ht'.1).2.1 (htag u hu'.1).2.1
      (Or.inr ⟨hneg t ht, hneg u hu⟩)
  have heq : P.card + N.card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) _
  omega

/-- At the natural contact scale, curvature separation bounds pair multiplicity
using the relative slope alone. -/
theorem card_jetCell_small_slope_pair (S : Finset (ℤ × ℤ × ℤ))
    {f f₀ F : ℝ → ℝ} {δ s ℓ w a b η c : ℝ} (tag : ℤ × ℤ × ℤ → ℝ)
    (hδ : 0 < δ) (hs : 0 < s) (hℓ : 0 < ℓ) (hc : 0 < c) (C L : ℕ)
    (hF : ContDiff ℝ 2 F)
    (hcurv : ∀ z ∈ Icc a b, c ≤ |deriv (deriv F) z|)
    (hS : ∀ t ∈ S, JetCell f f₀ δ s ℓ w C t)
    (hnear : ∀ t ∈ S, |tag t - (w + t.1 * ℓ)| ≤ ℓ)
    (htag : ∀ t ∈ S, tag t ∈ Icc a b ∧ |deriv F (tag t)| ≤ η)
    (hscale : 2 * η / c + 2 * ℓ ≤ L * ℓ) :
    S.card ≤ (4 * C + 1) ^ 2 * (2 * L + 1) := by
  apply card_jetCell_of_tag_diam S tag hδ hs hℓ C L hS hnear ?_ hscale
  intro t ht u hu
  exact sublevel_dist_le_of_deriv
    ((hF.deriv' (n := 1)).differentiable (by norm_num)) hc hcurv
    (htag t ht).1 (htag u hu).1 (htag t ht).2 (htag u hu).2

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
