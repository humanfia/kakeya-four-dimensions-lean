-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.OrientedContactRank.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactRank

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- A single lower time separation supplies all the quadratic contact
margins once the slope and value errors are below that scale. -/
theorem contact_margin_of_separation {γ s t δ η : ℝ}
    (hγ : 0 < γ) (hs : 0 < s) (hst : s ≤ t)
    (hvalue : 8 * δ < γ * s ^ 2) (hslope : 4 * η ≤ γ * s) :
    2 * δ < γ / 2 * t ^ 2 - η * t := by
  have ht : 0 ≤ t := hs.le.trans hst
  have h1 := mul_le_mul_of_nonneg_right hslope ht
  have h2 := mul_le_mul_of_nonneg_left hst (mul_nonneg hγ.le ht)
  have h3 := mul_le_mul_of_nonneg_left (sq_le_sq₀ hs.le ht |>.mpr hst) hγ.le
  nlinarith only [h1, h2, h3, hvalue]

/-- Two common-neighbor contacts in the same temporal orientation yield
strict canonical rank descent. This version assumes the first parent
curve always contacts before the second parent curve. -/
theorem windowLensRank_lt_of_forward_contacts {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j m : Fin n) {l u a b c d γ M δ η B s : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (hik : 0 < dist (q i) (q k)) (hjm : 0 < dist (q j) (q m))
    (hwithin : ∀ t ∈ Icc l u,
      |deriv (deriv (g i)) t - deriv (deriv (g k)) t| ≤ M)
    (hγ : 0 < γ) (hB : 1 < B) (hs : 0 < s)
    (hratio : 2 * M * B ≤ γ) (hslope : 4 * η ≤ γ * s) (hvalue : 8 * δ < γ * s ^ 2)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hc : c ∈ Icc l u) (hd : d ∈ Icc l u)
    (hac : a < c) (hbd : b < d)
    (hij : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g i)) t - deriv (deriv (g j)) t)
    (him : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g i)) t - deriv (deriv (g m)) t)
    (hkj : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g k)) t - deriv (deriv (g j)) t)
    (hkm : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g k)) t - deriv (deriv (g m)) t)
    (hca : NearContact δ η (g i) (g j) a) (hcb : NearContact δ η (g i) (g m) b)
    (hcc : NearContact δ η (g k) (g j) c) (hcd : NearContact δ η (g k) (g m) d)
    (hsepab : s ≤ |b - a|) (hsepcd : s ≤ |d - c|)
    (hsepac : s ≤ |c - a|) (hsepbd : s ≤ |d - b|) :
    windowLensRank g B s l u j m < windowLensRank g B s l u i k := by
  have hrab := contact_margin_of_separation hγ hs hsepab hvalue hslope
  have hrcd := contact_margin_of_separation hγ hs hsepcd hvalue hslope
  have hrac := contact_margin_of_separation hγ hs hsepac hvalue hslope
  have hrbd := contact_margin_of_separation hγ hs hsepbd hvalue hslope
  have habne : a ≠ b := by intro he; subst b; simp only [sub_self, abs_zero] at hsepab; linarith
  rcases lt_or_gt_of_ne habne with hab | hba
  · have horder := contact_cycle_order hg hjet i k j m hik hjm hl hu hshort
      ha hb hc hd hab hac (hab.trans hbd) hij him hkj hkm hca hcb hcc hcd hrab hrac hrbd hrcd
    have hdc : d < c := by rcases horder with h | h; exact h.2; linarith [h.2]
    exact windowLensRank_lt_of_contact_cycle hg hjet i k j m hl hu hshort hik hjm hwithin
      hγ hB hs hratio hslope ha hb hd hc hab
      (by simpa only [abs_of_pos (sub_pos.mpr hbd)] using hsepbd) hdc
      hij him hkj hkm hca hcb hcd hcc
      (by simpa only [abs_of_pos (sub_pos.mpr hab)] using hrab)
      (by simpa only [abs_of_neg (sub_neg.mpr hdc), neg_sub] using hrcd)
      (by simpa only [abs_of_pos (sub_pos.mpr hac)] using hrac)
  · have hrba : 2 * δ < γ / 2 * |a - b| ^ 2 - η * |a - b| := by
      simpa only [abs_sub_comm] using hrab
    have hrdc : 2 * δ < γ / 2 * |c - d| ^ 2 - η * |c - d| := by
      simpa only [abs_sub_comm] using hrcd
    have horder := contact_cycle_order hg hjet i k m j hik
      (by simpa only [dist_comm] using hjm) hl hu hshort
      hb ha hd hc hba hbd (hba.trans hac) him hij hkm hkj hcb hca hcd hcc hrba hrbd hrac hrdc
    have hcd' : c < d := by rcases horder with h | h; exact h.2; linarith [h.2]
    have h := windowLensRank_lt_of_contact_cycle hg hjet i k m j hl hu hshort hik
      (by simpa only [dist_comm] using hjm) hwithin
      hγ hB hs hratio hslope hb ha hc hd hba
      (by simpa only [abs_of_pos (sub_pos.mpr hac)] using hsepac) hcd'
      him hij hkm hkj hcb hca hcc hcd
      (by simpa only [abs_of_pos (sub_pos.mpr hba)] using hrba)
      (by simpa only [abs_of_pos (sub_pos.mpr hcd')] using hrcd)
      (by simpa only [abs_of_pos (sub_pos.mpr hbd)] using hrbd)
    rwa [windowLensRank_symm g B s l u m j] at h

/-- Rank descent for either common-neighbor temporal orientation. -/
theorem windowLensRank_lt_of_same_orientation {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j m : Fin n) {l u a b c d γ M δ η B s : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (hik : 0 < dist (q i) (q k)) (hjm : 0 < dist (q j) (q m))
    (hwithin : ∀ t ∈ Icc l u,
      |deriv (deriv (g i)) t - deriv (deriv (g k)) t| ≤ M)
    (hγ : 0 < γ) (hB : 1 < B) (hs : 0 < s)
    (hratio : 2 * M * B ≤ γ) (hslope : 4 * η ≤ γ * s) (hvalue : 8 * δ < γ * s ^ 2)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hc : c ∈ Icc l u) (hd : d ∈ Icc l u)
    (horient : (a < c ∧ b < d) ∨ (c < a ∧ d < b))
    (hij : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g i)) t - deriv (deriv (g j)) t)
    (him : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g i)) t - deriv (deriv (g m)) t)
    (hkj : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g k)) t - deriv (deriv (g j)) t)
    (hkm : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g k)) t - deriv (deriv (g m)) t)
    (hca : NearContact δ η (g i) (g j) a) (hcb : NearContact δ η (g i) (g m) b)
    (hcc : NearContact δ η (g k) (g j) c) (hcd : NearContact δ η (g k) (g m) d)
    (hsepab : s ≤ |b - a|) (hsepcd : s ≤ |d - c|)
    (hsepac : s ≤ |c - a|) (hsepbd : s ≤ |d - b|) :
    windowLensRank g B s l u j m < windowLensRank g B s l u i k := by
  rcases horient with h | h
  · exact windowLensRank_lt_of_forward_contacts hg hjet i k j m hl hu hshort hik hjm hwithin
      hγ hB hs hratio hslope hvalue ha hb hc hd h.1 h.2 hij him hkj hkm hca hcb hcc hcd
      hsepab hsepcd hsepac hsepbd
  · have hr := windowLensRank_lt_of_forward_contacts hg hjet k i j m hl hu hshort
      (by simpa only [dist_comm] using hik) hjm
      (by simpa only [abs_sub_comm] using hwithin) hγ hB hs hratio hslope hvalue
      hc hd ha hb h.1 h.2 hkj hkm hij him hcc hcd hca hcb hsepcd hsepab
      (by simpa only [abs_sub_comm] using hsepac) (by simpa only [abs_sub_comm] using hsepbd)
    rwa [windowLensRank_symm g B s l u k i] at hr

/-- The same canonical rank descent when the parent curves have lower
curvature than their common neighbors. -/
theorem windowLensRank_lt_of_same_orientation_lower {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j m : Fin n) {l u a b c d γ M δ η B s : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (hik : 0 < dist (q i) (q k)) (hjm : 0 < dist (q j) (q m))
    (hwithin : ∀ t ∈ Icc l u,
      |deriv (deriv (g i)) t - deriv (deriv (g k)) t| ≤ M)
    (hγ : 0 < γ) (hB : 1 < B) (hs : 0 < s)
    (hratio : 2 * M * B ≤ γ) (hslope : 4 * η ≤ γ * s) (hvalue : 8 * δ < γ * s ^ 2)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hc : c ∈ Icc l u) (hd : d ∈ Icc l u)
    (horient : (a < c ∧ b < d) ∨ (c < a ∧ d < b))
    (hij : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g j)) t - deriv (deriv (g i)) t)
    (him : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g m)) t - deriv (deriv (g i)) t)
    (hkj : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g j)) t - deriv (deriv (g k)) t)
    (hkm : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g m)) t - deriv (deriv (g k)) t)
    (hca : NearContact δ η (g i) (g j) a) (hcb : NearContact δ η (g i) (g m) b)
    (hcc : NearContact δ η (g k) (g j) c) (hcd : NearContact δ η (g k) (g m) d)
    (hsepab : s ≤ |b - a|) (hsepcd : s ≤ |d - c|)
    (hsepac : s ≤ |c - a|) (hsepbd : s ≤ |d - b|) :
    windowLensRank g B s l u j m < windowLensRank g B s l u i k := by
  have hnegd (r : Fin n) (t : ℝ) : deriv (deriv (-g r)) t = -deriv (deriv (g r)) t := by
    rw [deriv.neg']
    change deriv (-deriv (g r)) t = -deriv (deriv (g r)) t
    exact deriv.neg
  have hflip (r v : Fin n) (t : ℝ) :
      deriv (deriv (-g r)) t - deriv (deriv (-g v)) t =
        deriv (deriv (g v)) t - deriv (deriv (g r)) t := by
    rw [hnegd, hnegd]
    ring
  have hr := windowLensRank_lt_of_same_orientation
    (g := fun r => -g r) (fun r => (hg r).neg) (jetControlled_neg hjet)
    i k j m hl hu hshort hik hjm
    (by intro t ht; rw [hflip]; simpa only [abs_sub_comm] using hwithin t ht)
    hγ hB hs hratio hslope hvalue ha hb hc hd horient
    (by intro t ht; rw [hflip]; exact hij t ht)
    (by intro t ht; rw [hflip]; exact him t ht)
    (by intro t ht; rw [hflip]; exact hkj t ht)
    (by intro t ht; rw [hflip]; exact hkm t ht)
    (nearContact_neg.mpr hca) (nearContact_neg.mpr hcb)
    (nearContact_neg.mpr hcc) (nearContact_neg.mpr hcd) hsepab hsepcd hsepac hsepbd
  simpa only [windowLensRank_neg] using hr

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
