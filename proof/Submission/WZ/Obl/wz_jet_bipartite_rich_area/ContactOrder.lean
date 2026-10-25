-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactOrder.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactCrossing

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- Two upper-curvature curves contacting the same lower-curvature curve
at separated times have a strict order at each other's contact times. -/
theorem contact_pair_upper_dominance {f g h : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    {x y c δ η : ℝ}
    (hcf : ∀ t ∈ uIcc x y, c ≤ deriv (deriv f) t - deriv (deriv h) t)
    (hcg : ∀ t ∈ uIcc x y, c ≤ deriv (deriv g) t - deriv (deriv h) t)
    (hx : NearContact δ η f h x) (hy : NearContact δ η g h y)
    (hroom : 2 * δ < c / 2 * |y - x| ^ 2 - η * |y - x|) :
    f x - g x < 0 ∧ 0 < f y - g y := by
  have hx' : |deriv (f - h) x| ≤ η := by
    simpa only [deriv_sub_of_contDiff_two hf hh, Pi.sub_apply] using hx.2
  have hy' : |deriv (g - h) y| ≤ η := by
    simpa only [deriv_sub_of_contDiff_two hg hh, Pi.sub_apply] using hy.2
  have hcf' : ∀ t ∈ uIcc x y, c ≤ deriv (deriv (f - h)) t := by
    simpa only [deriv2_sub_of_contDiff_two hf hh, Pi.sub_apply] using hcf
  have hcg' : ∀ t ∈ uIcc y x, c ≤ deriv (deriv (g - h)) t := by
    simpa only [deriv2_sub_of_contDiff_two hg hh, Pi.sub_apply, uIcc_comm] using hcg
  have hleft := contact_quadratic_gap (hg.sub hh) hcg' hy.1 hy'
  have hright := contact_quadratic_gap (hf.sub hh) hcf' hx.1 hx'
  rw [abs_sub_comm x y] at hleft
  constructor <;> linarith [(abs_le.mp hx.1).2, (abs_le.mp hy.1).2]

/-- The lower curves have opposite strict orders at their separated
contacts to one upper-curvature curve, in either temporal orientation. -/
theorem contact_pair_lower_dominance {f g h : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    {x y c δ η : ℝ}
    (hcg : ∀ t ∈ uIcc x y, c ≤ deriv (deriv f) t - deriv (deriv g) t)
    (hch : ∀ t ∈ uIcc x y, c ≤ deriv (deriv f) t - deriv (deriv h) t)
    (hx : NearContact δ η f g x) (hy : NearContact δ η f h y)
    (hroom : 2 * δ < c / 2 * |y - x| ^ 2 - η * |y - x|) :
    0 < g x - h x ∧ g y - h y < 0 := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact contact_pair_dominance hf hg hh hxy hcg hch hx hy
      (by simpa only [abs_of_pos (sub_pos.mpr hxy)] using hroom)
  · subst y
    have hδ := (abs_nonneg _).trans hx.1
    simp only [sub_self, abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero] at hroom
    linarith
  · have hroom' : 2 * δ < c / 2 * (x - y) ^ 2 - η * (x - y) := by
      simpa only [abs_of_neg (sub_neg.mpr hyx), neg_sub] using hroom
    have h := contact_pair_dominance hf hh hg hyx
      (by simpa only [uIcc_comm] using hch) (by simpa only [uIcc_comm] using hcg)
      hy hx hroom'
    constructor <;> linarith [h.1, h.2]

/-- The four sign patterns at the corners of a contact quadrilateral force
its chronological edge order to follow the cycle. The first corner is
assumed earliest; either of the two cycle orientations can occur. -/
theorem contact_cycle_order_of_signs {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j m : Fin n) {a b c d l u : ℝ}
    (hik : 0 < dist (q i) (q k)) (hjm : 0 < dist (q j) (q m))
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u)
    (hc : c ∈ Icc l u) (hd : d ∈ Icc l u)
    (hab : a < b) (hac : a < c) (had : a < d)
    (hra : g i a - g k a < 0) (hrb : g i b - g k b < 0)
    (hrc : 0 < g i c - g k c) (hrd : 0 < g i d - g k d)
    (hba : 0 < g j a - g m a) (hbb : g j b - g m b < 0)
    (hbc : 0 < g j c - g m c) (hbd : g j d - g m d < 0) :
    (b < d ∧ d < c) ∨ (c < d ∧ d < b) := by
  have hmem {t : ℝ} (ht : t ∈ Icc l u) : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨hl.trans ht.1, ht.2.trans hu⟩
  have hred {w x y z : ℝ} (hw : w ∈ Icc l u) (hz : z ∈ Icc l u)
      (hwx : w < x) (hxy : x < y) (hyz : y < z)
      (hw' : g i w - g k w < 0) (hx' : 0 < g i x - g k x)
      (hy' : g i y - g k y < 0) (hz' : 0 < g i z - g k z) : False := by
    apply no_four_alternating_level_signs hg hjet k i (v := 0)
      (by rw [abs_zero, dist_comm]; positivity) (hmem hw) (hmem hz)
      hwx hxy hyz (by linarith [hw.1, hz.2]) <;> linarith
  have hblue {w x y z : ℝ} (hw : w ∈ Icc l u) (hz : z ∈ Icc l u)
      (hwx : w < x) (hxy : x < y) (hyz : y < z)
      (hw' : 0 < g j w - g m w) (hx' : g j x - g m x < 0)
      (hy' : 0 < g j y - g m y) (hz' : g j z - g m z < 0) : False := by
    exact no_four_alternating_level_signs hg hjet j m
      (by rw [abs_zero]; positivity) (hmem hw) (hmem hz)
      hwx hxy hyz (by linarith [hw.1, hz.2]) hw' hx' hy' hz'
  have hbcne : b ≠ c := by intro he; subst c; linarith
  have hbdne : b ≠ d := by intro he; subst d; linarith
  have hcdne : c ≠ d := by intro he; subst d; linarith
  rcases lt_or_gt_of_ne hbcne with hbc' | hcb
  · left
    constructor
    · by_contra h
      have hdb : d < b := lt_of_le_of_ne (le_of_not_gt h) hbdne.symm
      exact hred ha hc had hdb hbc' hra hrd hrb hrc
    · by_contra h
      have hcd : c < d := lt_of_le_of_ne (le_of_not_gt h) hcdne
      exact hblue ha hd hab hbc' hcd hba hbb hbc hbd
  · right
    constructor
    · by_contra h
      have hdc : d < c := lt_of_le_of_ne (le_of_not_gt h) hcdne.symm
      exact hblue ha hb had hdc hcb hba hbd hbc hbb
    · by_contra h
      have hbd : b < d := lt_of_le_of_ne (le_of_not_gt h) hbdne
      exact hred ha hd hac hcb hbd hra hrc hrb hrd

/-- A bipartite cycle of separated approximate contacts must occur in
cyclic temporal order. Only separations along the four participating curves
are required; the two disjoint edge pairs need no prescribed time gap. -/
theorem contact_cycle_order {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j m : Fin n) {a b c d l u γ δ η : ℝ}
    (hik : 0 < dist (q i) (q k)) (hjm : 0 < dist (q j) (q m))
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u)
    (hc : c ∈ Icc l u) (hd : d ∈ Icc l u)
    (hab : a < b) (hac : a < c) (had : a < d)
    (hij : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g i)) t - deriv (deriv (g j)) t)
    (him : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g i)) t - deriv (deriv (g m)) t)
    (hkj : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g k)) t - deriv (deriv (g j)) t)
    (hkm : ∀ t ∈ Icc l u, γ ≤ deriv (deriv (g k)) t - deriv (deriv (g m)) t)
    (hca : NearContact δ η (g i) (g j) a)
    (hcb : NearContact δ η (g i) (g m) b)
    (hcc : NearContact δ η (g k) (g j) c)
    (hcd : NearContact δ η (g k) (g m) d)
    (hrab : 2 * δ < γ / 2 * |b - a| ^ 2 - η * |b - a|)
    (hrac : 2 * δ < γ / 2 * |c - a| ^ 2 - η * |c - a|)
    (hrbd : 2 * δ < γ / 2 * |d - b| ^ 2 - η * |d - b|)
    (hrcd : 2 * δ < γ / 2 * |d - c| ^ 2 - η * |d - c|) :
    (b < d ∧ d < c) ∨ (c < d ∧ d < b) := by
  have hR₀ := contact_pair_upper_dominance (hg i) (hg k) (hg j)
    (fun t ht => hij t (uIcc_subset_Icc ha hc ht))
    (fun t ht => hkj t (uIcc_subset_Icc ha hc ht)) hca hcc hrac
  have hR₁ := contact_pair_upper_dominance (hg i) (hg k) (hg m)
    (fun t ht => him t (uIcc_subset_Icc hb hd ht))
    (fun t ht => hkm t (uIcc_subset_Icc hb hd ht)) hcb hcd hrbd
  have hB₀ := contact_pair_lower_dominance (hg i) (hg j) (hg m)
    (fun t ht => hij t (uIcc_subset_Icc ha hb ht))
    (fun t ht => him t (uIcc_subset_Icc ha hb ht)) hca hcb hrab
  have hB₁ := contact_pair_lower_dominance (hg k) (hg j) (hg m)
    (fun t ht => hkj t (uIcc_subset_Icc hc hd ht))
    (fun t ht => hkm t (uIcc_subset_Icc hc hd ht)) hcc hcd hrcd
  exact contact_cycle_order_of_signs hg hjet i k j m hik hjm hl hu hshort
    ha hb hc hd hab hac had hR₀.1 hR₁.1 hR₀.2 hR₁.2 hB₀.1 hB₀.2 hB₁.1 hB₁.2

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
