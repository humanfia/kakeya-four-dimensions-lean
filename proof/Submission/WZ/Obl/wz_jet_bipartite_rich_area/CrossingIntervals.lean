-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.CrossingIntervals.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.Crossings

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- Three intermediate-value crossings rule out four alternating strict
signs for a small level of a curve difference on a short interval. -/
theorem no_four_alternating_level_signs {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {v a b c d : ℝ}
    (hv : |v| < dist (q i) (q j) / 480)
    (ha : a ∈ Icc (-1 : ℝ) 1) (hd : d ∈ Icc (-1 : ℝ) 1)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hshort : d - a ≤ 1 / 10000)
    (hfa : v < g i a - g j a) (hfb : g i b - g j b < v)
    (hfc : v < g i c - g j c) (hfd : g i d - g j d < v) : False := by
  have hf : Continuous (fun t => g i t - g j t) :=
    (hg i).continuous.sub (hg j).continuous
  obtain ⟨x, hx, hex⟩ := intermediate_value_Ioo' hab.le hf.continuousOn ⟨hfb, hfa⟩
  obtain ⟨y, hy, hey⟩ := intermediate_value_Ioo hbc.le hf.continuousOn ⟨hfb, hfc⟩
  obtain ⟨z, hz, hez⟩ := intermediate_value_Ioo' hcd.le hf.continuousOn ⟨hfd, hfc⟩
  exact no_three_close_level_crossings hg hjet i j hv
    ⟨ha.1.trans hx.1.le, by linarith [hx.2, hd.2]⟩
    ⟨by linarith [ha.1, hz.1], hz.2.le.trans hd.2⟩
    (hx.2.trans hy.1) (hy.2.trans hz.1) (by linarith [hx.1, hz.2])
    hex hey hez

/-- Two positive-to-negative crossing intervals for the same small level
overlap. The enclosing time interval must have length at most `1/10000`. -/
theorem oriented_level_intervals_overlap {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {v l u a b c d : ℝ}
    (hv : |v| < dist (q i) (q j) / 480)
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u)
    (hc : c ∈ Icc l u) (hd : d ∈ Icc l u)
    (hab : a < b) (hcd : c < d)
    (hfa : v < g i a - g j a) (hfb : g i b - g j b < v)
    (hfc : v < g i c - g j c) (hfd : g i d - g j d < v) :
    a < d ∧ c < b := by
  have hmem {t : ℝ} (ht : t ∈ Icc l u) : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨hl.trans ht.1, ht.2.trans hu⟩
  constructor
  · by_contra h
    have hda : d < a := lt_of_le_of_ne (le_of_not_gt h) (by
      intro hda
      subst d
      linarith)
    exact no_four_alternating_level_signs hg hjet i j hv
      (hmem hc) (hmem hb) hcd hda hab (by linarith [hc.1, hb.2])
      hfc hfd hfa hfb
  · by_contra h
    have hbc : b < c := lt_of_le_of_ne (le_of_not_gt h) (by
      intro hbc
      subst c
      linarith)
    exact no_four_alternating_level_signs hg hjet i j hv
      (hmem ha) (hmem hd) hab hbc hcd (by linarith [ha.1, hd.2])
      hfa hfb hfc hfd

/-- A finite nonempty collection of crossing intervals with the same
orientation has a common level crossing, not merely a common time. -/
theorem exists_shared_oriented_level_crossing {n : ℕ} {ι : Type*}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {v l u : ℝ} (F : Finset ι) (hF : F.Nonempty)
    (a b : ι → ℝ) (hv : |v| < dist (q i) (q j) / 480)
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (ha : ∀ k ∈ F, a k ∈ Icc l u) (hb : ∀ k ∈ F, b k ∈ Icc l u)
    (hab : ∀ k ∈ F, a k < b k)
    (hfa : ∀ k ∈ F, v < g i (a k) - g j (a k))
    (hfb : ∀ k ∈ F, g i (b k) - g j (b k) < v) :
    ∃ t ∈ Icc l u, g i t - g j t = v ∧ ∀ k ∈ F, t ∈ Ioo (a k) (b k) := by
  obtain ⟨k, hk, hmax⟩ := F.exists_max_image a hF
  obtain ⟨m, hm, hmin⟩ := F.exists_min_image b hF
  have hkm : a k < b m :=
    (oriented_level_intervals_overlap hg hjet i j hv hl hu hshort
      (ha k hk) (hb k hk) (ha m hm) (hb m hm) (hab k hk) (hab m hm)
      (hfa k hk) (hfb k hk) (hfa m hm) (hfb m hm)).1
  have hf : Continuous (fun t => g i t - g j t) :=
    (hg i).continuous.sub (hg j).continuous
  obtain ⟨t, ht, het⟩ := intermediate_value_Ioo' hkm.le hf.continuousOn
    ⟨hfb m hm, hfa k hk⟩
  refine ⟨t, ⟨(ha k hk).1.trans ht.1.le, ht.2.le.trans (hb m hm).2⟩, het, ?_⟩
  intro r hr
  exact ⟨(hmax r hr).trans_lt ht.1, ht.2.trans_le (hmin r hr)⟩

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
