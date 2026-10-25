-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactCrossing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.CrossingIntervals
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LensGeometry

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- Two well-separated approximate contacts with a common upper-curvature
curve force strict opposite signs for the difference of the other curves. -/
theorem contact_pair_dominance {f g h : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    {x y c δ η : ℝ} (hxy : x < y)
    (hcg : ∀ t ∈ uIcc x y, c ≤ deriv (deriv f) t - deriv (deriv g) t)
    (hch : ∀ t ∈ uIcc x y, c ≤ deriv (deriv f) t - deriv (deriv h) t)
    (hx : NearContact δ η f g x) (hy : NearContact δ η f h y)
    (hroom : 2 * δ < c / 2 * (y - x) ^ 2 - η * (y - x)) :
    0 < g x - h x ∧ g y - h y < 0 := by
  have hx' : |deriv (f - g) x| ≤ η := by
    simpa only [deriv_sub_of_contDiff_two hf hg, Pi.sub_apply] using hx.2
  have hy' : |deriv (f - h) y| ≤ η := by
    simpa only [deriv_sub_of_contDiff_two hf hh, Pi.sub_apply] using hy.2
  have hcg' : ∀ t ∈ uIcc x y, c ≤ deriv (deriv (f - g)) t := by
    simpa only [deriv2_sub_of_contDiff_two hf hg, Pi.sub_apply] using hcg
  have hch' : ∀ t ∈ uIcc y x, c ≤ deriv (deriv (f - h)) t := by
    simpa only [deriv2_sub_of_contDiff_two hf hh, Pi.sub_apply, uIcc_comm] using hch
  have hleft := contact_quadratic_gap (hf.sub hh) hch' hy.1 hy'
  have hright := contact_quadratic_gap (hf.sub hg) hcg' hx.1 hx'
  have habs : |x - y| = y - x := by
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hxy)]
  simp only [habs, abs_of_pos (sub_pos.mpr hxy)] at hleft hright
  constructor <;> linarith [(abs_le.mp hx.1).2, (abs_le.mp hy.1).2]

/-- All ordered, separated contacts from a family of upper-curvature curves
to the same two opposite curves straddle one common crossing of those two
curves. This supplies an anchor for the entire common-neighbor family. -/
theorem exists_crossing_between_common_contacts {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (j k : Fin n) (F : Finset (Fin n)) (hF : F.Nonempty)
    (a b : Fin n → ℝ) {l u c δ η : ℝ}
    (hjk : 0 < dist (q j) (q k))
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (ha : ∀ i ∈ F, a i ∈ Icc l u) (hb : ∀ i ∈ F, b i ∈ Icc l u)
    (hab : ∀ i ∈ F, a i < b i)
    (hcj : ∀ i ∈ F, ∀ t ∈ Icc l u,
      c ≤ deriv (deriv (g i)) t - deriv (deriv (g j)) t)
    (hck : ∀ i ∈ F, ∀ t ∈ Icc l u,
      c ≤ deriv (deriv (g i)) t - deriv (deriv (g k)) t)
    (haj : ∀ i ∈ F, NearContact δ η (g i) (g j) (a i))
    (hbk : ∀ i ∈ F, NearContact δ η (g i) (g k) (b i))
    (hroom : ∀ i ∈ F,
      2 * δ < c / 2 * (b i - a i) ^ 2 - η * (b i - a i)) :
    ∃ t ∈ Icc l u, g j t = g k t ∧ ∀ i ∈ F, t ∈ Ioo (a i) (b i) := by
  have hsign : ∀ i ∈ F,
      0 < g j (a i) - g k (a i) ∧ g j (b i) - g k (b i) < 0 := by
    intro i hi
    apply contact_pair_dominance (hg i) (hg j) (hg k) (hab i hi)
      (fun t ht => hcj i hi t (uIcc_subset_Icc (ha i hi) (hb i hi) ht))
      (fun t ht => hck i hi t (uIcc_subset_Icc (ha i hi) (hb i hi) ht))
      (haj i hi) (hbk i hi) (hroom i hi)
  have hv : |(0 : ℝ)| < dist (q j) (q k) / 480 := by
    rw [abs_zero]
    positivity
  obtain ⟨t, ht, he, hbetween⟩ := exists_shared_oriented_level_crossing
    hg hjet j k F hF a b hv hl hu hshort ha hb hab
    (fun i hi => (hsign i hi).1) (fun i hi => (hsign i hi).2)
  exact ⟨t, ht, sub_eq_zero.mp he, hbetween⟩

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
