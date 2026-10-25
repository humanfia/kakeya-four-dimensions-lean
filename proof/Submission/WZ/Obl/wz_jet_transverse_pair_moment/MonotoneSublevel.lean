-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_transverse_pair_moment.MonotoneSublevel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_transverse_pair_moment.Sublevel

namespace WangZahlLot.Obl.wz_jet_transverse_pair_moment

open MeasureTheory Set

/-- For a function whose derivative is monotone on an interval, each of the
positive and negative transverse parts of a sublevel has small diameter. -/
theorem volume_sublevel_transverse_of_monotone_deriv {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) {a b A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hmono : MonotoneOn (deriv f) (Icc a b) ∨ AntitoneOn (deriv f) (Icc a b)) :
    volume {t | t ∈ Icc a b ∧ |f t| ≤ A ∧ c ≤ |deriv f t|} ≤
      ENNReal.ofReal (4*A/c) := by
  let P := {t | t ∈ Icc a b ∧ |f t| ≤ A ∧ c ≤ deriv f t}
  let N := {t | t ∈ Icc a b ∧ |f t| ≤ A ∧ deriv f t ≤ -c}
  have hbound : ∀ S : Set ℝ,
      (∀ x ∈ S, x ∈ Icc a b ∧ |f x| ≤ A) →
      (∀ x ∈ S, ∀ y ∈ S, ∀ t ∈ Icc x y, c ≤ |deriv f t|) →
      volume S ≤ ENNReal.ofReal (2*A/c) := by
    intro S hS hd
    apply (Real.volume_le_diam S).trans
    apply Metric.ediam_le_of_forall_dist_le
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · exact sublevel_dist_le_of_deriv hf hc (hd x hx y hy)
        ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ (hS x hx).2 (hS y hy).2
    · rw [dist_comm]
      exact sublevel_dist_le_of_deriv hf hc (hd y hy x hx)
        ⟨le_rfl, hyx⟩ ⟨hyx, le_rfl⟩ (hS y hy).2 (hS x hx).2
  have hP : volume P ≤ ENNReal.ofReal (2*A/c) := by
    apply hbound P (fun _ hx => ⟨hx.1, hx.2.1⟩)
    intro x hx y hy t ht
    have ht' : t ∈ Icc a b := ⟨hx.1.1.trans ht.1, ht.2.trans hy.1.2⟩
    apply le_trans (b := deriv f t) _ (le_abs_self _)
    rcases hmono with hm | hm
    · exact hx.2.2.trans (hm hx.1 ht' ht.1)
    · exact hy.2.2.trans (hm ht' hy.1 ht.2)
  have hN : volume N ≤ ENNReal.ofReal (2*A/c) := by
    apply hbound N (fun _ hx => ⟨hx.1, hx.2.1⟩)
    intro x hx y hy t ht
    have ht' : t ∈ Icc a b := ⟨hx.1.1.trans ht.1, ht.2.trans hy.1.2⟩
    apply le_trans (b := -deriv f t) _ (neg_le_abs _)
    rcases hmono with hm | hm
    · have h := (hm ht' hy.1 ht.2).trans hy.2.2
      linarith
    · have h := (hm hx.1 ht' ht.1).trans hx.2.2
      linarith
  have hsub : {t | t ∈ Icc a b ∧ |f t| ≤ A ∧ c ≤ |deriv f t|} ⊆ P ∪ N := by
    intro t ht
    rcases le_abs.mp ht.2.2 with hp | hn
    · exact Or.inl ⟨ht.1, ht.2.1, hp⟩
    · exact Or.inr ⟨ht.1, ht.2.1, by linarith⟩
  calc
    volume {t | t ∈ Icc a b ∧ |f t| ≤ A ∧ c ≤ |deriv f t|} ≤
        volume (P ∪ N) := measure_mono hsub
    _ ≤ volume P + volume N := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2*A/c) + ENNReal.ofReal (2*A/c) := add_le_add hP hN
    _ = ENNReal.ofReal (4*A/c) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- A nonvanishing continuous second derivative has one sign on an interval,
so the first derivative is monotone there. -/
theorem monotone_deriv_of_deriv2_ne_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b : ℝ} (hnonzero : ∀ t ∈ Icc a b, deriv (deriv f) t ≠ 0) :
    MonotoneOn (deriv f) (Icc a b) ∨ AntitoneOn (deriv f) (Icc a b) := by
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv' (n := 1)
  have hdd : Continuous (deriv (deriv f)) := (hd.deriv' (n := 0)).continuous
  have hsign : (∀ t ∈ Icc a b, 0 ≤ deriv (deriv f) t) ∨
      (∀ t ∈ Icc a b, deriv (deriv f) t ≤ 0) := by
    by_cases ha : a ≤ b
    · have haa : a ∈ Icc a b := ⟨le_rfl, ha⟩
      rcases lt_or_gt_of_ne (hnonzero a haa) with hneg | hpos
      · right
        intro t ht
        by_contra hnot
        have hpos' : 0 ≤ deriv (deriv f) t := le_of_not_ge hnot
        obtain ⟨s, hs, hzero⟩ := intermediate_value_Icc ht.1
          hdd.continuousOn ⟨hneg.le, hpos'⟩
        exact hnonzero s ⟨hs.1, hs.2.trans ht.2⟩ hzero
      · left
        intro t ht
        by_contra hnot
        have hneg' : deriv (deriv f) t ≤ 0 := le_of_not_ge hnot
        obtain ⟨s, hs, hzero⟩ := intermediate_value_Icc' ht.1
          hdd.continuousOn ⟨hneg', hpos.le⟩
        exact hnonzero s ⟨hs.1, hs.2.trans ht.2⟩ hzero
    · left
      intro t ht
      exact (ha (ht.1.trans ht.2)).elim
  rcases hsign with hp | hn
  · left
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hd.continuous.continuousOn
      (hd.differentiable (by norm_num)).differentiableOn
    intro t ht
    exact hp t (interior_subset ht)
  · right
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hd.continuous.continuousOn
      (hd.differentiable (by norm_num)).differentiableOn
    intro t ht
    exact hn t (interior_subset ht)

end WangZahlLot.Obl.wz_jet_transverse_pair_moment
