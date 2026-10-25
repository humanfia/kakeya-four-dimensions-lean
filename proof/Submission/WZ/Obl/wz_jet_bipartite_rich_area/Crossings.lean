-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.Crossings.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_close_pair_moment.Geometry
import Submission.WZ.Obl.wz_jet_close_pair_moment.Sublevel

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- A sufficiently small level of a separated curve difference cannot be
attained three times on an interval of length at most `1 / 10000`. -/
theorem no_three_close_level_crossings {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {v x y z : ℝ}
    (hv : |v| < dist (q i) (q j) / 480)
    (hx : x ∈ Icc (-1 : ℝ) 1) (hz : z ∈ Icc (-1 : ℝ) 1)
    (hxy : x < y) (hyz : y < z) (hshort : z - x ≤ 1 / 10000)
    (heqx : g i x - g j x = v) (heqy : g i y - g j y = v)
    (heqz : g i z - g j z = v) : False := by
  have hpos : 0 < dist (q i) (q j) := by
    linarith [abs_nonneg v]
  have hf : ContDiff ℝ 2 (g i - g j) := (hg i).sub (hg j)
  have htmem {t : ℝ} (ht : t ∈ Ioo x z) :
      t ∈ Icc (-1 : ℝ) 1 ∧ |t - x| ≤ 1 / 10000 := by
    refine ⟨⟨hx.1.trans ht.1.le, ht.2.le.trans hz.2⟩, ?_⟩
    rw [abs_of_pos (sub_pos.mpr ht.1)]
    linarith [ht.2]
  rcases hjet.local_alternative hg i j hx with hval | hslope | hcurv
  · have h := hval x hx (by norm_num)
    rw [heqx] at h
    exact (not_lt_of_ge h) hv
  · obtain ⟨t, ht, hdt⟩ := exists_deriv_eq_zero hxy hf.continuous.continuousOn
      (show (g i - g j) x = (g i - g j) y from heqx.trans heqy.symm)
    have ht' := htmem ⟨ht.1, ht.2.trans hyz⟩
    have h := hslope t ht'.1 ht'.2
    rw [deriv_sub_of_contDiff_two (hg i) (hg j)] at hdt
    change deriv (g i) t - deriv (g j) t = 0 at hdt
    rw [hdt, abs_zero] at h
    linarith
  · have hfc : ContDiff ℝ 2 (fun t => (g i - g j) t - v) :=
      hf.sub contDiff_const
    obtain ⟨t, ht, hdt⟩ := exists_deriv2_eq_zero_of_three_zeros hfc hxy hyz
      (by simp only [Pi.sub_apply, heqx, sub_self])
      (by simp only [Pi.sub_apply, heqy, sub_self])
      (by simp only [Pi.sub_apply, heqz, sub_self])
    rw [deriv_sub_const_fun, deriv2_sub_of_contDiff_two (hg i) (hg j)] at hdt
    change deriv (deriv (g i)) t - deriv (deriv (g j)) t = 0 at hdt
    have ht' := htmem ht
    have h := hcurv t ht'.1 ht'.2
    rw [hdt, abs_zero] at h
    linarith

private theorem finite_ncard_le_two_of_no_three {S : Set ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → False) :
    S.Finite ∧ S.ncard ≤ 2 := by
  have hfin := Set.finite_of_forall_not_lt_lt h
  refine ⟨hfin, ?_⟩
  by_contra hcard
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    (Set.two_lt_ncard_iff hfin).mp (Nat.lt_of_not_ge hcard)
  have hn : ∀ ⦃a b c : S⦄, a < b → b < c → False := by
    intro a b c hab hbc
    exact h a a.property b b.property c c.property hab hbc
  rcases eq_or_eq_or_eq_of_forall_not_lt_lt hn
      (⟨x, hx⟩ : S) (⟨y, hy⟩ : S) (⟨z, hz⟩ : S) with he | he | he
  · exact hxy (congrArg Subtype.val he)
  · exact hyz (congrArg Subtype.val he)
  · exact hxz (congrArg Subtype.val he)

/-- Every short time interval contains at most two crossings with a level
whose magnitude is small compared with the coefficient distance. -/
theorem finite_ncard_level_crossings {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {v a b : ℝ}
    (hv : |v| < dist (q i) (q j) / 480) (hab : b - a ≤ 1 / 10000) :
    {z | z ∈ Icc (-1 : ℝ) 1 ∧ z ∈ Icc a b ∧ g i z - g j z = v}.Finite ∧
    {z | z ∈ Icc (-1 : ℝ) 1 ∧ z ∈ Icc a b ∧ g i z - g j z = v}.ncard ≤ 2 := by
  apply finite_ncard_le_two_of_no_three
  intro x hx y hy z hz hxy hyz
  exact no_three_close_level_crossings hg hjet i j hv hx.1 hz.1 hxy hyz
    (by linarith [hx.2.1.1, hz.2.1.2]) hx.2.2 hy.2.2 hz.2.2

/-- There is an absolute bound for the number of small-level crossings on
the whole parameter interval. In particular the crossing set is finite. -/
theorem exists_uniform_level_crossing_bound : ∃ N : ℕ, 0 < N ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
    (∀ i, ContDiff ℝ 2 (g i)) → JetControlled q g →
    ∀ i j : Fin n, ∀ v : ℝ, |v| < dist (q i) (q j) / 480 →
    {z | z ∈ Icc (-1 : ℝ) 1 ∧ g i z - g j z = v}.Finite ∧
    {z | z ∈ Icc (-1 : ℝ) 1 ∧ g i z - g j z = v}.ncard ≤ N := by
  classical
  obtain ⟨F, hcover⟩ := isCompact_Icc.elim_finite_subcover
    (fun w : Icc (-1 : ℝ) 1 => Metric.ball (w : ℝ) (1 / 30000))
    (fun _ => Metric.isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (by norm_num)⟩)
  refine ⟨2 * F.card + 1, by omega, ?_⟩
  intro n q g hg hjet i j v hv
  let T (w : Icc (-1 : ℝ) 1) : Set ℝ :=
    {z | z ∈ Icc (-1 : ℝ) 1 ∧
      z ∈ Icc ((w : ℝ) - 1 / 30000) ((w : ℝ) + 1 / 30000) ∧
      g i z - g j z = v}
  have hT (w : Icc (-1 : ℝ) 1) : (T w).Finite ∧ (T w).ncard ≤ 2 :=
    finite_ncard_level_crossings hg hjet i j hv (by linarith)
  have hsub : {z | z ∈ Icc (-1 : ℝ) 1 ∧ g i z - g j z = v} ⊆
      ⋃ w ∈ F, T w := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hcover hz.1)
    have hd : |z - (w : ℝ)| < 1 / 30000 := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hzw
    refine mem_iUnion₂.mpr ⟨w, hw, hz.1, ?_, hz.2⟩
    exact ⟨by linarith [(abs_lt.mp hd).1], by linarith [(abs_lt.mp hd).2]⟩
  have hfinite : (⋃ w ∈ F, T w).Finite :=
    F.finite_toSet.biUnion (fun w _ => (hT w).1)
  refine ⟨hfinite.subset hsub, ?_⟩
  calc
    _ ≤ (⋃ w ∈ F, T w).ncard := Set.ncard_le_ncard hsub hfinite
    _ ≤ ∑ w ∈ F, (T w).ncard := F.set_ncard_biUnion_le T
    _ ≤ ∑ _w ∈ F, 2 := Finset.sum_le_sum fun w _ => (hT w).2
    _ ≤ 2 * F.card + 1 := by simp; omega

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
