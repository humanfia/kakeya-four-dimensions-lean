-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.CurvatureOrder.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGeometry

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- A continuous function bounded away from zero on a connected domain
has one uniform sign on that domain. -/
theorem continuous_abs_lower_sign {S : Set ℝ} {f : ℝ → ℝ} {c : ℝ}
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hc : 0 < c)
    (habs : ∀ t ∈ S, c ≤ |f t|) :
    (∀ t ∈ S, c ≤ f t) ∨ (∀ t ∈ S, f t ≤ -c) := by
  by_cases hnonneg : ∀ t ∈ S, 0 ≤ f t
  · left
    intro t ht
    simpa only [abs_of_nonneg (hnonneg t ht)] using habs t ht
  · push Not at hnonneg
    obtain ⟨a, ha, hfa⟩ := hnonneg
    right
    intro b hb
    have hfb : f b < 0 := by
      by_contra hn
      have hfb0 : 0 ≤ f b := le_of_not_gt hn
      obtain ⟨t, ht, hft⟩ := hS.intermediate_value₂ ha hb hf continuousOn_const
        hfa.le hfb0
      have htbound := habs t ht
      rw [hft, abs_zero] at htbound
      linarith
    have hbabs := habs b hb
    rw [abs_of_neg hfb] at hbabs
    linarith

/-- Within two sufficiently small coefficient balls, one near contact fixes
the curvature ordering of every cross pair throughout the short time window.
The ordering is uniform in both curve indices and in time. -/
theorem cluster_curvature_order {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (a b : Fin n) {δ η D w : ℝ} {I : Set ℝ}
    (hD : 0 < D) (hfar : D ≤ dist (q a) (q b))
    (hδ : δ < D / 480) (hη : η < D / 480)
    (hI : IsPreconnected I) (hsub : I ⊆ Icc (-1 : ℝ) 1)
    (hw : w ∈ I) (hshort : ∀ t ∈ I, |t - w| ≤ 1 / 10000)
    (hc : NearContact δ η (g a) (g b) w) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ i j : Fin n, dist (q i) (q a) ≤ D / 10000 →
        dist (q j) (q b) ≤ D / 10000 → ∀ t ∈ I,
        D / 120 ≤ σ * (deriv (deriv (g i)) t - deriv (deriv (g j)) t) := by
  have hcurv := contact_curvature_separation hg hjet a b hfar hδ hη (hsub hw) hc
  have hcont (i : Fin n) : Continuous (deriv (deriv (g i))) :=
    (((hg i).deriv' (n := 1)).deriv' (n := 0)).continuous
  have hbound : ∀ t ∈ I,
      D / 60 ≤ |deriv (deriv (g a)) t - deriv (deriv (g b)) t| :=
    fun t ht => hcurv t (hsub ht) (hshort t ht)
  have herror (i j : Fin n) (hi : dist (q i) (q a) ≤ D / 10000)
      (hj : dist (q j) (q b) ≤ D / 10000) (t : ℝ) (ht : t ∈ I) :
      |(deriv (deriv (g i)) t - deriv (deriv (g j)) t) -
        (deriv (deriv (g a)) t - deriv (deriv (g b)) t)| ≤ 38 * D / 10000 := by
    have hi' := (deriv2_le_jetDistance (g i) (g a) t).trans (hjet i a t (hsub ht)).2
    have hj' := (deriv2_le_jetDistance (g j) (g b) t).trans (hjet j b t (hsub ht)).2
    calc
      _ = |(deriv (deriv (g i)) t - deriv (deriv (g a)) t) -
          (deriv (deriv (g j)) t - deriv (deriv (g b)) t)| := by congr 1; ring
      _ ≤ |deriv (deriv (g i)) t - deriv (deriv (g a)) t| +
          |deriv (deriv (g j)) t - deriv (deriv (g b)) t| := abs_sub _ _
      _ ≤ _ := by linarith
  rcases continuous_abs_lower_sign hI
      ((hcont a).sub (hcont b)).continuousOn (by positivity : 0 < D / 60) hbound with
    hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro i j hi hj t ht
    have he := (abs_le.mp (herror i j hi hj t ht)).1
    have hp := hpos t ht
    simp only [Pi.sub_apply] at hp
    simpa only [one_mul] using (show D / 120 ≤
      deriv (deriv (g i)) t - deriv (deriv (g j)) t by linarith)
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro i j hi hj t ht
    have he := (abs_le.mp (herror i j hi hj t ht)).2
    have hn := hneg t ht
    simp only [Pi.sub_apply] at hn
    nlinarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
