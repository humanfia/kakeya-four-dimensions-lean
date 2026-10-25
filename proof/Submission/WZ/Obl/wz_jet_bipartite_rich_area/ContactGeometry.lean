-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_close_pair_moment.Geometry
import Submission.WZ.Obl.wz_jet_close_pair_moment.Sublevel

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- A contact records value and slope errors separately. -/
def NearContact (δ η : ℝ) (f h : ℝ → ℝ) (t : ℝ) : Prop :=
  |f t - h t| ≤ δ ∧ |deriv f t - deriv h t| ≤ η

/-- Near a contact at a scale much smaller than the coefficient distance,
the curvature alternative holds throughout a fixed short interval. -/
theorem contact_curvature_separation {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {δ η D y : ℝ}
    (hD : D ≤ dist (q i) (q j)) (hδ : δ < D / 480) (hη : η < D / 480)
    (hy : y ∈ Icc (-1 : ℝ) 1) (hc : NearContact δ η (g i) (g j) y) :
    ∀ t ∈ Icc (-1 : ℝ) 1, |t - y| ≤ 1 / 10000 →
      D / 60 ≤ |deriv (deriv (g i)) t - deriv (deriv (g j)) t| := by
  rcases hjet.local_alternative hg i j hy with hv | hs | hcurv
  · have hb := hv y hy (by norm_num)
    have hc0 := hc.1
    linarith
  · have hb := hs y hy (by norm_num)
    have hc1 := hc.2
    linarith
  · intro t ht hty
    exact (by linarith : D / 60 ≤ dist (q i) (q j) / 60).trans (hcurv t ht hty)

/-- The value variation of a curve difference near a time at which its slope
is small has a quadratic error. Only the upper jet bound is used. -/
theorem value_difference_near_contact {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {η x y : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1)
    (hslope : |deriv (g i) y - deriv (g j) y| ≤ η) :
    |(g i x - g j x) - (g i y - g j y)| ≤
      (η + 19 * dist (q i) (q j) * |x - y|) * |x - y| := by
  have hd : Differentiable ℝ (g i - g j) :=
    ((hg i).sub (hg j)).differentiable (by norm_num)
  have hb : ∀ t ∈ uIcc y x, ‖deriv (g i - g j) t‖ ≤
      η + 19 * dist (q i) (q j) * |x - y| := by
    intro t ht
    rw [deriv_sub_of_contDiff_two (hg i) (hg j), Real.norm_eq_abs]
    have hty := abs_sub_left_of_mem_uIcc ht
    have hvar := hjet.slope_difference_lipschitz hg i j (uIcc_subset_Icc hy hx ht) hy
    have htri := abs_sub_le (deriv (g i) t - deriv (g j) t)
      (deriv (g i) y - deriv (g j) y) 0
    simp only [sub_zero] at htri
    have hmul := mul_le_mul_of_nonneg_left hty
      (by positivity : 0 ≤ 19 * dist (q i) (q j))
    change |deriv (g i) t - deriv (g j) t| ≤ _
    linarith
  have h := (convex_uIcc y x).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => hd t) hb (left_mem_uIcc) (right_mem_uIcc)
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using h

/-- If two curves contact the same opposite curve in one short interval,
their contact times differ by at most the coefficient separation divided by
the cross scale, plus the slope error at that scale. -/
theorem contact_time_dist_le {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j : Fin n) {δ η D x y : ℝ}
    (hD : 0 < D) (hfar : D ≤ dist (q k) (q j))
    (hδ : δ < D / 480) (hη : η < D / 480)
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1)
    (hshort : |x - y| ≤ 1 / 10000)
    (hc : NearContact δ η (g i) (g j) x)
    (hc' : NearContact δ η (g k) (g j) y) :
    |x - y| ≤ 120 * (19 * dist (q i) (q k) + η) / D := by
  let A := 19 * dist (q i) (q k) + η
  have hdf : Differentiable ℝ (deriv (g k - g j)) :=
    (((hg k).sub (hg j)).deriv' (n := 1)).differentiable (by norm_num)
  have hcurv := contact_curvature_separation hg hjet k j hfar hδ hη hy hc'
  have hbound : ∀ t ∈ Icc (min y x) (max y x),
      D / 60 ≤ |deriv (deriv (g k - g j)) t| := by
    intro t ht
    rw [deriv2_sub_of_contDiff_two (hg k) (hg j)]
    exact hcurv t (uIcc_subset_Icc hy hx ht)
      ((abs_sub_left_of_mem_uIcc ht).trans hshort)
  have hfx : |deriv (g k - g j) x| ≤ A := by
    rw [deriv_sub_of_contDiff_two (hg k) (hg j)]
    change |deriv (g k) x - deriv (g j) x| ≤ _
    have htri := abs_sub_le (deriv (g k) x) (deriv (g i) x) (deriv (g j) x)
    have hki := (deriv_le_jetDistance (g k) (g i) x).trans (hjet k i x hx).2
    rw [dist_comm (q k) (q i)] at hki
    dsimp [A]
    linarith [hc.2]
  have hfy : |deriv (g k - g j) y| ≤ A := by
    rw [deriv_sub_of_contDiff_two (hg k) (hg j)]
    change |deriv (g k) y - deriv (g j) y| ≤ _
    dsimp [A]
    linarith [hc'.2, dist_nonneg (x := q i) (y := q k)]
  have h := sublevel_dist_le_of_deriv hdf (by positivity : 0 < D / 60)
    hbound (right_mem_uIcc) (left_mem_uIcc) hfx hfy
  rw [Real.dist_eq] at h
  apply h.trans
  dsimp [A]
  apply le_of_eq
  field_simp
  ring

/-- Transfer a near contact from one curve to another contacting the same
opposite curve. The quadratic loss in coefficient separation is essential. -/
theorem contact_value_transfer {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j : Fin n) {δ η D x y : ℝ}
    (hD : 0 < D) (hfar : D ≤ dist (q k) (q j))
    (hupper : dist (q k) (q j) ≤ 2 * D)
    (hδ : δ < D / 480) (hη : η < D / 480)
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1)
    (hshort : |x - y| ≤ 1 / 10000)
    (hc : NearContact δ η (g i) (g j) x)
    (hc' : NearContact δ η (g k) (g j) y) :
    |g i x - g k x| ≤
      2 * δ + 200000000 * (dist (q i) (q k) + η) ^ 2 / D := by
  let r := dist (q i) (q k)
  let L := |x - y|
  have hr : 0 ≤ r := dist_nonneg
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hc.2
  have hL0 : 0 ≤ L := abs_nonneg _
  have htime := contact_time_dist_le hg hjet i k j hD hfar hδ hη hx hy hshort hc hc'
  have hLD : L * D ≤ 2280 * (r + η) := by
    have h := (le_div_iff₀ hD).mp htime
    dsimp [r, L] at *
    linarith
  have hvar := value_difference_near_contact hg hjet k j hx hy hc'.2
  have hv : |g i x - g k x| ≤ 2 * δ + (η + 38 * D * L) * L := by
    have hki : |g k x - g j x| ≤ δ + (η + 38 * D * L) * L := by
      have htri := abs_sub_le (g k x - g j x) (g k y - g j y) 0
      simp only [sub_zero] at htri
      have hm : (η + 19 * dist (q k) (q j) * L) * L ≤
          (η + 38 * D * L) * L := by
        have hcoef : 19 * dist (q k) (q j) ≤ 38 * D := by linarith
        exact mul_le_mul_of_nonneg_right
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hL0)) hL0
      dsimp [L] at hm
      linarith [hc'.1]
    have htri := abs_sub_le (g i x) (g j x) (g k x)
    rw [abs_sub_comm (g j x) (g k x)] at htri
    linarith [hc.1]
  apply hv.trans
  apply add_le_add le_rfl
  apply (le_div_iff₀ hD).mpr
  have hsq : (L * D) ^ 2 ≤ (2280 * (r + η)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hL0 hD.le) hLD 2
  have hηL : η * (L * D) ≤ 2280 * (r + η) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hLD hη0
    nlinarith [mul_nonneg hr (add_nonneg hr hη0)]
  change (η + 38 * D * L) * L * D ≤ 200000000 * (r + η) ^ 2
  nlinarith [sq_nonneg (r + η)]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
