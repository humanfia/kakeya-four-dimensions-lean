-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.GraphLine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.Covering

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A graph point with its horizontal coordinate first. -/
def graphPoint (f : ℝ → ℝ) (z : ℝ) : Plane := !₂[z, f z]

lemma graphPoint_dist_le {f : ℝ → ℝ} {x y : ℝ}
    (hf : |f x - f y| ≤ |x - y|) :
    dist (graphPoint f x) (graphPoint f y) ≤ 2 * |x - y| := by
  have hs := EuclideanSpace.dist_sq_eq (graphPoint f x) (graphPoint f y)
  simp only [Fin.sum_univ_two, graphPoint, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.dist_eq, sq_abs] at hs
  have hd : 0 ≤ dist (graphPoint f x) (graphPoint f y) := dist_nonneg
  have ha : 0 ≤ |x - y| := abs_nonneg _
  change dist (graphPoint f x) (graphPoint f y) ^ 2 = (x-y)^2 + (f x-f y)^2 at hs
  have hf2 := mul_self_le_mul_self (abs_nonneg (f x-f y)) hf
  nlinarith [sq_abs (f x - f y), sq_abs (x - y)]

lemma abs_inner_sub_lt_of_mem_thickening {p e : Plane} {c δ : ℝ}
    (he : ‖e‖ = 1) (hp : p ∈ thickening δ {q : Plane | inner ℝ q e = c}) :
    |inner ℝ p e - c| < δ := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  have hq' : inner ℝ q e = c := hq
  calc
    |inner ℝ p e - c| = |inner ℝ (p - q) e| := by rw [inner_sub_left, hq']
    _ ≤ ‖p - q‖ * ‖e‖ := abs_real_inner_le_norm _ _
    _ = dist p q := by rw [he, mul_one, dist_eq_norm]
    _ < δ := hpq

/-- A strip meeting widely separated points of a 1-Lipschitz graph has a
nonzero vertical normal component. -/
lemma vertical_normal_lower {f : ℝ → ℝ} {S : Set ℝ} {e : Plane} {c δ : ℝ}
    (he : ‖e‖ = 1) (hδ : 0 ≤ δ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ |x - y|)
    (hstrip : ∀ z ∈ S, |e 0 * z + e 1 * f z - c| ≤ δ)
    (hsep : ∃ x ∈ S, ∃ y ∈ S, 8 * δ < |x - y|) :
    (1 / 4 : ℝ) ≤ |e 1| := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hsep
  have hn : |e 0| ^ 2 + |e 1| ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq e
    simpa only [he, one_pow, Fin.sum_univ_two, sq_abs] using h.symm
  have hdiff : |e 0| * |x - y| ≤ 2 * δ + |e 1| * |f x - f y| := by
    calc
      |e 0| * |x - y| = |(e 0 * x + e 1 * f x - c) -
          (e 0 * y + e 1 * f y - c) - e 1 * (f x - f y)| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ |(e 0 * x + e 1 * f x - c) - (e 0 * y + e 1 * f y - c)| +
          |e 1 * (f x - f y)| := abs_sub _ _
      _ ≤ (|e 0 * x + e 1 * f x - c| + |e 0 * y + e 1 * f y - c|) +
          |e 1 * (f x - f y)| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ 2 * δ + |e 1| * |f x - f y| := by
        rw [abs_mul]
        linarith [hstrip x hx, hstrip y hy]
  have hlip := mul_le_mul_of_nonneg_left (hf x hx y hy) (abs_nonneg (e 1))
  by_contra hbad
  have hv : |e 1| < 1 / 4 := lt_of_not_ge hbad
  have hh : 3 / 4 < |e 0| := by nlinarith [abs_nonneg (e 0), abs_nonneg (e 1)]
  have hpos : 0 < |x - y| := lt_of_le_of_lt (by positivity) hxy
  nlinarith [mul_pos (sub_pos.mpr hh) hpos, mul_pos (sub_pos.mpr hv) hpos]

/-- Convert concentration near a line into an affine approximation to a graph. -/
lemma affine_of_strip_with_slope {f : ℝ → ℝ} {S : Set ℝ} {e : Plane} {c δ : ℝ}
    (he : ‖e‖ = 1) (hδ : 0 ≤ δ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ |x - y|)
    (hstrip : ∀ z ∈ S, |e 0 * z + e 1 * f z - c| ≤ δ)
    (hsep : ∃ x ∈ S, ∃ y ∈ S, 8 * δ < |x - y|) :
    ∃ a b : ℝ, |b| ≤ 4 ∧ ∀ z ∈ S, |f z - (a + b * z)| ≤ 4 * δ := by
  have hv := vertical_normal_lower he hδ hf hstrip hsep
  have he1 : e 1 ≠ 0 := by intro h; simp [h] at hv; linarith
  refine ⟨c / e 1, -(e 0 / e 1), ?_, ?_⟩
  · rw [abs_neg, abs_div, div_le_iff₀ (by linarith)]
    have h0 : |e 0| ≤ 1 := by simpa [he] using PiLp.norm_apply_le e 0
    linarith
  intro z hz
  have hid : (f z - (c / e 1 + -(e 0 / e 1) * z)) * e 1 =
      e 0 * z + e 1 * f z - c := by field_simp; ring
  have hprod : |f z - (c / e 1 + -(e 0 / e 1) * z)| * |e 1| ≤ δ := by
    rw [← abs_mul, hid]
    exact hstrip z hz
  nlinarith [mul_nonneg (abs_nonneg (f z - (c / e 1 + -(e 0 / e 1) * z)))
    (sub_nonneg.mpr hv)]

/-- A 1-Lipschitz graph over an interval has a cover with the expected linear size.
The centres are chosen on the graph, so Lipschitz control is needed only on `S`. -/
lemma graph_cover_of_interval {f : ℝ → ℝ} {S : Set ℝ} {a δ : ℝ} {n : ℕ}
    (hδ : 0 < δ)
    (hS : S ⊆ Ico a (a + (n : ℝ) * (δ / 2)))
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ |x - y|) :
    ∃ c : Fin n → Plane, graphPoint f '' S ⊆ ⋃ j, closedBall (c j) δ := by
  classical
  let cell (j : Fin n) : Set ℝ :=
    {z ∈ S | a + (j : ℝ) * (δ / 2) ≤ z ∧ z < a + ((j : ℝ) + 1) * (δ / 2)}
  let q (j : Fin n) : ℝ := if h : (cell j).Nonempty then h.choose else 0
  have hq (j : Fin n) (h : (cell j).Nonempty) : q j ∈ cell j := by
    simp only [q, dite_eq_left h]
    exact h.choose_spec
  refine ⟨fun j => graphPoint f (q j), ?_⟩
  rintro p ⟨z, hz, rfl⟩
  have hz0 : 0 ≤ (z - a) / (δ / 2) := div_nonneg (sub_nonneg.mpr (hS hz).1) (by positivity)
  have hzn : (z - a) / (δ / 2) < (n : ℝ) :=
    (div_lt_iff₀ (by positivity)).2 (by linarith [(hS hz).2])
  let j : Fin n := ⟨⌊(z - a) / (δ / 2)⌋₊, (Nat.floor_lt hz0).2 hzn⟩
  have hj0 : (j : ℝ) * (δ / 2) ≤ z - a :=
    (le_div_iff₀ (by positivity)).1 (Nat.floor_le hz0)
  have hj1 : z - a < ((j : ℝ) + 1) * (δ / 2) :=
    (div_lt_iff₀ (by positivity)).1 (Nat.lt_floor_add_one ((z - a) / (δ / 2)))
  have hzcell : z ∈ cell j := ⟨hz, by linarith, by linarith⟩
  have hqcell := hq j ⟨z, hzcell⟩
  have hd : |z - q j| ≤ δ / 2 := abs_le.mpr ⟨by linarith [hqcell.2.2], by linarith [hqcell.2.1]⟩
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  apply mem_closedBall.mpr
  exact (graphPoint_dist_le (hf z hz (q j) hqcell.1)).trans (by linarith)

/-- A graph with a large covering number contains a pair separated in height. -/
lemma separated_pair_of_graph_coverLower {f : ℝ → ℝ} {S : Set ℝ} {δ N : ℝ}
    (hδ : 0 < δ) (hN : 33 < N)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ |x - y|)
    (hcover : CoverLower (graphPoint f '' S) δ N) :
    ∃ x ∈ S, ∃ y ∈ S, 8 * δ < |x - y| := by
  by_contra hsep
  push Not at hsep
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hdom : S ⊆ Ico (x - 8 * δ) (x - 8 * δ + (33 : ℝ) * (δ / 2)) := by
      intro z hz
      have h := abs_le.mp (hsep z hz x hx)
      constructor <;> linarith
    obtain ⟨c, hc⟩ := graph_cover_of_interval hδ hdom hf
    have hle := hcover 33 c hc
    norm_num at hle
    linarith
  · have hempty : graphPoint f '' S = ∅ := by simp [Set.not_nonempty_iff_eq_empty.mp hS]
    have hle := hcover 0 Fin.elim0 (by simp [hempty])
    norm_num at hle
    linarith

/-- The line alternative of the projection dichotomy yields an affine graph on
all the heights whose graph points lie in the strip. -/
lemma affine_of_graph_line_coverLower_with_slope {f : ℝ → ℝ} {Z : Set ℝ} {e : Plane} {c δ N : ℝ}
    (hδ : 0 < δ) (hN : 33 < N) (he : ‖e‖ = 1)
    (hf : ∀ x ∈ Z, ∀ y ∈ Z, |f x - f y| ≤ |x - y|)
    (hcover : CoverLower (thickening δ {q : Plane | inner ℝ q e = c} ∩
      (graphPoint f '' Z)) δ N) :
    ∃ a b : ℝ, |b| ≤ 4 ∧ ∀ z ∈ Z,
      graphPoint f z ∈ thickening δ {q : Plane | inner ℝ q e = c} →
      |f z - (a + b * z)| ≤ 4 * δ := by
  let S : Set ℝ := {z ∈ Z | graphPoint f z ∈ thickening δ {q : Plane | inner ℝ q e = c}}
  have hS : CoverLower (graphPoint f '' S) δ N := by
    apply hcover.mono
    rintro p ⟨hp, z, hz, rfl⟩
    exact ⟨z, ⟨hz, hp⟩, rfl⟩
  have hfl : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ |x - y| :=
    fun x hx y hy => hf x hx.1 y hy.1
  have hstrip : ∀ z ∈ S, |e 0 * z + e 1 * f z - c| ≤ δ := by
    intro z hz
    have h := (abs_inner_sub_lt_of_mem_thickening he hz.2).le
    simpa [PiLp.inner_apply, Fin.sum_univ_two, graphPoint, mul_comm] using h
  obtain ⟨a, b, hb, hab⟩ := affine_of_strip_with_slope he hδ.le hfl hstrip
    (separated_pair_of_graph_coverLower hδ hN hfl hS)
  exact ⟨a, b, hb, fun z hz hzt => hab z ⟨hz, hzt⟩⟩

lemma affine_of_graph_line_coverLower {f : ℝ → ℝ} {Z : Set ℝ} {e : Plane} {c δ N : ℝ}
    (hδ : 0 < δ) (hN : 33 < N) (he : ‖e‖ = 1)
    (hf : ∀ x ∈ Z, ∀ y ∈ Z, |f x - f y| ≤ |x - y|)
    (hcover : CoverLower (thickening δ {q : Plane | inner ℝ q e = c} ∩
      (graphPoint f '' Z)) δ N) :
    ∃ a b : ℝ, ∀ z ∈ Z,
      graphPoint f z ∈ thickening δ {q : Plane | inner ℝ q e = c} →
      |f z - (a + b * z)| ≤ 4 * δ := by
  obtain ⟨a, b, _, h⟩ := affine_of_graph_line_coverLower_with_slope hδ hN he hf hcover
  exact ⟨a, b, h⟩

end WangZahlLot.Obl.wz_slab_local_linearity
