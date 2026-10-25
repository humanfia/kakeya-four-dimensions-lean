import Submission.Obl.k4_narrow_projected_row_parents.DeepCover
import Submission.Obl.k4_narrow_projected_row_parents.CompareCode

/-!
# Velocity lists from the comparison of true and projected labels

`Compared` is the output of the comparison of the true labels at depth `s` with a
projected layer at the same depth (paper, Lemma 8.3): a retained set of incidences of
`ρ`-mass at least `1/K₀`, the projected label and the true label of each retained
incidence, and for every true label and comparison code a list of at most `K₀`
projected labels containing the label of every retained incidence with that true
label and code.

`lists_of_compared` produces, in every true parent `Q` at a deeper depth `r`, lists of
the zoomed transverse velocity on the retained set (paper, Proposition 8.5, "From
projected intervals to a row list"):

* the zoomed cell and velocity bin of a retained incidence of `Q` pin its comparison
  code to an explicit menu of `O(K²)` codes (`parentMenu`); the true label at depth
  `s` is the ancestor of `Q`;
* each projected label confines the transverse velocity `b₄` to its velocity `vel i`
  up to `Hβ`, so the zoomed transverse velocity lies in one of three bins of width
  `E₁` predicted by `(i, w)`.

The choice of a heavy parent and the joint cell cap are in `VelocityGlue.lean`.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-! ### The interface of the comparison -/

/-- The output of the comparison at index `k` and depth `s`, for a family `C` of
projected assignments, with comparison codes of widths `(q, χ, g, m)`. -/
structure Compared (a : PreparedModel α) (k : ℕ) (s : ℝ) {n : ℕ} (C : Fin n → Set α)
    (q χ g m K₀ : ℝ) where
  /-- retained incidences -/
  R : Set (α × ℝ)
  measurable_R : MeasurableSet R
  mass : ENNReal.ofReal K₀⁻¹ ≤ a.rho k R
  /-- projected label of a line -/
  lab : α → Fin n
  lab_mem : ∀ z ∈ R, z.1 ∈ C (lab z.1)
  /-- true label of an incidence at depth `s` -/
  tru : α × ℝ → Fin (a.n k s)
  tru_mem : ∀ z ∈ R, z.1 ∈ a.B k s (tru z) ∧ z.2 ∈ a.block k s (tru z)
  /-- the partner lists -/
  partners : Fin (a.n k s) → (Fin 5 → ℤ) → Finset (Fin n)
  partners_card : ∀ Q c, ((partners Q c).card : ℝ) ≤ K₀
  partners_mem : ∀ z ∈ R, lab z.1 ∈ partners (tru z) (ccode q χ g m (a.b k z.1) z.2)

/-! ### Geometry: from a parent cell to comparison codes -/

/-- If `⌊x / δ⌋ = n` then `x` is within `δ` of the centre of the `n`-th bin. -/
theorem abs_sub_center_of_floor {x δ : ℝ} {n : ℤ} (hδ : 0 < δ) (h : ⌊x / δ⌋ = n) :
    |x - ((n : ℝ) + 1 / 2) * δ| ≤ δ := by
  have h1 := Int.floor_le (x / δ)
  have h2 := Int.lt_floor_add_one (x / δ)
  rw [h] at h1 h2
  rw [le_div_iff₀ hδ] at h1
  rw [div_lt_iff₀ hδ] at h2
  rw [abs_le]
  constructor <;> nlinarith

/-- The comparison-code menu of the zoomed cell `c` and velocity bin `w` of a parent `Q`
at depth `r`, for codes of widths `(q', χ, g', m)`. -/
def parentMenu (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ) (Q : Fin (a.n k r))
    (ξ Kb q' χ g' m : ℝ) (c : Fin 2 → ℤ) (w : ℤ) : Finset (Fin 5 → ℤ) :=
  codeMenu q' χ g' m
    (blockStart (a.T k r) (a.j k r Q) + a.q k r * (((c 0 : ℝ) + 1 / 2) * ξ)) (a.q k r * ξ)
    (((w : ℝ) + 1 / 2) * ξ) ξ
    ((a.c k r Q 0 + blockStart (a.T k r) (a.j k r Q) * a.c k r Q 1 +
        a.q k r * (((c 1 : ℝ) + 1 / 2) * ξ)) -
      (blockStart (a.T k r) (a.j k r Q) + a.q k r * (((c 0 : ℝ) + 1 / 2) * ξ)) *
        (((w : ℝ) + 1 / 2) * ξ))
    (a.q k r * ξ * (1 + Kb) + 2 * ξ)
    (a.c k r Q 3 + a.c k r Q 4 * (((w : ℝ) + 1 / 2) * ξ)) (Kb * narrow p k r + Kb * ξ) Kb
    (a.c k r Q 2 + (blockStart (a.T k r) (a.j k r Q) + a.q k r * (((c 0 : ℝ) + 1 / 2) * ξ)) *
        a.c k r Q 3 +
      a.c k r Q 4 * (a.c k r Q 0 + blockStart (a.T k r) (a.j k r Q) * a.c k r Q 1 +
        a.q k r * (((c 1 : ℝ) + 1 / 2) * ξ)))
    (Kb * a.q k r * narrow p k r + 2 * Kb * a.q k r * ξ)

theorem interval_subset_unit (T : ℕ) (j : Fin (2 ^ T)) : interval T j ⊆ Icc (0 : ℝ) 1 := by
  intro t ht
  rw [interval_eq] at ht
  obtain ⟨h1, h2⟩ := ht
  have hj : (j : ℝ) + 1 ≤ (2 : ℝ) ^ T := by
    have : (j : ℕ) + 1 ≤ 2 ^ T := j.2
    exact_mod_cast this
  have hpos : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hstart : blockStart T j + (2 : ℝ) ^ (-(T : ℤ)) = ((j : ℝ) + 1) / (2 : ℝ) ^ T := by
    unfold blockStart
    rw [zpow_neg, zpow_natCast, add_div, div_eq_mul_inv (1 : ℝ), one_mul]
  constructor
  · refine le_trans ?_ h1
    unfold blockStart
    positivity
  · rw [hstart] at h2
    refine h2.trans ?_
    rw [div_le_one hpos]
    exact hj

/-- The comparison code of an incidence of a parent lies in the menu of its zoomed cell
and velocity bin. -/
theorem ccode_mem_parentMenu (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) {ξ Kb q' χ g' m : ℝ} (hξ : 0 < ξ) (hq' : 0 < q') (hχ : 0 < χ)
    (hg' : 0 < g') (hm : 0 < m) (hKb : 0 ≤ Kb) (hqξ : a.q k r * ξ ≤ 1)
    (hc : ∀ e, |a.c k r Q e| ≤ Kb)
    {l : α} {t : ℝ} (ht : t ∈ a.block k r Q)
    (hbox : ∀ t' ∈ a.block k r Q,
      |(a.x k l t') 1 - a.c k r Q 0 - t' * a.c k r Q 1| ≤ Kb * a.q k r ∧
      |(a.x k l t') 2 - a.c k r Q 2 - t' * a.c k r Q 3 - a.c k r Q 4 * (a.x k l t') 1| ≤
        Kb * a.q k r * narrow p k r ∧
      |a.b k l 4 - a.c k r Q 3 - a.c k r Q 4 * a.b k l 3| ≤ Kb * narrow p k r)
    (h3 : |a.b k l 3| ≤ Kb) (h4 : |a.b k l 4| ≤ Kb)
    {c : Fin 2 → ℤ} {w : ℤ}
    (hcl : hcell (parentZoom p a k r Q) ξ (a.b k l) t = c) (hw : ⌊a.b k l 3 / ξ⌋ = w) :
    ccode q' χ g' m (a.b k l) t ∈ parentMenu p a k r Q ξ Kb q' χ g' m c w := by
  set t₀ := blockStart (a.T k r) (a.j k r Q) with ht₀
  set qr := a.q k r with hqr
  have hqr0 : 0 < qr := q_pos a k r
  set z₀ := a.c k r Q 0 + t₀ * a.c k r Q 1 with hz₀
  set tc := t₀ + qr * (((c 0 : ℝ) + 1 / 2) * ξ) with htc
  set Zc := z₀ + qr * (((c 1 : ℝ) + 1 / 2) * ξ) with hZc
  set v3 := ((w : ℝ) + 1 / 2) * ξ with hv3
  set g := narrow p k r with hg
  set b := a.b k l with hb
  -- the cell
  have hc0 : ⌊((t - t₀) / qr) / ξ⌋ = c 0 := by
    have := congrFun hcl 0
    simpa [k4_narrow_projected_row_parents.hcell, hpos, parentZoom] using this
  have hc1 : ⌊((b 0 + t * b 3 - z₀) / qr) / ξ⌋ = c 1 := by
    have := congrFun hcl 1
    have hid : (parentZoom p a k r Q).coeff b 0 + (t - (parentZoom p a k r Q).t₀) /
        (parentZoom p a k r Q).q * b 3 = (b 0 + t * b 3 - z₀) / qr := by
      rw [Zoom.coeff_zero]
      show (b 0 + t₀ * b 3 - z₀) / qr + (t - t₀) / qr * b 3 = (b 0 + t * b 3 - z₀) / qr
      field_simp
      ring
    simpa [k4_narrow_projected_row_parents.hcell, hpos, hid] using this
  have et : |t - tc| ≤ qr * ξ := by
    have h := abs_sub_center_of_floor hξ hc0
    have hid : t - tc = qr * ((t - t₀) / qr - ((c 0 : ℝ) + 1 / 2) * ξ) := by
      rw [htc]; field_simp; ring
    rw [hid, abs_mul, abs_of_pos hqr0]
    exact mul_le_mul_of_nonneg_left h hqr0.le
  have eZ : |(b 0 + t * b 3) - Zc| ≤ qr * ξ := by
    have h := abs_sub_center_of_floor hξ hc1
    have hid : (b 0 + t * b 3) - Zc = qr * ((b 0 + t * b 3 - z₀) / qr - ((c 1 : ℝ) + 1 / 2) * ξ) := by
      rw [hZc]; field_simp; ring
    rw [hid, abs_mul, abs_of_pos hqr0]
    exact mul_le_mul_of_nonneg_left h hqr0.le
  have e3 : |b 3 - v3| ≤ ξ := abs_sub_center_of_floor hξ hw
  have htunit : t ∈ Icc (0 : ℝ) 1 := interval_subset_unit _ _ ht
  have htc2 : |tc| ≤ 2 := by
    rw [abs_le] at et ⊢
    constructor <;> linarith [htunit.1, htunit.2]
  obtain ⟨_, hY, hrow⟩ := hbox t ht
  have hx1 : (a.x k l t) 1 = b 0 + t * b 3 := rfl
  have hx2 : (a.x k l t) 2 = b 1 + t * b 4 := rfl
  rw [hx1, hx2] at hY
  have hc3 := hc 3
  have hc4 := hc 4
  apply ccode_mem_codeMenu hq' hχ hg' hm et e3 _ _ h4 _
  · -- the major intercept
    have hid : b 0 - (Zc - tc * v3) = ((b 0 + t * b 3) - Zc) - (t - tc) * b 3 - tc * (b 3 - v3) := by
      ring
    rw [hid]
    have a1 : |(t - tc) * b 3| ≤ qr * ξ * Kb := by
      rw [abs_mul]; exact mul_le_mul et h3 (abs_nonneg _) (by positivity)
    have a2 : |tc * (b 3 - v3)| ≤ 2 * ξ := by
      rw [abs_mul]; exact mul_le_mul htc2 e3 (abs_nonneg _) (by norm_num)
    calc |((b 0 + t * b 3) - Zc) - (t - tc) * b 3 - tc * (b 3 - v3)|
        ≤ |(b 0 + t * b 3) - Zc| + |(t - tc) * b 3| + |tc * (b 3 - v3)| := by
          have := abs_sub (((b 0 + t * b 3) - Zc) - (t - tc) * b 3) (tc * (b 3 - v3))
          have := abs_sub ((b 0 + t * b 3) - Zc) ((t - tc) * b 3)
          linarith
      _ ≤ qr * ξ * (1 + Kb) + 2 * ξ := by nlinarith
  · -- the transverse velocity
    have hid : b 4 - (a.c k r Q 3 + a.c k r Q 4 * v3) =
        (b 4 - a.c k r Q 3 - a.c k r Q 4 * b 3) + a.c k r Q 4 * (b 3 - v3) := by ring
    rw [hid]
    have a1 : |a.c k r Q 4 * (b 3 - v3)| ≤ Kb * ξ := by
      rw [abs_mul]; exact mul_le_mul hc4 e3 (abs_nonneg _) hKb
    calc _ ≤ |b 4 - a.c k r Q 3 - a.c k r Q 4 * b 3| + |a.c k r Q 4 * (b 3 - v3)| :=
          abs_add_le _ _
      _ ≤ Kb * g + Kb * ξ := add_le_add hrow a1
  · -- the transverse position
    have hid : (b 1 + t * b 4) - (a.c k r Q 2 + tc * a.c k r Q 3 + a.c k r Q 4 * Zc) =
        ((b 1 + t * b 4) - a.c k r Q 2 - t * a.c k r Q 3 - a.c k r Q 4 * (b 0 + t * b 3)) +
          (t - tc) * a.c k r Q 3 + a.c k r Q 4 * ((b 0 + t * b 3) - Zc) := by ring
    rw [hid]
    have a1 : |(t - tc) * a.c k r Q 3| ≤ qr * ξ * Kb := by
      rw [abs_mul]; exact mul_le_mul et hc3 (abs_nonneg _) (by positivity)
    have a2 : |a.c k r Q 4 * ((b 0 + t * b 3) - Zc)| ≤ Kb * (qr * ξ) := by
      rw [abs_mul]; exact mul_le_mul hc4 eZ (abs_nonneg _) hKb
    calc _ ≤ |((b 1 + t * b 4) - a.c k r Q 2 - t * a.c k r Q 3 - a.c k r Q 4 * (b 0 + t * b 3))| +
          |(t - tc) * a.c k r Q 3| + |a.c k r Q 4 * ((b 0 + t * b 3) - Zc)| := by
          have := abs_add_le (((b 1 + t * b 4) - a.c k r Q 2 - t * a.c k r Q 3 -
            a.c k r Q 4 * (b 0 + t * b 3)) + (t - tc) * a.c k r Q 3)
            (a.c k r Q 4 * ((b 0 + t * b 3) - Zc))
          have := abs_add_le ((b 1 + t * b 4) - a.c k r Q 2 - t * a.c k r Q 3 -
            a.c k r Q 4 * (b 0 + t * b 3)) ((t - tc) * a.c k r Q 3)
          linarith
      _ ≤ Kb * qr * g + 2 * Kb * qr * ξ := by nlinarith

/-- The menu of a parent cell has `O(K²)` codes once the cell is finer than the codes. -/
theorem card_parentMenu_le (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (k : ℕ)
    (r : ℝ) (Q : Fin (a.n k r)) {ξ Kb q' χ g' m : ℝ} (hξ : 0 < ξ) (hq' : 0 < q') (hχ : 0 < χ)
    (hg' : 0 < g') (hKb : 1 ≤ Kb) (hm : m = q' * g')
    (h1 : a.q k r * ξ ≤ q') (h2 : a.q k r * ξ * (1 + Kb) + 2 * ξ ≤ χ) (h2' : ξ ≤ χ)
    (h3 : narrow p k r ≤ g') (h3' : ξ ≤ g') (h4 : a.q k r * narrow p k r ≤ m)
    (h4' : a.q k r * ξ ≤ m) (c : Fin 2 → ℤ) (w : ℤ) :
    ((parentMenu p a k r Q ξ Kb q' χ g' m c w).card : ℝ) ≤ 6912 * Kb ^ 2 := by
  have hqr0 := q_pos a k r
  have hg0 := narrow_pos p hp k r
  have hm0 : 0 < m := by rw [hm]; positivity
  have hKb0 : 0 ≤ Kb := by linarith
  refine (card_codeMenu_le hq' hχ hg' hm0 (by positivity) hξ.le (by positivity) (by positivity)
    hKb0 (by positivity)).trans ?_
  have f1 : 2 * (a.q k r * ξ) / q' + 2 ≤ 4 := by
    rw [div_add' _ _ _ hq'.ne', div_le_iff₀ hq']; linarith
  have f2 : 2 * ξ / χ + 2 ≤ 4 := by
    rw [div_add' _ _ _ hχ.ne', div_le_iff₀ hχ]; linarith
  have f3 : 2 * (a.q k r * ξ * (1 + Kb) + 2 * ξ) / χ + 2 ≤ 4 := by
    rw [div_add' _ _ _ hχ.ne', div_le_iff₀ hχ]; linarith
  have f4 : 2 * (Kb * narrow p k r + Kb * ξ) / g' + 2 ≤ 6 * Kb := by
    rw [div_add' _ _ _ hg'.ne', div_le_iff₀ hg']; nlinarith
  have f5 : 2 * (Kb * a.q k r * narrow p k r + 2 * Kb * a.q k r * ξ + a.q k r * ξ * Kb +
      (a.q k r * ξ + q') * (Kb * narrow p k r + Kb * ξ)) / m + 2 ≤ 18 * Kb := by
    rw [div_add' _ _ _ hm0.ne', div_le_iff₀ hm0]
    have e1 : Kb * a.q k r * narrow p k r ≤ Kb * m := by nlinarith
    have e2 : 2 * Kb * a.q k r * ξ ≤ 2 * Kb * m := by nlinarith
    have e3 : a.q k r * ξ * Kb ≤ Kb * m := by nlinarith
    have e4 : (a.q k r * ξ + q') * (Kb * narrow p k r + Kb * ξ) ≤ (2 * q') * (2 * Kb * g') := by
      apply mul_le_mul (by linarith) (by nlinarith) (by positivity) (by positivity)
    have e5 : (2 * q') * (2 * Kb * g') = 4 * Kb * m := by rw [hm]; ring
    nlinarith
  calc (2 * (a.q k r * ξ) / q' + 2) * ((2 * ξ / χ + 2) *
        (2 * (a.q k r * ξ * (1 + Kb) + 2 * ξ) / χ + 2) *
        ((2 * (Kb * narrow p k r + Kb * ξ) / g' + 2) *
          (2 * (Kb * a.q k r * narrow p k r + 2 * Kb * a.q k r * ξ + a.q k r * ξ * Kb +
            (a.q k r * ξ + q') * (Kb * narrow p k r + Kb * ξ)) / m + 2)))
      ≤ 4 * (4 * 4 * (6 * Kb * (18 * Kb))) := by
        have p1 : 0 ≤ 2 * (a.q k r * ξ) / q' + 2 := by positivity
        have p2 : 0 ≤ 2 * ξ / χ + 2 := by positivity
        have p3 : 0 ≤ 2 * (a.q k r * ξ * (1 + Kb) + 2 * ξ) / χ + 2 := by positivity
        have p4 : 0 ≤ 2 * (Kb * narrow p k r + Kb * ξ) / g' + 2 := by positivity
        have p5 : 0 ≤ 2 * (Kb * a.q k r * narrow p k r + 2 * Kb * a.q k r * ξ + a.q k r * ξ * Kb +
            (a.q k r * ξ + q') * (Kb * narrow p k r + Kb * ξ)) / m + 2 := by positivity
        gcongr
    _ = 6912 * Kb ^ 2 := by ring

/-! ### The lists -/

/-- The bin of width `E₁` of the zoomed transverse velocity predicted by a projected label
of velocity `v` at the velocity bin `w`. -/
def predBin (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ) (Q : Fin (a.n k r))
    (ξ E₁ v : ℝ) (w : ℤ) : ℤ :=
  ⌊((v - a.c k r Q 3 - a.c k r Q 4 * (((w : ℝ) + 1 / 2) * ξ)) / narrow p k r) / E₁⌋

/-- The list of bins of a parent cell: the predictions of the partners of every code of
its menu. -/
def parentList (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ) (Q : Fin (a.n k r))
    (ξ Kb q' χ g' m E₁ : ℝ) {n : ℕ} (vel : Fin n → ℝ)
    (partners : (Fin 5 → ℤ) → Finset (Fin n)) (c : Fin 2 → ℤ) (w : ℤ) : Finset ℤ :=
  (parentMenu p a k r Q ξ Kb q' χ g' m c w).biUnion fun code =>
    (partners code).biUnion fun i =>
      Finset.Icc (predBin p a k r Q ξ E₁ (vel i) w - 1) (predBin p a k r Q ξ E₁ (vel i) w + 1)

theorem card_parentList_le (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) (ξ Kb q' χ g' m E₁ : ℝ) {n : ℕ} (vel : Fin n → ℝ)
    (partners : (Fin 5 → ℤ) → Finset (Fin n)) {K₀ : ℝ}
    (hpart : ∀ code, ((partners code).card : ℝ) ≤ K₀) (c : Fin 2 → ℤ) (w : ℤ) :
    ((parentList p a k r Q ξ Kb q' χ g' m E₁ vel partners c w).card : ℝ) ≤
      ((parentMenu p a k r Q ξ Kb q' χ g' m c w).card : ℝ) * (3 * K₀) := by
  unfold parentList
  refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
  push_cast
  calc (∑ code ∈ parentMenu p a k r Q ξ Kb q' χ g' m c w, (((partners code).biUnion fun i =>
        Finset.Icc (predBin p a k r Q ξ E₁ (vel i) w - 1)
          (predBin p a k r Q ξ E₁ (vel i) w + 1)).card : ℝ))
      ≤ ∑ _code ∈ parentMenu p a k r Q ξ Kb q' χ g' m c w, (3 * K₀) := by
        refine Finset.sum_le_sum fun code _ => ?_
        refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
        push_cast
        calc (∑ i ∈ partners code, ((Finset.Icc (predBin p a k r Q ξ E₁ (vel i) w - 1)
              (predBin p a k r Q ξ E₁ (vel i) w + 1)).card : ℝ))
            = ∑ _i ∈ partners code, (3 : ℝ) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Int.card_Icc]
              have : predBin p a k r Q ξ E₁ (vel i) w + 1 + 1 -
                  (predBin p a k r Q ξ E₁ (vel i) w - 1) = 3 := by ring
              rw [this]; rfl
          _ = (partners code).card * 3 := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ K₀ * 3 := by gcongr; exact hpart code
          _ = 3 * K₀ := by ring
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The zoomed transverse velocity of a line of a projected label lies in one of the
three predicted bins. -/
theorem floor_mem_pred (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) {ξ E₁ Kb Hβ v : ℝ} (hξ : 0 < ξ) (hE₁ : 0 < E₁)
    (hc4 : |a.c k r Q 4| ≤ Kb) {b : Fin 6 → ℝ} {w : ℤ} (hw : ⌊b 3 / ξ⌋ = w)
    (hv : |b 4 - v| ≤ Hβ) (hsmall : (Hβ + Kb * ξ) / narrow p k r ≤ E₁) :
    ⌊(parentZoom p a k r Q).coeff b 4 / E₁⌋ ∈
      Finset.Icc (predBin p a k r Q ξ E₁ v w - 1) (predBin p a k r Q ξ E₁ v w + 1) := by
  have hg := narrow_pos p hp k r
  have hq := q_pos a k r
  have hcoeff : (parentZoom p a k r Q).coeff b 4 =
      (b 4 - a.c k r Q 3 - a.c k r Q 4 * b 3) / narrow p k r := by
    rw [Zoom.coeff_four]
    show a.q k r * (b 4 - a.c k r Q 3 - a.c k r Q 4 * b 3) / (a.q k r * narrow p k r) = _
    field_simp
  have e3 := abs_sub_center_of_floor hξ hw
  have hKb : 0 ≤ Kb := (abs_nonneg _).trans hc4
  have hdiff : |(parentZoom p a k r Q).coeff b 4 -
      (v - a.c k r Q 3 - a.c k r Q 4 * (((w : ℝ) + 1 / 2) * ξ)) / narrow p k r| ≤ E₁ := by
    rw [hcoeff, ← sub_div, abs_div, abs_of_pos hg]
    refine le_trans ?_ hsmall
    apply div_le_div_of_nonneg_right _ hg.le
    have hid : b 4 - a.c k r Q 3 - a.c k r Q 4 * b 3 -
        (v - a.c k r Q 3 - a.c k r Q 4 * (((w : ℝ) + 1 / 2) * ξ)) =
        (b 4 - v) - a.c k r Q 4 * (b 3 - ((w : ℝ) + 1 / 2) * ξ) := by ring
    rw [hid]
    have a1 : |a.c k r Q 4 * (b 3 - ((w : ℝ) + 1 / 2) * ξ)| ≤ Kb * ξ := by
      rw [abs_mul]; exact mul_le_mul hc4 e3 (abs_nonneg _) hKb
    calc _ ≤ |b 4 - v| + |a.c k r Q 4 * (b 3 - ((w : ℝ) + 1 / 2) * ξ)| := abs_sub _ _
      _ ≤ Hβ + Kb * ξ := add_le_add hv a1
  have h := floor_sub_le_one hE₁ hdiff
  rw [Finset.mem_Icc]
  unfold predBin
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-! ### Lists on the retained set -/

set_option maxHeartbeats 1600000 in
/-- **Velocity lists from the comparison.** At one index, the retained set of a comparison
at depth `s` (minus null sets) carries, in every true parent at depth `r`, lists of the
zoomed transverse velocity per zoomed cell and velocity bin, of size `O(K₀ K²)`. -/
theorem lists_of_compared (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (k : ℕ)
    (hcommon : a.Common p) {R r s : ℝ}
    (hatr : a.AtlasAt p R k r) (hats : a.AtlasAt p R k s)
    (hnest : ∀ i : Fin (a.n k r), ∃ h : Fin (a.n k s),
      a.A k r i ⊆ a.A k s h ∧ a.block k r i ⊆ a.block k s h)
    {n : ℕ} {C : Fin n → Set α} {vel : Fin n → ℝ} {Hβ : ℝ}
    (hvel : ∀ i, ∀ l ∈ C i, |a.b k l 4 - vel i| ≤ Hβ)
    {q' χ g' m K₀ : ℝ} (cmp : Compared a k s C q' χ g' m K₀) (hK₀ : 0 ≤ K₀)
    {ξ E₁ : ℝ} (hξ : 0 < ξ) (hq' : 0 < q') (hχ : 0 < χ) (hg' : 0 < g') (hm : m = q' * g')
    (hE₁ : 0 < E₁)
    (h1 : a.q k r * ξ ≤ q') (h2 : a.q k r * ξ * (1 + p.K k) + 2 * ξ ≤ χ) (h2' : ξ ≤ χ)
    (h3 : narrow p k r ≤ g') (h3' : ξ ≤ g') (h4 : a.q k r * narrow p k r ≤ m)
    (h4' : a.q k r * ξ ≤ m) (h5 : (Hβ + p.K k * ξ) / narrow p k r ≤ E₁)
    (hqξ : a.q k r * ξ ≤ 1) :
    ∃ Gl : Set (α × ℝ), MeasurableSet Gl ∧ ENNReal.ofReal K₀⁻¹ ≤ a.rho k Gl ∧
      ∀ Q : Fin (a.n k r), ∃ L : (Fin 2 → ℤ) → ℤ → Finset ℤ,
        (∀ c w, ((L c w).card : ℝ) ≤ 3 * K₀ * (6912 * p.K k ^ 2)) ∧
        ∀ z ∈ Gl, z ∈ a.B k r Q ×ˢ a.block k r Q →
          ⌊(parentZoom p a k r Q).coeff (a.b k z.1) 4 / E₁⌋ ∈
            L (hcell (parentZoom p a k r Q) ξ (a.b k z.1) z.2) ⌊a.b k z.1 3 / ξ⌋ := by
  classical
  obtain ⟨hbm, hνp, -, hμ, hρμ, -, -, -, hνb, -⟩ := hcommon k
  have hK1 : 1 ≤ p.K k := hp.2.2.1.1 k
  have hKpos : 0 < p.K k := by linarith
  obtain ⟨-, -, hmeas_r, -, hlab_r, -, -⟩ := hatr
  obtain ⟨-, -, hmeas_s, hdisj_s, -, -, -⟩ := hats
  -- a.e. bounds of the major and transverse velocities
  have hbd : ∀ᵐ z ∂a.rho k, |a.b k z.1 3| ≤ p.K k ∧ |a.b k z.1 4| ≤ p.K k := by
    have hnull : a.nu k {l | ¬ (|a.b k l 0| + |a.b k l 1| + |a.b k l 3| + |a.b k l 4| ≤ p.K k)} = 0 :=
      ae_iff.mp hνb
    have hμnull : a.mu k ({l | ¬ (|a.b k l 0| + |a.b k l 1| + |a.b k l 3| + |a.b k l 4| ≤ p.K k)}
        ×ˢ univ) = 0 := by
      apply le_antisymm _ zero_le
      calc _ ≤ (ENNReal.ofReal (p.K k) • (a.nu k).prod volume) _ := hμ _
        _ = 0 := by rw [Measure.smul_apply, Measure.prod_prod, hnull, zero_mul, smul_zero]
    have hμae : ∀ᵐ z ∂a.mu k,
        |a.b k z.1 0| + |a.b k z.1 1| + |a.b k z.1 3| + |a.b k z.1 4| ≤ p.K k := by
      rw [ae_iff]
      refine measure_mono_null (fun z hz => ?_) hμnull
      exact ⟨hz, mem_univ _⟩
    filter_upwards [ae_mono hρμ hμae] with z hz
    have := abs_nonneg (a.b k z.1 0)
    have := abs_nonneg (a.b k z.1 1)
    have := abs_nonneg (a.b k z.1 3)
    have := abs_nonneg (a.b k z.1 4)
    constructor <;> linarith
  have huniq := ae_mono hρμ (ae_unique_block hμ (a.T k s))
  -- the good set
  set G₀ : Set (α × ℝ) := {z | |a.b k z.1 3| ≤ p.K k ∧ |a.b k z.1 4| ≤ p.K k} ∩
    ⋂ j : Fin (2 ^ a.T k s), ⋂ j' : Fin (2 ^ a.T k s), {z | j ≠ j' →
      ¬ (z.2 ∈ interval (a.T k s) j ∧ z.2 ∈ interval (a.T k s) j')} with hG₀
  have hG₀m : MeasurableSet G₀ := by
    refine MeasurableSet.inter ?_ ?_
    · have h3m : Measurable fun z : α × ℝ => a.b k z.1 3 :=
        ((measurable_pi_apply 3).comp hbm).comp measurable_fst
      have h4m : Measurable fun z : α × ℝ => a.b k z.1 4 :=
        ((measurable_pi_apply 4).comp hbm).comp measurable_fst
      exact (measurableSet_le h3m.abs measurable_const).inter
        (measurableSet_le h4m.abs measurable_const)
    · refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun j' => ?_
      by_cases hjj : j = j'
      · have : {z : α × ℝ | j ≠ j' → ¬ (z.2 ∈ interval (a.T k s) j ∧
            z.2 ∈ interval (a.T k s) j')} = univ := by
          ext z; simp [hjj]
        rw [this]; exact MeasurableSet.univ
      · have : {z : α × ℝ | j ≠ j' → ¬ (z.2 ∈ interval (a.T k s) j ∧
            z.2 ∈ interval (a.T k s) j')} =
            (univ ×ˢ (interval (a.T k s) j ∩ interval (a.T k s) j'))ᶜ := by
          ext z; simp [hjj]
        rw [this]
        exact (MeasurableSet.univ.prod (measurableSet_Icc.inter measurableSet_Icc)).compl
  have hG₀ae : ∀ᵐ z ∂a.rho k, z ∈ G₀ := by
    filter_upwards [hbd, huniq] with z hz1 hz2
    refine ⟨hz1, ?_⟩
    simp only [mem_iInter, mem_setOf_eq]
    exact fun j j' hjj => hz2 j j' hjj
  refine ⟨cmp.R ∩ G₀, cmp.measurable_R.inter hG₀m, ?_, ?_⟩
  · have hXeq : a.rho k (cmp.R ∩ G₀) = a.rho k cmp.R := by
      apply measure_congr
      filter_upwards [hG₀ae] with z hz
      simp only [mem_inter_iff, hz, and_true]
    rw [hXeq]
    exact cmp.mass
  intro Q
  obtain ⟨anc, hancA, hancI⟩ := hnest Q
  obtain ⟨-, -, -, hc, -, hbox, -, -⟩ := hlab_r Q
  refine ⟨parentList p a k r Q ξ (p.K k) q' χ g' m E₁ vel (cmp.partners anc), ?_, ?_⟩
  · -- the list sizes
    intro c w
    refine (card_parentList_le p a k r Q ξ (p.K k) q' χ g' m E₁ vel (cmp.partners anc)
      (fun code => cmp.partners_card anc code) c w).trans ?_
    have hmenu := card_parentMenu_le p hp a k r Q (Kb := p.K k) hξ hq' hχ hg' hK1 hm h1 h2 h2'
      h3 h3' h4 h4' c w
    calc ((parentMenu p a k r Q ξ (p.K k) q' χ g' m c w).card : ℝ) * (3 * K₀)
        ≤ (6912 * p.K k ^ 2) * (3 * K₀) := by gcongr
      _ = 3 * K₀ * (6912 * p.K k ^ 2) := by ring
  · -- the lists contain the actual bins
    intro z hz hzQ
    have hzR : z ∈ cmp.R := hz.1
    have hzA : z.1 ∈ a.A k r Q := (hmeas_r Q).2.2 hzQ.1
    have hb3 := hz.2.1.1
    have hb4 := hz.2.1.2
    -- the true label of a retained incidence is the ancestor
    have htru : cmp.tru z = anc := by
      obtain ⟨htB, htI⟩ := cmp.tru_mem z hzR
      have hzA' : z.1 ∈ a.A k s anc := hancA hzA
      have hzI : z.2 ∈ a.block k s anc := hancI hzQ.2
      by_contra hne
      by_cases hj : a.j k s (cmp.tru z) = a.j k s anc
      · exact Set.disjoint_left.mp (hdisj_s _ _ hne hj) ((hmeas_s _).2.2 htB) hzA'
      · have := hz.2.2
        simp only [mem_iInter, mem_setOf_eq] at this
        exact this _ _ hj ⟨htI, hzI⟩
    have hmem := cmp.partners_mem z hzR
    rw [htru] at hmem
    have hcode := ccode_mem_parentMenu p a k r Q (Kb := p.K k) (q' := q') (χ := χ) (g' := g')
      (m := m) hξ hq' hχ hg' (by rw [hm]; positivity) hKpos.le hqξ hc hzQ.2
      (hbox z.1 hzA) hb3 hb4 rfl rfl
    unfold parentList
    rw [Finset.mem_biUnion]
    refine ⟨_, hcode, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨cmp.lab z.1, hmem, ?_⟩
    exact floor_mem_pred p hp a k r Q hξ hE₁ (hc 4) rfl (hvel _ _ (cmp.lab_mem z hzR)) h5

end

end Submission.Obl.k4_narrow_projected_row_parents
