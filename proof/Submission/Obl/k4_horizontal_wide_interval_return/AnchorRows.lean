/- Adapted within this LOT tree from o218/x0764, commit 57a9c674add438aa35f784b08ec4154ae5ff1920,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/AnchorRows.lean. -/
import Mathlib

set_option linter.unusedVariables false

/-!
# Bilinear fits from row and column fits on a weighted grid

The "common coefficient field" step of the wide-interval proposition (paper
`prop:wide-interval`): on a product grid in two velocity directions, a field that agrees to `e`
with one affine function along every row and one along every column is, on dense weight, within
`O(e/γ)` of the bilinear interpolant of two anchor rows at distance `≥ γ`.

* `affine_interp_bound`: an affine function bounded by `E` at two points `y₁ ≠ y₂` is bounded by
  `E (|y - y₁| + |y - y₂|)/|y₂ - y₁|`.
* `column_fit_of_anchors`: deterministic core; a value fitting its column's affine function,
  in a column that also has fitted values at both anchor rows, is close to `anchorBilinear`.
* `exists_dense_anchor_rows`: the weight of columns occupied at both anchor rows is dense, for
  some pair of anchor rows at distance `≥ γ` (power mean over columns and a near-pair count).

Rate-free and independent of the horizontal model.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return

open Finset

/-- Affine interpolation error. -/
theorem affine_interp_bound {a b y₁ y₂ y E : ℝ} (h12 : y₁ ≠ y₂) (h1 : |a + b * y₁| ≤ E)
    (h2 : |a + b * y₂| ≤ E) : |a + b * y| ≤ E * (|y - y₁| + |y - y₂|) / |y₂ - y₁| := by
  have hd : y₂ - y₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have hpos : 0 < |y₂ - y₁| := abs_pos.mpr hd
  have heq : a + b * y = ((a + b * y₁) * (y₂ - y) + (a + b * y₂) * (y - y₁)) / (y₂ - y₁) := by
    field_simp; ring
  rw [heq, abs_div, le_div_iff₀ hpos, div_mul_cancel₀ _ hpos.ne']
  calc |(a + b * y₁) * (y₂ - y) + (a + b * y₂) * (y - y₁)|
      ≤ |a + b * y₁| * |y₂ - y| + |a + b * y₂| * |y - y₁| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ E * |y₂ - y| + E * |y - y₁| := by gcongr
    _ = E * (|y - y₁| + |y - y₂|) := by rw [abs_sub_comm y₂ y]; ring

/-- The bilinear interpolant of the affine functions `r₁, r₂` of two anchor rows at heights
`y₁, y₂`. -/
noncomputable def anchorBilinear (r₁ r₂ : ℝ × ℝ) (y₁ y₂ x y : ℝ) : ℝ :=
  (r₁.1 + r₁.2 * x) * (y₂ - y) / (y₂ - y₁) + (r₂.1 + r₂.2 * x) * (y - y₁) / (y₂ - y₁)

theorem anchorBilinear_left (r₁ r₂ : ℝ × ℝ) {y₁ y₂ : ℝ} (h : y₁ ≠ y₂) (x : ℝ) :
    anchorBilinear r₁ r₂ y₁ y₂ x y₁ = r₁.1 + r₁.2 * x := by
  have hd : y₂ - y₁ ≠ 0 := sub_ne_zero.mpr h.symm
  unfold anchorBilinear; field_simp; ring

theorem anchorBilinear_right (r₁ r₂ : ℝ × ℝ) {y₁ y₂ : ℝ} (h : y₁ ≠ y₂) (x : ℝ) :
    anchorBilinear r₁ r₂ y₁ y₂ x y₂ = r₂.1 + r₂.2 * x := by
  have hd : y₂ - y₁ ≠ 0 := sub_ne_zero.mpr h.symm
  unfold anchorBilinear; field_simp; ring

/-- **Deterministic core.** If `f₁, f₂, f` are values in one column at heights `y₁, y₂, y`, each
within `e` of the column's affine function `c`, and `f₁, f₂` are within `e` of the anchor rows'
affine functions at the column's abscissa `x`, then `f` is within
`e + 2e (|y - y₁| + |y - y₂|)/|y₂ - y₁|` of the anchor bilinear interpolant. -/
theorem column_fit_of_anchors {r₁ r₂ c : ℝ × ℝ} {y₁ y₂ y x f₁ f₂ f e : ℝ} (h12 : y₁ ≠ y₂)
    (hr₁ : |f₁ - (r₁.1 + r₁.2 * x)| ≤ e) (hr₂ : |f₂ - (r₂.1 + r₂.2 * x)| ≤ e)
    (hc₁ : |f₁ - (c.1 + c.2 * y₁)| ≤ e) (hc₂ : |f₂ - (c.1 + c.2 * y₂)| ≤ e)
    (hc : |f - (c.1 + c.2 * y)| ≤ e) :
    |f - anchorBilinear r₁ r₂ y₁ y₂ x y| ≤
      e + 2 * e * (|y - y₁| + |y - y₂|) / |y₂ - y₁| := by
  -- the difference `c - B(x, ·)` is affine in the height
  set A := c.1 - ((r₁.1 + r₁.2 * x) * y₂ - (r₂.1 + r₂.2 * x) * y₁) / (y₂ - y₁) with hA
  set Bc := c.2 - ((r₂.1 + r₂.2 * x) - (r₁.1 + r₁.2 * x)) / (y₂ - y₁) with hB
  have hd : y₂ - y₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have hform : ∀ z, (c.1 + c.2 * z) - anchorBilinear r₁ r₂ y₁ y₂ x z = A + Bc * z := by
    intro z; simp only [anchorBilinear, hA, hB]; field_simp; ring
  have hD₁ : |A + Bc * y₁| ≤ 2 * e := by
    rw [← hform, anchorBilinear_left r₁ r₂ h12]
    calc |(c.1 + c.2 * y₁) - (r₁.1 + r₁.2 * x)|
        ≤ |(c.1 + c.2 * y₁) - f₁| + |f₁ - (r₁.1 + r₁.2 * x)| := abs_sub_le _ _ _
      _ ≤ e + e := by rw [abs_sub_comm]; exact add_le_add hc₁ hr₁
      _ = 2 * e := by ring
  have hD₂ : |A + Bc * y₂| ≤ 2 * e := by
    rw [← hform, anchorBilinear_right r₁ r₂ h12]
    calc |(c.1 + c.2 * y₂) - (r₂.1 + r₂.2 * x)|
        ≤ |(c.1 + c.2 * y₂) - f₂| + |f₂ - (r₂.1 + r₂.2 * x)| := abs_sub_le _ _ _
      _ ≤ e + e := by rw [abs_sub_comm]; exact add_le_add hc₂ hr₂
      _ = 2 * e := by ring
  have hD := affine_interp_bound h12 hD₁ hD₂ (y := y)
  rw [← hform] at hD
  calc |f - anchorBilinear r₁ r₂ y₁ y₂ x y|
      ≤ |f - (c.1 + c.2 * y)| + |(c.1 + c.2 * y) - anchorBilinear r₁ r₂ y₁ y₂ x y| :=
        abs_sub_le _ _ _
    _ ≤ e + 2 * e * (|y - y₁| + |y - y₂|) / |y₂ - y₁| := add_le_add hc hD

section Density

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Columns occupied (positive weight) at both rows `j₁, j₂`, weighted by column mass. -/
noncomputable def pairWeight (w : ι → κ → ℝ) (j₁ j₂ : κ) : ℝ :=
  ∑ i, if 0 < w i j₁ ∧ 0 < w i j₂ then ∑ j, w i j else 0

/-- **Dense anchor rows.** With vertex weights `0 ≤ w ≤ M` (`M > 0`), total weight `W`, and at
most `G` rows within height `γ` of any row, some pair of rows at height distance `≥ γ` has
`pairWeight ≥ (W³/(M² |ι|²) - G |κ| W)/|κ|²`, provided this is positive. -/
theorem exists_dense_anchor_rows (w : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ w i j) {M : ℝ} (hM0 : 0 < M)
    (hM : ∀ i j, w i j ≤ M) (y : κ → ℝ) {γ : ℝ} {G : ℕ}
    (hG : ∀ j, (univ.filter fun j' => |y j - y j'| < γ).card ≤ G)
    (hpos : 0 < (∑ i, ∑ j, w i j) ^ 3 / (M ^ 2 * (Fintype.card ι : ℝ) ^ 2) -
      G * Fintype.card κ * ∑ i, ∑ j, w i j) :
    ∃ j₁ j₂, γ ≤ |y j₁ - y j₂| ∧
      ((∑ i, ∑ j, w i j) ^ 3 / (M ^ 2 * (Fintype.card ι : ℝ) ^ 2) -
        G * Fintype.card κ * ∑ i, ∑ j, w i j) / (Fintype.card κ : ℝ) ^ 2 ≤ pairWeight w j₁ j₂ := by
  classical
  set W := ∑ i, ∑ j, w i j with hW
  set col : ι → ℝ := fun i => ∑ j, w i j with hcol
  have hcol0 : ∀ i, 0 ≤ col i := fun i => Finset.sum_nonneg fun j _ => hw i j
  set occ : ι → Finset κ := fun i => univ.filter fun j => 0 < w i j with hocc
  -- a column's mass is at most `M` times its number of occupied rows
  have hcolM : ∀ i, col i ≤ M * (occ i).card := by
    intro i
    calc col i = ∑ j ∈ occ i, w i j := by
          simp only [col, occ]
          rw [Finset.sum_filter_of_ne (fun j _ hne => lt_of_le_of_ne (hw i j) (Ne.symm hne))]
      _ ≤ ∑ _j ∈ occ i, M := Finset.sum_le_sum fun j _ => hM i j
      _ = M * (occ i).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- total pair weight over all ordered pairs of rows
  have htotal : ∑ p : κ × κ, pairWeight w p.1 p.2 = ∑ i, col i * ((occ i).card : ℝ) ^ 2 := by
    simp only [pairWeight]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_filter]
    have : (univ.filter fun p : κ × κ => 0 < w i p.1 ∧ 0 < w i p.2) = occ i ×ˢ occ i := by
      ext p; simp [occ]
    rw [this, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast; ring
  -- lower bound by the power mean
  have hcube : ∀ i, col i ^ 3 / M ^ 2 ≤ col i * ((occ i).card : ℝ) ^ 2 := by
    intro i
    rw [div_le_iff₀ (by positivity)]
    have h1 : col i ≤ M * (occ i).card := hcolM i
    have h2 : 0 ≤ col i := hcol0 i
    nlinarith [mul_le_mul h1 h1 h2 (by positivity)]
  have hmean : W ^ 3 / (Fintype.card ι : ℝ) ^ 2 ≤ ∑ i, col i ^ 3 := by
    have := pow_sum_div_card_le_sum_pow (s := (univ : Finset ι)) (f := col)
      (fun i _ => hcol0 i) 2
    simpa [hW, col, Finset.card_univ] using this
  have hall : W ^ 3 / (M ^ 2 * (Fintype.card ι : ℝ) ^ 2) ≤ ∑ p : κ × κ, pairWeight w p.1 p.2 := by
    rw [htotal]
    calc W ^ 3 / (M ^ 2 * (Fintype.card ι : ℝ) ^ 2)
        = (W ^ 3 / (Fintype.card ι : ℝ) ^ 2) / M ^ 2 := by ring
      _ ≤ (∑ i, col i ^ 3) / M ^ 2 := by gcongr
      _ = ∑ i, col i ^ 3 / M ^ 2 := by rw [Finset.sum_div]
      _ ≤ ∑ i, col i * ((occ i).card : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hcube i
  -- near pairs carry at most `G |κ| W`
  have hpw0 : ∀ j₁ j₂, 0 ≤ pairWeight w j₁ j₂ := fun j₁ j₂ =>
    Finset.sum_nonneg fun i _ => by split_ifs <;> [exact hcol0 i; exact le_rfl]
  set near : Finset (κ × κ) := univ.filter fun p => |y p.1 - y p.2| < γ with hnear
  have hnear_le : ∑ p ∈ near, pairWeight w p.1 p.2 ≤ G * Fintype.card κ * W := by
    calc ∑ p ∈ near, pairWeight w p.1 p.2 ≤ ∑ p ∈ near, W := by
          apply Finset.sum_le_sum; intro p _
          calc pairWeight w p.1 p.2 ≤ ∑ i, col i := Finset.sum_le_sum fun i _ => by
                split_ifs <;> [exact le_rfl; exact hcol0 i]
            _ = W := rfl
      _ = near.card * W := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (G * Fintype.card κ : ℕ) * W := by
          gcongr
          · exact Finset.sum_nonneg fun i _ => hcol0 i
          · have : near = univ.biUnion fun j => (univ.filter fun j' => |y j - y j'| < γ).image
                (fun j' => (j, j')) := by
              ext ⟨a, b⟩; simp [near]
            rw [this]
            refine (Finset.card_biUnion_le).trans ?_
            calc ∑ j, ((univ.filter fun j' => |y j - y j'| < γ).image (fun j' => (j, j'))).card
                ≤ ∑ _j : κ, G := Finset.sum_le_sum fun j _ => Finset.card_image_le.trans (hG j)
              _ = G * Fintype.card κ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
                  mul_comm]
      _ = G * Fintype.card κ * W := by push_cast; ring
  -- the far pairs carry the rest
  set far : Finset (κ × κ) := univ.filter fun p => γ ≤ |y p.1 - y p.2| with hfar
  have hsplit : ∑ p : κ × κ, pairWeight w p.1 p.2 =
      ∑ p ∈ near, pairWeight w p.1 p.2 + ∑ p ∈ far, pairWeight w p.1 p.2 := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun p : κ × κ => |y p.1 - y p.2| < γ)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p; simp [far, not_lt]
  have hfar_ge : W ^ 3 / (M ^ 2 * (Fintype.card ι : ℝ) ^ 2) - G * Fintype.card κ * W ≤
      ∑ p ∈ far, pairWeight w p.1 p.2 := by linarith
  -- some far pair carries the average
  have hfar_ne : far.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hfar_ge
    linarith
  obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image far (fun p => pairWeight w p.1 p.2) hfar_ne
  refine ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, ?_⟩
  have hcard : (far.card : ℝ) ≤ (Fintype.card κ : ℝ) ^ 2 := by
    have : far.card ≤ Fintype.card κ ^ 2 := by
      calc far.card ≤ (univ : Finset (κ × κ)).card := Finset.card_le_univ _
        _ = Fintype.card κ ^ 2 := by rw [Finset.card_univ, Fintype.card_prod, sq]
    exact_mod_cast this
  have hκ : (0 : ℝ) < (Fintype.card κ : ℝ) ^ 2 := by
    have : 0 < far.card := Finset.card_pos.mpr hfar_ne
    have : (0 : ℝ) < far.card := by exact_mod_cast this
    linarith
  rw [div_le_iff₀ hκ]
  calc W ^ 3 / (M ^ 2 * (Fintype.card ι : ℝ) ^ 2) - G * Fintype.card κ * W
      ≤ ∑ p ∈ far, pairWeight w p.1 p.2 := hfar_ge
    _ ≤ ∑ _q ∈ far, pairWeight w p.1 p.2 := Finset.sum_le_sum fun q hq => hpmax q hq
    _ = far.card * pairWeight w p.1 p.2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card κ : ℝ) ^ 2 * pairWeight w p.1 p.2 :=
        mul_le_mul_of_nonneg_right hcard (hpw0 _ _)
    _ = pairWeight w p.1 p.2 * (Fintype.card κ : ℝ) ^ 2 := by ring

end Density

end Submission.Obl.k4_horizontal_wide_interval_return
