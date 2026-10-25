import Mathlib

set_option autoImplicit false

/-!
# Anchor rows of a weighted grid

Adapted (Finset-indexed instead of Fintype-indexed) from session x0764's
`Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/AnchorRows.lean` on branch `x0764` of
o218 (this tree, LOT run g-oai-074).

* `affine_interp_bound`: an affine function bounded by `E` at two points `y₁ ≠ y₂` is bounded by
  `E (|y - y₁| + |y - y₂|)/|y₂ - y₁|`.
* `exists_dense_anchor_rows`: on a grid with cell weights at most `M`, the weight of the columns
  occupied at both of two rows is dense for some pair of rows at height distance `≥ γ` (power mean
  over columns and a near-pair count).
-/

namespace Submission.Obl.k4_conditional_common_affine_field

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

/-- Columns `i ∈ I` occupied (positive weight) at both rows `j₁, j₂`, weighted by column mass. -/
noncomputable def pairWeight (I J : Finset ℤ) (w : ℤ → ℤ → ℝ) (j₁ j₂ : ℤ) : ℝ :=
  ∑ i ∈ I, if 0 < w i j₁ ∧ 0 < w i j₂ then ∑ j ∈ J, w i j else 0

/-- **Dense anchor rows.** With cell weights `0 ≤ w ≤ M` (`M > 0`) on `I × J`, total weight `W`,
and at most `G` rows of `J` within height `γ` of any row of `J`, some pair of rows of `J` at
height distance `≥ γ` has `pairWeight ≥ (W³/(M² |I|²) - G |J| W)/|J|²`, provided this is
positive. -/
theorem exists_dense_anchor_rows (I J : Finset ℤ) (w : ℤ → ℤ → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    {M : ℝ} (hM0 : 0 < M) (hM : ∀ i j, w i j ≤ M) (y : ℤ → ℝ) {γ : ℝ} {G : ℕ}
    (hG : ∀ j ∈ J, (J.filter fun j' => |y j - y j'| < γ).card ≤ G)
    (hpos : 0 < (∑ i ∈ I, ∑ j ∈ J, w i j) ^ 3 / (M ^ 2 * (I.card : ℝ) ^ 2) -
      G * J.card * ∑ i ∈ I, ∑ j ∈ J, w i j) :
    ∃ j₁ ∈ J, ∃ j₂ ∈ J, γ ≤ |y j₁ - y j₂| ∧
      ((∑ i ∈ I, ∑ j ∈ J, w i j) ^ 3 / (M ^ 2 * (I.card : ℝ) ^ 2) -
        G * J.card * ∑ i ∈ I, ∑ j ∈ J, w i j) / (J.card : ℝ) ^ 2 ≤ pairWeight I J w j₁ j₂ := by
  classical
  set W := ∑ i ∈ I, ∑ j ∈ J, w i j with hW
  set col : ℤ → ℝ := fun i => ∑ j ∈ J, w i j with hcol
  have hcol0 : ∀ i, 0 ≤ col i := fun i => Finset.sum_nonneg fun j _ => hw i j
  set occ : ℤ → Finset ℤ := fun i => J.filter fun j => 0 < w i j with hocc
  -- a column's mass is at most `M` times its number of occupied rows
  have hcolM : ∀ i, col i ≤ M * (occ i).card := by
    intro i
    calc col i = ∑ j ∈ occ i, w i j := by
          simp only [col, occ]
          rw [Finset.sum_filter_of_ne (fun j _ hne => lt_of_le_of_ne (hw i j) (Ne.symm hne))]
      _ ≤ ∑ _j ∈ occ i, M := Finset.sum_le_sum fun j _ => hM i j
      _ = M * (occ i).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- total pair weight over all ordered pairs of rows
  have htotal : ∑ p ∈ J ×ˢ J, pairWeight I J w p.1 p.2 =
      ∑ i ∈ I, col i * ((occ i).card : ℝ) ^ 2 := by
    simp only [pairWeight]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_filter]
    have : ((J ×ˢ J).filter fun p : ℤ × ℤ => 0 < w i p.1 ∧ 0 < w i p.2) = occ i ×ˢ occ i := by
      ext p; simp only [Finset.mem_filter, Finset.mem_product, occ]; tauto
    rw [this, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast; ring
  -- lower bound by the power mean
  have hcube : ∀ i, col i ^ 3 / M ^ 2 ≤ col i * ((occ i).card : ℝ) ^ 2 := by
    intro i
    rw [div_le_iff₀ (by positivity)]
    have h1 : col i ≤ M * (occ i).card := hcolM i
    have h2 : 0 ≤ col i := hcol0 i
    nlinarith [mul_le_mul h1 h1 h2 (by positivity)]
  have hmean : W ^ 3 / (I.card : ℝ) ^ 2 ≤ ∑ i ∈ I, col i ^ 3 := by
    have := pow_sum_div_card_le_sum_pow (s := I) (f := col) (fun i _ => hcol0 i) 2
    simpa [hW, col] using this
  have hall : W ^ 3 / (M ^ 2 * (I.card : ℝ) ^ 2) ≤
      ∑ p ∈ J ×ˢ J, pairWeight I J w p.1 p.2 := by
    rw [htotal]
    calc W ^ 3 / (M ^ 2 * (I.card : ℝ) ^ 2)
        = (W ^ 3 / (I.card : ℝ) ^ 2) / M ^ 2 := by ring
      _ ≤ (∑ i ∈ I, col i ^ 3) / M ^ 2 := by gcongr
      _ = ∑ i ∈ I, col i ^ 3 / M ^ 2 := by rw [Finset.sum_div]
      _ ≤ ∑ i ∈ I, col i * ((occ i).card : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hcube i
  -- near pairs carry at most `G |J| W`
  have hpw0 : ∀ j₁ j₂, 0 ≤ pairWeight I J w j₁ j₂ := fun j₁ j₂ =>
    Finset.sum_nonneg fun i _ => by split_ifs <;> [exact hcol0 i; exact le_rfl]
  have hpwW : ∀ j₁ j₂, pairWeight I J w j₁ j₂ ≤ W := by
    intro j₁ j₂
    calc pairWeight I J w j₁ j₂ ≤ ∑ i ∈ I, col i := Finset.sum_le_sum fun i _ => by
          split_ifs <;> [exact le_rfl; exact hcol0 i]
      _ = W := rfl
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => hcol0 i
  set near : Finset (ℤ × ℤ) := (J ×ˢ J).filter fun p => |y p.1 - y p.2| < γ with hnear
  have hnear_le : ∑ p ∈ near, pairWeight I J w p.1 p.2 ≤ G * J.card * W := by
    calc ∑ p ∈ near, pairWeight I J w p.1 p.2 ≤ ∑ _p ∈ near, W :=
          Finset.sum_le_sum fun p _ => hpwW _ _
      _ = near.card * W := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (G * J.card : ℕ) * W := by
          gcongr
          have : near = J.biUnion fun j => (J.filter fun j' => |y j - y j'| < γ).image
              (fun j' => (j, j')) := by
            ext ⟨a, b⟩
            simp only [near, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
              Finset.mem_image, Prod.mk.injEq]
            constructor
            · rintro ⟨⟨ha, hb⟩, h⟩; exact ⟨a, ha, b, ⟨hb, h⟩, rfl, rfl⟩
            · rintro ⟨j, hj, j', ⟨hj', h⟩, rfl, rfl⟩; exact ⟨⟨hj, hj'⟩, h⟩
          rw [this]
          refine (Finset.card_biUnion_le).trans ?_
          calc ∑ j ∈ J, ((J.filter fun j' => |y j - y j'| < γ).image (fun j' => (j, j'))).card
              ≤ ∑ j ∈ J, G := Finset.sum_le_sum fun j hj => Finset.card_image_le.trans (hG j hj)
            _ = G * J.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ = G * J.card * W := by push_cast; ring
  -- the far pairs carry the rest
  set far : Finset (ℤ × ℤ) := (J ×ˢ J).filter fun p => γ ≤ |y p.1 - y p.2| with hfar
  have hsplit : ∑ p ∈ J ×ˢ J, pairWeight I J w p.1 p.2 =
      ∑ p ∈ near, pairWeight I J w p.1 p.2 + ∑ p ∈ far, pairWeight I J w p.1 p.2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (J ×ˢ J) (fun p : ℤ × ℤ => |y p.1 - y p.2| < γ)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p; simp [far, not_lt]
  have hfar_ge : W ^ 3 / (M ^ 2 * (I.card : ℝ) ^ 2) - G * J.card * W ≤
      ∑ p ∈ far, pairWeight I J w p.1 p.2 := by linarith
  -- some far pair carries the average
  have hfar_ne : far.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hfar_ge
    linarith
  obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image far (fun p => pairWeight I J w p.1 p.2) hfar_ne
  have hp' := Finset.mem_filter.mp hp
  refine ⟨p.1, (Finset.mem_product.mp hp'.1).1, p.2, (Finset.mem_product.mp hp'.1).2, hp'.2, ?_⟩
  have hcard : (far.card : ℝ) ≤ (J.card : ℝ) ^ 2 := by
    have : far.card ≤ J.card ^ 2 := by
      calc far.card ≤ (J ×ˢ J).card := Finset.card_filter_le _ _
        _ = J.card ^ 2 := by rw [Finset.card_product, sq]
    exact_mod_cast this
  have hκ : (0 : ℝ) < (J.card : ℝ) ^ 2 := by
    have : 0 < far.card := Finset.card_pos.mpr hfar_ne
    have : (0 : ℝ) < far.card := by exact_mod_cast this
    linarith
  rw [div_le_iff₀ hκ]
  calc W ^ 3 / (M ^ 2 * (I.card : ℝ) ^ 2) - G * J.card * W
      ≤ ∑ p ∈ far, pairWeight I J w p.1 p.2 := hfar_ge
    _ ≤ ∑ _q ∈ far, pairWeight I J w p.1 p.2 := Finset.sum_le_sum fun q hq => hpmax q hq
    _ = far.card * pairWeight I J w p.1 p.2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (J.card : ℝ) ^ 2 * pairWeight I J w p.1 p.2 :=
        mul_le_mul_of_nonneg_right hcard (hpw0 _ _)
    _ = pairWeight I J w p.1 p.2 * (J.card : ℝ) ^ 2 := by ring

end Submission.Obl.k4_conditional_common_affine_field
