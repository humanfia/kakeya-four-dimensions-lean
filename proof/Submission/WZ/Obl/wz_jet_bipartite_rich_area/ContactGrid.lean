-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactGrid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ShearRect
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- Quantized value and slope at a grid time. -/
def JetCell (f f₀ : ℝ → ℝ) (δ s ℓ w : ℝ) (C : ℕ)
    (t : ℤ × ℤ × ℤ) : Prop :=
  |f (w + t.1 * ℓ) - f₀ (w + t.1 * ℓ) - t.2.1 * δ| ≤ C * δ ∧
  |deriv f (w + t.1 * ℓ) - deriv f₀ (w + t.1 * ℓ) - t.2.2 * s| ≤ C * s

/-- A finite set of integers of diameter at most `L` lies in a bounded interval. -/
theorem int_card_le_of_dist_le (S : Finset ℤ) (L : ℕ)
    (hS : ∀ i ∈ S, ∀ j ∈ S, |(i : ℝ) - j| ≤ L) :
    S.card ≤ 2 * L + 1 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · simp
  have hsub : S ⊆ Finset.Icc (j - (L : ℤ)) (j + (L : ℤ)) := by
    intro i hi
    have hab := abs_le.mp (hS i hi j hj)
    have ha : (j : ℝ) - L ≤ i := by linarith
    have hb : (i : ℝ) ≤ j + L := by linarith
    simp only [Finset.mem_Icc]
    constructor
    · exact_mod_cast ha
    · exact_mod_cast hb
  have hc := Finset.card_le_card hsub
  rw [Int.card_Icc] at hc
  omega

/-- Only boundedly many indices can approximate one value at the grid scale. -/
theorem int_card_le_of_grid_near (S : Finset ℤ) {x h : ℝ} (hh : 0 < h)
    (C : ℕ) (hS : ∀ j ∈ S, |x - j * h| ≤ C * h) :
    S.card ≤ 4 * C + 1 := by
  apply (int_card_le_of_dist_le S (2 * C) ?_).trans_eq (by omega)
  intro i hi j hj
  have ht := abs_sub_le (x - i * h) 0 (x - j * h)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  have heq : (x - i * h) - (x - j * h) = ((j : ℝ) - i) * h := by ring
  rw [heq, abs_mul, abs_of_pos hh, abs_sub_comm (j : ℝ)] at ht
  have hmul : |(i : ℝ) - j| * h ≤ (2 * C : ℝ) * h := by
    linarith [hS i hi, hS j hj]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using (mul_le_mul_iff_left₀ hh).mp hmul

/-- At one fixed time a curve occupies only boundedly many value/slope cells. -/
theorem card_jetCell_time_fiber (S : Finset (ℤ × ℤ × ℤ))
    {f f₀ : ℝ → ℝ} {δ s ℓ w : ℝ} (hδ : 0 < δ) (hs : 0 < s) (C : ℕ)
    (hS : ∀ t ∈ S, JetCell f f₀ δ s ℓ w C t) (j : ℤ) :
    (S.filter (fun t => t.1 = j)).card ≤ (4 * C + 1) ^ 2 := by
  classical
  let T := S.filter (fun t => t.1 = j)
  let V := T.image (fun t => t.2.1)
  let W := T.image (fun t => t.2.2)
  have hV : V.card ≤ 4 * C + 1 := by
    apply int_card_le_of_grid_near V hδ C
    intro l hl
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hl
    have ht' := Finset.mem_filter.mp ht
    simpa only [JetCell, ht'.2] using (hS t ht'.1).1
  have hW : W.card ≤ 4 * C + 1 := by
    apply int_card_le_of_grid_near W hs C
    intro m hm
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
    have ht' := Finset.mem_filter.mp ht
    simpa only [JetCell, ht'.2] using (hS t ht'.1).2
  have hcard : T.card ≤ (V ×ˢ W).card := by
    apply Finset.card_le_card_of_injOn (fun t => t.2)
    · intro t ht
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ht,
        Finset.mem_image_of_mem _ ht⟩
    · intro t ht u hu heq
      apply Prod.ext
      · exact (Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hu).2.symm
      · exact heq
  calc
    T.card ≤ V.card * W.card := by simpa only [Finset.card_product] using hcard
    _ ≤ (4 * C + 1) * (4 * C + 1) := Nat.mul_le_mul hV hW
    _ = (4 * C + 1) ^ 2 := by ring

/-- Local crowding is proportional to the number of time steps in the window. -/
theorem card_jetCell_time_window (S : Finset (ℤ × ℤ × ℤ))
    {f f₀ : ℝ → ℝ} {δ s ℓ w z : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) (hℓ : 0 < ℓ) (C L : ℕ)
    (hS : ∀ t ∈ S, JetCell f f₀ δ s ℓ w C t)
    (htime : ∀ t ∈ S, |w + t.1 * ℓ - z| ≤ L * ℓ) :
    S.card ≤ (4 * C + 1) ^ 2 * (4 * L + 1) := by
  classical
  have hcount : (S.image (fun t => t.1)).card ≤ 4 * L + 1 := by
    apply int_card_le_of_grid_near _ hℓ L (x := z - w)
    intro j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
    have heq : z - w - t.1 * ℓ = -(w + t.1 * ℓ - z) := by ring
    rw [heq, abs_neg]
    exact htime t ht
  exact (Finset.card_le_mul_card_image S ((4 * C + 1) ^ 2)
    (fun j _ => card_jetCell_time_fiber S hδ hs C hS j)).trans
      (Nat.mul_le_mul_left _ hcount)

/-- Quantized jets control the entire short sheared rectangle. -/
theorem jetCell_follows {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i i₀ : Fin n) {δ s ℓ w D : ℝ} (C : ℕ) (t : ℤ × ℤ × ℤ)
    (_hδ : 0 ≤ δ) (hs : 0 ≤ s) (_hℓ : 0 ≤ ℓ) (hD : 0 ≤ D)
    (hdist : dist (q i) (q i₀) ≤ 2 * D)
    (hw : w + t.1 * ℓ ∈ Icc (-1 : ℝ) 1)
    (hlin : s * ℓ ≤ δ) (hquad : D * ℓ ^ 2 ≤ δ)
    (hcell : JetCell (g i) (g i₀) δ s ℓ w C t) :
    Follows (g i) (g i₀) (w + t.1 * ℓ) ℓ (t.2.1 * δ) (t.2.2 * s)
      ((2 * C + 38) * δ) := by
  intro z hz hzt
  let y := w + t.1 * ℓ
  let σ := deriv (g i) y - deriv (g i₀) y
  have htaylor := JetControlled.sub_tangent_le hjet hg i i₀ hw hz
  have hzsq : (z - y) ^ 2 ≤ ℓ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hzt 2
  have hT : |(g i z - g i₀ z) - (g i y - g i₀ y) - σ * (z - y)| ≤ 38 * δ := by
    calc
      _ ≤ 19 * dist (q i) (q i₀) * (z - y) ^ 2 := htaylor
      _ ≤ 38 * D * ℓ ^ 2 :=
        mul_le_mul (by linarith) hzsq (sq_nonneg _) (by positivity)
      _ ≤ 38 * δ := by linarith
  have hS : |(σ - t.2.2 * s) * (z - y)| ≤ C * δ := by
    rw [abs_mul]
    calc
      _ ≤ (C * s) * ℓ := mul_le_mul hcell.2 hzt (abs_nonneg _) (by positivity)
      _ = C * (s * ℓ) := by ring
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hlin (Nat.cast_nonneg _)
  have hid : g i z - g i₀ z - (t.2.1 * δ + t.2.2 * s * (z - y)) =
      ((g i z - g i₀ z) - (g i y - g i₀ y) - σ * (z - y)) +
      (g i y - g i₀ y - t.2.1 * δ) + (σ - t.2.2 * s) * (z - y) := by ring
  change |g i z - g i₀ z - (t.2.1 * δ + t.2.2 * s * (z - y))| ≤ _
  rw [hid]
  have ht1 := abs_add_le
    (((g i z - g i₀ z) - (g i y - g i₀ y) - σ * (z - y)) +
      (g i y - g i₀ y - t.2.1 * δ)) ((σ - t.2.2 * s) * (z - y))
  have ht2 := abs_add_le
    ((g i z - g i₀ z) - (g i y - g i₀ y) - σ * (z - y))
    (g i y - g i₀ y - t.2.1 * δ)
  linarith [hcell.1]

/-- Two curves in the same jet cell have a near contact at its time center. -/
theorem nearContact_of_jetCell {f h f₀ : ℝ → ℝ} {δ s ℓ w : ℝ} {C : ℕ}
    {t : ℤ × ℤ × ℤ} (hf : JetCell f f₀ δ s ℓ w C t)
    (hh : JetCell h f₀ δ s ℓ w C t) :
    NearContact (2 * C * δ) (2 * C * s) f h (w + t.1 * ℓ) := by
  constructor
  · have ht := abs_sub_le (f (w + t.1 * ℓ) - f₀ (w + t.1 * ℓ) - t.2.1 * δ)
      0 (h (w + t.1 * ℓ) - f₀ (w + t.1 * ℓ) - t.2.1 * δ)
    have heq : (f (w + t.1 * ℓ) - f₀ (w + t.1 * ℓ) - t.2.1 * δ) -
        (h (w + t.1 * ℓ) - f₀ (w + t.1 * ℓ) - t.2.1 * δ) =
        f (w + t.1 * ℓ) - h (w + t.1 * ℓ) := by ring
    rw [heq] at ht
    simp only [sub_zero, zero_sub, abs_neg] at ht
    linarith [hf.1, hh.1]
  · have ht := abs_sub_le
      (deriv f (w + t.1 * ℓ) - deriv f₀ (w + t.1 * ℓ) - t.2.2 * s)
      0 (deriv h (w + t.1 * ℓ) - deriv f₀ (w + t.1 * ℓ) - t.2.2 * s)
    have heq : (deriv f (w + t.1 * ℓ) - deriv f₀ (w + t.1 * ℓ) - t.2.2 * s) -
        (deriv h (w + t.1 * ℓ) - deriv f₀ (w + t.1 * ℓ) - t.2.2 * s) =
        deriv f (w + t.1 * ℓ) - deriv h (w + t.1 * ℓ) := by ring
    rw [heq] at ht
    simp only [sub_zero, zero_sub, abs_neg] at ht
    linarith [hf.2, hh.2]

/-- Local crowding also holds when each cell is tagged by a point in its time window. -/
theorem card_jetCell_tag_window (S : Finset (ℤ × ℤ × ℤ))
    {f f₀ : ℝ → ℝ} {δ s ℓ w z R : ℝ} (tag : ℤ × ℤ × ℤ → ℝ)
    (hδ : 0 < δ) (hs : 0 < s) (hℓ : 0 < ℓ) (C L : ℕ)
    (hS : ∀ t ∈ S, JetCell f f₀ δ s ℓ w C t)
    (hnear : ∀ t ∈ S, |tag t - (w + t.1 * ℓ)| ≤ ℓ)
    (htime : ∀ t ∈ S, |tag t - z| ≤ R) (hscale : R + ℓ ≤ L * ℓ) :
    S.card ≤ (4 * C + 1) ^ 2 * (4 * L + 1) := by
  apply card_jetCell_time_window S hδ hs hℓ C L hS (z := z)
  intro t ht
  have htri := abs_sub_le (w + t.1 * ℓ) (tag t) z
  rw [abs_sub_comm (w + t.1 * ℓ) (tag t)] at htri
  linarith [hnear t ht, htime t ht]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
