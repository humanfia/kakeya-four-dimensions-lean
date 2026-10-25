-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.GridCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/GridCounts.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.AtScale
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.ColumnCodes

/-!
# Grid counts

* `roundZero_image_card_le`: reals within `ℓ` of a point `t₀` round (toward zero, to multiples
  of `w`) to at most `2 ℓ / w + 5` values.
* `cellOf_image_card_le`: points within `R` of `x` lie in at most `(2 R / c + 2) ^ 2` grid cells
  of side `c`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

attribute [local instance] Classical.propDecidable

theorem roundZero_eq_mul_int (w t : ℝ) : ∃ m : ℤ, roundZero w t = w * m := by
  unfold roundZero
  split_ifs
  · exact ⟨⌊t / w⌋, rfl⟩
  · exact ⟨⌈t / w⌉, rfl⟩

/-- Integers `m` with `|w m - u| ≤ L` number at most `2 L / w + 1`. -/
theorem int_window_card_le {w u L : ℝ} (hw : 0 < w) (hL : 0 ≤ L) (M : Finset ℤ)
    (hM : ∀ m ∈ M, |w * m - u| ≤ L) : (M.card : ℝ) ≤ 2 * L / w + 1 := by
  classical
  set lo : ℤ := ⌈(u - L) / w⌉ with hlo
  set hi : ℤ := ⌊(u + L) / w⌋ with hhi
  have hsub : M ⊆ Finset.Icc lo hi := by
    intro m hm
    have h := abs_le.mp (hM m hm)
    rw [Finset.mem_Icc]
    constructor
    · rw [hlo, Int.ceil_le, div_le_iff₀ hw]; linarith
    · rw [hhi, Int.le_floor, le_div_iff₀ hw]; linarith
  have hc := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
  rw [Int.card_Icc] at hc
  refine hc.trans ?_
  by_cases hle : lo ≤ hi + 1
  · have h1 : ((hi + 1 - lo).toNat : ℝ) = ((hi + 1 - lo : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [h1]
    push_cast
    have e1 : ((hi : ℤ) : ℝ) ≤ (u + L) / w := Int.floor_le _
    have e2 : (u - L) / w ≤ ((lo : ℤ) : ℝ) := Int.le_ceil _
    have e3 : (u + L) / w - (u - L) / w = 2 * L / w := by ring
    linarith
  · have h0 : (hi + 1 - lo).toNat = 0 := by omega
    rw [h0, Nat.cast_zero]
    positivity

/-- **Rounded values of a short interval.** -/
theorem roundZero_image_card_le {w ℓ t₀ : ℝ} (hw : 0 < w) (hℓ : 0 ≤ ℓ) (A : Finset ℝ)
    (hA : ∀ t ∈ A, |t - t₀| ≤ ℓ) :
    ((A.image (roundZero w)).card : ℝ) ≤ 2 * (ℓ + w) / w + 1 := by
  classical
  choose m hm using fun t => roundZero_eq_mul_int w t
  have himg : A.image (roundZero w) = (A.image m).image (fun k : ℤ => w * k) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro t _
    exact hm t
  rw [himg]
  refine ((Nat.cast_le (α := ℝ)).mpr Finset.card_image_le).trans ?_
  apply int_window_card_le hw (by linarith)
  intro k hk
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
  rw [← hm t]
  have h1 := roundZero_close hw t
  have h2 := hA t ht
  calc |roundZero w t - t₀| = |(roundZero w t - t) + (t - t₀)| := by ring_nf
    _ ≤ |roundZero w t - t| + |t - t₀| := abs_add_le _ _
    _ ≤ ℓ + w := by linarith

/-- **Grid cells of a ball.** -/
theorem cellOf_image_card_le {c R : ℝ} (hc : 0 < c) (hR : 0 ≤ R) (x : E2) (Q : Finset E2)
    (hQ : ∀ p ∈ Q, dist p x ≤ R) :
    ((Q.image (cellOf c)).card : ℝ) ≤ (2 * (R + c) / c + 1) ^ 2 := by
  classical
  have hcoord : ∀ p ∈ Q, ∀ i : Fin 2, |p i - x i| ≤ R := by
    intro p hp i
    have h2 : |p i - x i| ≤ dist p x := by
      have := EuclideanSpace.dist_eq p x
      rw [this]
      calc |p i - x i| = Real.sqrt ((p i - x i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (∑ j, dist (p j) (x j) ^ 2) := by
          apply Real.sqrt_le_sqrt
          have hterm : (p i - x i) ^ 2 = dist (p i) (x i) ^ 2 := by
            rw [Real.dist_eq, sq_abs]
          rw [hterm]
          exact Finset.single_le_sum (f := fun j => dist (p j) (x j) ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    exact h2.trans (hQ p hp)
  have hwin : ∀ i : Fin 2,
      (((Q.image (fun p => ⌊p i / c⌋))).card : ℝ) ≤ 2 * (R + c) / c + 1 := by
    intro i
    apply int_window_card_le hc (by linarith) (u := x i)
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have h1 : c * (⌊p i / c⌋ : ℝ) ≤ p i := by
      have := Int.floor_le (p i / c)
      calc c * (⌊p i / c⌋ : ℝ) ≤ c * (p i / c) := mul_le_mul_of_nonneg_left this hc.le
        _ = p i := by field_simp
    have h2 : p i < c * (⌊p i / c⌋ : ℝ) + c := by
      have := Int.lt_floor_add_one (p i / c)
      calc p i = c * (p i / c) := by field_simp
        _ < c * ((⌊p i / c⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left this hc
        _ = c * (⌊p i / c⌋ : ℝ) + c := by ring
    have h3 := abs_le.mp (hcoord p hp i)
    rw [abs_le]
    constructor <;> linarith
  have hsub : Q.image (cellOf c) ⊆
      (Q.image (fun p => ⌊p 0 / c⌋)) ×ˢ (Q.image (fun p => ⌊p 1 / c⌋)) := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hcard := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
  rw [Finset.card_product] at hcard
  push_cast at hcard
  calc ((Q.image (cellOf c)).card : ℝ)
      ≤ ((Q.image (fun p => ⌊p 0 / c⌋)).card : ℝ) * ((Q.image (fun p => ⌊p 1 / c⌋)).card : ℝ) :=
        hcard
    _ ≤ (2 * (R + c) / c + 1) * (2 * (R + c) / c + 1) :=
        mul_le_mul (hwin 0) (hwin 1) (Nat.cast_nonneg _) (by positivity)
    _ = (2 * (R + c) / c + 1) ^ 2 := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
