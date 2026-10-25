-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/Frames.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Frames.lean.

import Submission.Obl.k4_clean_cover_graph_atlas.Interface
import Submission.Lib.K4XInterface.Charts

/-!
# Sub-block and sub-box charts inside an old path chart

An old chart at time resolution `T` and block `j₀` has normalized spatial coordinates
`z_l(t) = Q⁻¹ (y_l(t) - c - t u)`, bounded by `κ` on the block. We subdivide the block into
`2^s₀` sub-blocks and bin `z_l` at the sub-block midpoint into boxes of side `ℓ = 2^{-s₀}`.
The scaled frame `ℓ Q`, centred at the box centre, is a frame of slack `κ + 1` for every
assigned line on its sub-block (`subFrame_bound`), and `gchart_subbox` assembles the new chart
from the new hidden-test facts.
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Submission.Lib.K4XInterface

/-- The normalized spatial coordinate of a line in a chart frame. -/
noncomputable def zc (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)

/-- The side `ℓ = 2^{-s₀}` of sub-boxes in normalized coordinates. -/
noncomputable def side (s₀ : ℕ) : ℝ := ((2 : ℝ) ^ s₀)⁻¹

theorem side_pos (s₀ : ℕ) : 0 < side s₀ := by unfold side; positivity

theorem side_le_one (s₀ : ℕ) : side s₀ ≤ 1 := by
  unfold side
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- The index of sub-block `jj` of block `j₀` at the finer resolution `T + s₀`. -/
def subIdx (s₀ j₀ jj : ℕ) : ℕ := j₀ * 2 ^ s₀ + jj

theorem subIdx_lt {T s₀ j₀ jj : ℕ} (hj₀ : j₀ < 2 ^ T) (hjj : jj < 2 ^ s₀) :
    subIdx s₀ j₀ jj < 2 ^ (T + s₀) := by
  unfold subIdx
  rw [pow_add]
  calc j₀ * 2 ^ s₀ + jj < j₀ * 2 ^ s₀ + 2 ^ s₀ := by omega
    _ = (j₀ + 1) * 2 ^ s₀ := by ring
    _ ≤ 2 ^ T * 2 ^ s₀ := Nat.mul_le_mul_right _ hj₀

/-- The sub-block endpoints in terms of the old block. -/
theorem subIdx_div (T s₀ j₀ jj : ℕ) :
    (subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀) = j₀ / (2 : ℝ) ^ T + jj * side s₀ / (2 : ℝ) ^ T := by
  unfold subIdx side
  push_cast
  rw [pow_add]
  field_simp

theorem subIdx_succ_div (T s₀ j₀ jj : ℕ) :
    ((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀) =
      j₀ / (2 : ℝ) ^ T + (jj + 1) * side s₀ / (2 : ℝ) ^ T := by
  unfold subIdx side
  push_cast
  rw [pow_add]
  field_simp
  ring

/-- Sub-blocks lie inside their block. -/
theorem subblock_subset {T s₀ j₀ jj : ℕ} (hjj : jj < 2 ^ s₀) :
    Set.Icc ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀))
        (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀)) ⊆
      Set.Icc ((j₀ : ℝ) / (2 : ℝ) ^ T) (((j₀ : ℝ) + 1) / (2 : ℝ) ^ T) := by
  intro t ht
  rw [subIdx_div] at ht
  rw [subIdx_succ_div] at ht
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hs := side_pos s₀
  have hjjr : ((jj : ℝ) + 1) * side s₀ ≤ 1 := by
    unfold side
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact_mod_cast hjj
  constructor
  · have : 0 ≤ (jj : ℝ) * side s₀ / (2 : ℝ) ^ T := by positivity
    linarith [ht.1]
  · have : ((jj : ℝ) + 1) * side s₀ / (2 : ℝ) ^ T ≤ 1 / (2 : ℝ) ^ T :=
      div_le_div_of_nonneg_right hjjr h2.le
    calc t ≤ _ := ht.2
      _ ≤ (j₀ : ℝ) / (2 : ℝ) ^ T + 1 / (2 : ℝ) ^ T := by linarith
      _ = ((j₀ : ℝ) + 1) / (2 : ℝ) ^ T := by ring

/-- The midpoint of a sub-block. -/
noncomputable def subMid (T s₀ j₀ jj : ℕ) : ℝ :=
  ((subIdx s₀ j₀ jj : ℝ) + 1 / 2) / (2 : ℝ) ^ (T + s₀)

/-- Points of a sub-block are within half its length of its midpoint. -/
theorem abs_sub_subMid_le {T s₀ j₀ jj : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀))
        (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀))) :
    |t - subMid T s₀ j₀ jj| ≤ side s₀ / 2 / (2 : ℝ) ^ T := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (T + s₀) := by positivity
  have hside : side s₀ / 2 / (2 : ℝ) ^ T = (1 / 2) / (2 : ℝ) ^ (T + s₀) := by
    unfold side
    rw [pow_add]
    field_simp
  rw [hside, abs_le]
  unfold subMid
  constructor
  · have := ht.1
    have e : ((subIdx s₀ j₀ jj : ℝ) + 1 / 2) / (2 : ℝ) ^ (T + s₀) =
        (subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀) + (1 / 2) / (2 : ℝ) ^ (T + s₀) := by ring
    linarith
  · have := ht.2
    have e : ((subIdx s₀ j₀ jj : ℝ) + 1 / 2) / (2 : ℝ) ^ (T + s₀) =
        ((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀) - (1 / 2) / (2 : ℝ) ^ (T + s₀) := by
      ring
    linarith

/-- The midpoint lies in the sub-block. -/
theorem subMid_mem (T s₀ j₀ jj : ℕ) :
    subMid T s₀ j₀ jj ∈ Set.Icc ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀))
        (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀)) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (T + s₀) := by positivity
  unfold subMid
  constructor
  · exact div_le_div_of_nonneg_right (by linarith) h2.le
  · exact div_le_div_of_nonneg_right (by linarith) h2.le

/-- Box membership of a normalized position: `k ℓ ≤ z < (k+1) ℓ` in both coordinates. -/
def inBox (s₀ : ℕ) (k : Fin 2 → ℤ) (z : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ e : Fin 2, (k e : ℝ) * side s₀ ≤ z e ∧ z e < ((k e : ℝ) + 1) * side s₀

/-- The box centre. -/
noncomputable def boxCenter (s₀ : ℕ) (k : Fin 2 → ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun e => ((k e : ℝ) + 1 / 2) * side s₀)

theorem norm_sub_boxCenter_le {s₀ : ℕ} {k : Fin 2 → ℤ} {z : EuclideanSpace ℝ (Fin 2)}
    (hz : inBox s₀ k z) : ‖z - boxCenter s₀ k‖ ≤ side s₀ := by
  have hs := side_pos s₀
  have hc : ∀ e : Fin 2, |(z - boxCenter s₀ k) e| ≤ side s₀ / 2 := by
    intro e
    obtain ⟨h1, h2⟩ := hz e
    simp only [boxCenter, PiLp.sub_apply]
    rw [abs_le]
    constructor <;> nlinarith
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left hs.le]
  rw [Fin.sum_univ_two]
  have h0 := hc 0
  have h1 := hc 1
  have e0 : ‖(z - boxCenter s₀ k) 0‖ ^ 2 ≤ (side s₀ / 2) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    exact sq_le_sq' (abs_le.mp h0).1 (abs_le.mp h0).2
  have e1 : ‖(z - boxCenter s₀ k) 1‖ ^ 2 ≤ (side s₀ / 2) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    exact sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  nlinarith

/-- The scaled sub-box frame `Q * (ℓ • 1)`. -/
noncomputable def subFrame (Q : Matrix (Fin 2) (Fin 2) ℝ) (s₀ : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Q * (side s₀ • (1 : Matrix (Fin 2) (Fin 2) ℝ))

theorem subFrame_eq (Q : Matrix (Fin 2) (Fin 2) ℝ) (s₀ : ℕ) : subFrame Q s₀ = side s₀ • Q := by
  unfold subFrame
  rw [Matrix.mul_smul, Matrix.mul_one]

theorem det_scalar_ne_zero (s₀ : ℕ) : (side s₀ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ (side_pos s₀).ne'

/-- The scaled frame is a frame of slack `κ + 1` on the sub-block, for every line of the old
chart whose midpoint position lies in the box. -/
theorem subFrame_bound {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j₀ : ℕ} {r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T (j₀ : ℝ) r Bv Ev c u Q R A F ex) {s₀ jj : ℕ} {k : Fin 2 → ℤ}
    {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ A) (hbox : inBox s₀ k (zc Q c u l (subMid T s₀ j₀ jj)))
    {t : ℝ} (ht : t ∈ Set.Icc ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀))
        (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀))) :
    ‖Matrix.toEuclideanLin (subFrame Q s₀)⁻¹
        (gy l t - (c + Matrix.toEuclideanLin Q (boxCenter s₀ k)) - t • u)‖ ≤ κ + 1 := by
  have hdet : Q.det ≠ 0 := h.1
  have hs := side_pos s₀
  have hv := gchart_velocity h hl
  have h2T : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  -- write the frame as a composition with the scalar frame
  have hcomp := frame_comp_apply Q (side s₀ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) hdet
    (det_scalar_ne_zero s₀) (gy l t) c u (boxCenter s₀ k) 0 t
  simp only [map_zero, add_zero, smul_zero, sub_zero] at hcomp
  unfold subFrame
  rw [hcomp]
  have hsc : (side s₀ • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ = (side s₀)⁻¹ • 1 := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hs.ne',
      one_smul]
  rw [hsc]
  have happ : ∀ w : EuclideanSpace ℝ (Fin 2),
      Matrix.toEuclideanLin ((side s₀)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) w = (side s₀)⁻¹ • w := by
    intro w
    rw [map_smul, Matrix.toLpLin_one]
    rfl
  rw [happ, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
  -- the normalized position moves by at most `ℓ κ` from the midpoint
  set tm := subMid T s₀ j₀ jj
  have hz : zc Q c u l t = zc Q c u l tm + (t - tm) • Matrix.toEuclideanLin Q⁻¹ (gv l - u) := by
    unfold zc
    rw [gy_offset_eq l c u tm t, map_add, map_smul]
  have hmove : ‖(t - tm) • Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ ≤ side s₀ * κ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hd := abs_sub_subMid_le ht
    calc |t - tm| * ‖Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖
        ≤ side s₀ / 2 / (2 : ℝ) ^ T * (2 * κ * (2 : ℝ) ^ T) :=
          mul_le_mul hd hv (norm_nonneg _) (by positivity)
      _ = side s₀ * κ := by field_simp
  have hcen := norm_sub_boxCenter_le hbox
  have htot : ‖Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u) - boxCenter s₀ k‖ ≤
      side s₀ * (κ + 1) := by
    change ‖zc Q c u l t - boxCenter s₀ k‖ ≤ _
    rw [hz]
    calc ‖zc Q c u l tm + (t - tm) • Matrix.toEuclideanLin Q⁻¹ (gv l - u) - boxCenter s₀ k‖
        = ‖(zc Q c u l tm - boxCenter s₀ k) + (t - tm) • Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ := by
          congr 1; abel
      _ ≤ ‖zc Q c u l tm - boxCenter s₀ k‖ + ‖(t - tm) • Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ :=
          norm_add_le _ _
      _ ≤ side s₀ + side s₀ * κ := add_le_add hcen hmove
      _ = side s₀ * (κ + 1) := by ring
  calc (side s₀)⁻¹ * ‖Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u) - boxCenter s₀ k‖
      ≤ (side s₀)⁻¹ * (side s₀ * (κ + 1)) :=
        mul_le_mul_of_nonneg_left htot (inv_nonneg.mpr hs.le)
    _ = κ + 1 := by field_simp

theorem det_subFrame_ne_zero {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) (s₀ : ℕ) :
    (subFrame Q s₀).det ≠ 0 := by
  unfold subFrame
  rw [Matrix.det_mul]
  exact mul_ne_zero hQ (det_scalar_ne_zero s₀)

theorem sum_abs_smul_fin2 (a : ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ e : Fin 2, ∑ e' : Fin 2, |(a • Q) e e'|) = |a| * ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| := by
  simp [Fin.sum_univ_two, abs_mul]
  ring

/-- The entry sum of the scaled frame. -/
theorem sum_abs_subFrame (Q : Matrix (Fin 2) (Fin 2) ℝ) (s₀ : ℕ) :
    (∑ e : Fin 2, ∑ e' : Fin 2, |subFrame Q s₀ e e'|) =
      side s₀ * ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| := by
  rw [subFrame_eq, sum_abs_smul_fin2, abs_of_pos (side_pos s₀)]

/-- The entry sum of the inverse scaled frame. -/
theorem sum_abs_subFrame_inv {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) (s₀ : ℕ) :
    (∑ e : Fin 2, ∑ e' : Fin 2, |(subFrame Q s₀)⁻¹ e e'|) =
      (side s₀)⁻¹ * ∑ e : Fin 2, ∑ e' : Fin 2, |Q⁻¹ e e'| := by
  have hs := side_pos s₀
  have hinv : (subFrame Q s₀)⁻¹ = (side s₀)⁻¹ • Q⁻¹ := by
    rw [subFrame_eq]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ),
      smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  rw [hinv, sum_abs_smul_fin2, abs_of_pos (inv_pos.mpr hs)]

theorem one_le_inv_side (s₀ : ℕ) : 1 ≤ (side s₀)⁻¹ := by
  unfold side
  rw [inv_inv]
  exact one_le_pow₀ (by norm_num)

/-- Frame complexity of the scaled frame. -/
theorem subFrame_complexity_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) (s₀ : ℕ) {H : ℝ}
    (h : (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ H) :
    (∑ e : Fin 2, ∑ e' : Fin 2, (|subFrame Q s₀ e e'| + |(subFrame Q s₀)⁻¹ e e'|)) ≤
      (side s₀)⁻¹ * H := by
  have hs := side_pos s₀
  have h1 := one_le_inv_side s₀
  have hsplit : ∀ P : Matrix (Fin 2) (Fin 2) ℝ, (∑ e : Fin 2, ∑ e' : Fin 2, (|P e e'| + |P⁻¹ e e'|)) =
      (∑ e : Fin 2, ∑ e' : Fin 2, |P e e'|) + ∑ e : Fin 2, ∑ e' : Fin 2, |P⁻¹ e e'| := by
    intro P
    simp only [Fin.sum_univ_two]
    ring
  rw [hsplit] at h ⊢
  rw [sum_abs_subFrame, sum_abs_subFrame_inv hQ]
  have hQn : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| := by positivity
  have hQin : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |Q⁻¹ e e'| := by positivity
  have hsl : side s₀ ≤ (side s₀)⁻¹ := (side_le_one s₀).trans h1
  calc side s₀ * (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) +
        (side s₀)⁻¹ * ∑ e : Fin 2, ∑ e' : Fin 2, |Q⁻¹ e e'|
      ≤ (side s₀)⁻¹ * (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) +
        (side s₀)⁻¹ * ∑ e : Fin 2, ∑ e' : Fin 2, |Q⁻¹ e e'| := by gcongr
    _ = (side s₀)⁻¹ * ((∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) +
        ∑ e : Fin 2, ∑ e' : Fin 2, |Q⁻¹ e e'|) := by ring
    _ ≤ (side s₀)⁻¹ * H := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs.le)

/-- A matrix acting on the plane is bounded by its entry sum. -/
theorem norm_toEuclideanLin_le_sum (Q : Matrix (Fin 2) (Fin 2) ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    ‖Matrix.toEuclideanLin Q w‖ ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) * ‖w‖ := by
  have hw0 : |w 0| ≤ ‖w‖ := by
    have := PiLp.norm_apply_le w 0
    simpa [Real.norm_eq_abs] using this
  have hw1 : |w 1| ≤ ‖w‖ := by
    have := PiLp.norm_apply_le w 1
    simpa [Real.norm_eq_abs] using this
  have hwn := norm_nonneg w
  have r0 : |Q 0 0 * w 0 + Q 0 1 * w 1| ≤ (|Q 0 0| + |Q 0 1|) * ‖w‖ := by
    calc |Q 0 0 * w 0 + Q 0 1 * w 1| ≤ |Q 0 0| * |w 0| + |Q 0 1| * |w 1| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (|Q 0 0| + |Q 0 1|) * ‖w‖ := by
          nlinarith [abs_nonneg (Q 0 0), abs_nonneg (Q 0 1)]
  have r1 : |Q 1 0 * w 0 + Q 1 1 * w 1| ≤ (|Q 1 0| + |Q 1 1|) * ‖w‖ := by
    calc |Q 1 0 * w 0 + Q 1 1 * w 1| ≤ |Q 1 0| * |w 0| + |Q 1 1| * |w 1| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (|Q 1 0| + |Q 1 1|) * ‖w‖ := by
          nlinarith [abs_nonneg (Q 1 0), abs_nonneg (Q 1 1)]
  calc ‖Matrix.toEuclideanLin Q w‖ ≤ (|Q 0 0| + |Q 0 1|) * ‖w‖ + (|Q 1 0| + |Q 1 1|) * ‖w‖ :=
        norm_le_of_rows Q w r0 r1
    _ = (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) * ‖w‖ := by
        simp only [Fin.sum_univ_two]; ring

/-- The box centre of an occupied box is close to an assigned position. -/
theorem norm_boxCenter_le {s₀ : ℕ} {k : Fin 2 → ℤ} {z : EuclideanSpace ℝ (Fin 2)}
    (hz : inBox s₀ k z) : ‖boxCenter s₀ k‖ ≤ ‖z‖ + 1 := by
  have := norm_sub_boxCenter_le hz
  have h1 := side_le_one s₀
  calc ‖boxCenter s₀ k‖ = ‖z - (z - boxCenter s₀ k)‖ := by congr 1; abel
    _ ≤ ‖z‖ + ‖z - boxCenter s₀ k‖ := norm_sub_le _ _
    _ ≤ ‖z‖ + 1 := by linarith

/-- The new centre of an occupied box. -/
theorem subCenter_norm_le {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j₀ : ℕ} {r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T (j₀ : ℝ) r Bv Ev c u Q R A F ex) {s₀ jj : ℕ} (hjj : jj < 2 ^ s₀)
    {k : Fin 2 → ℤ} {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ A)
    (hbox : inBox s₀ k (zc Q c u l (subMid T s₀ j₀ jj))) :
    ‖c + Matrix.toEuclideanLin Q (boxCenter s₀ k)‖ + ‖u‖ ≤ Nk ^ M + κ * (κ + 1) := by
  obtain ⟨-, hcu, -, hQs, -, -, -, -, -, hAl, -⟩ := h
  have h2T : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hQs' : (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ := by
    have h1 : 1 ≤ (2 : ℝ) ^ T := one_le_pow₀ (by norm_num)
    have hκ : 0 ≤ κ := by
      have := (hAl l hl).2.2 (subMid T s₀ j₀ jj) (subblock_subset hjj (subMid_mem T s₀ j₀ jj))
      exact (norm_nonneg _).trans this.1
    calc _ ≤ κ / (2 : ℝ) ^ T := hQs
      _ ≤ κ := div_le_self hκ h1
  have hz : ‖zc Q c u l (subMid T s₀ j₀ jj)‖ ≤ κ :=
    ((hAl l hl).2.2 _ (subblock_subset hjj (subMid_mem T s₀ j₀ jj))).1
  have hb := norm_boxCenter_le hbox
  have hκ : 0 ≤ κ := (norm_nonneg _).trans hz
  calc ‖c + Matrix.toEuclideanLin Q (boxCenter s₀ k)‖ + ‖u‖
      ≤ ‖c‖ + ‖Matrix.toEuclideanLin Q (boxCenter s₀ k)‖ + ‖u‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ‖c‖ + κ * (κ + 1) + ‖u‖ := by
        gcongr
        calc ‖Matrix.toEuclideanLin Q (boxCenter s₀ k)‖
            ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) * ‖boxCenter s₀ k‖ :=
              norm_toEuclideanLin_le_sum Q _
          _ ≤ κ * (κ + 1) := mul_le_mul hQs' (hb.trans (by linarith)) (norm_nonneg _) hκ
    _ ≤ Nk ^ M + κ * (κ + 1) := by linarith

/-- **The sub-box chart.** An old path chart, a sub-block and a box of side `2^{-s₀}`, and a new
test with the required hidden bounds on a sub-assignment of lines whose midpoint position lies in
the box, give a chart at the finer resolution `T + s₀` with the scaled frame. -/
theorem gchart_subbox {Nk : ℝ} {M D M' D' : ℕ} {κ κ' : ℝ} {T : ℕ} {j₀ : ℕ} {r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T (j₀ : ℝ) r Bv Ev c u Q R A F ex) (hNk : 1 ≤ Nk) (hM : M ≤ M')
    {s₀ jj : ℕ} (hjj : jj < 2 ^ s₀) {k : Fin 2 → ℤ} (hκ' : κ + 1 ≤ κ')
    (R₂ : MvPolynomial (Fin 4) ℝ) (r₂ : ℝ) (A₂ : Set (ℕ × (Fin 6 → ℝ)))
    (F₂ : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hA₂ : ∀ l ∈ A₂, l ∈ A ∧ inBox s₀ k (zc Q c u l (subMid T s₀ j₀ jj)))
    (htests : ∀ l ∈ A₂, ∀ t ∈ Set.Icc ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀))
        (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀)),
      |MvPolynomial.eval (gx l t) R₂| ≤ κ' * gδ Nk r₂ ∧
      |MvPolynomial.eval (gx l t) (MvPolynomial.pderiv (3 : Fin 4) R₂)| ≤ κ' * Bv ∧
      |MvPolynomial.eval (gx l t)
          (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R₂))| ≤
        κ' * Bv ^ 2 / gδ Nk r₂)
    (hF₂ : ∀ p ∈ F₂, p ∈ Ev ∧ p.1 ∈ A₂ ∧
      p.2 ∈ Set.Icc ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀))
        (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀)) ∧
      Bv / κ' ≤ |MvPolynomial.eval (gx p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R₂)|)
    (hdeg : R₂.totalDegree ≤ 2) (hcoef : ∀ e, |R₂.coeff e| ≤ Nk ^ M')
    (hmA : MeasurableSet A₂) (hmF : MeasurableSet F₂)
    (hfmt : ∀ i, gfmt 6 (Nk ^ M') D' {x | (i, x) ∈ A₂} ∧
      gfmt 7 (Nk ^ M') D' {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F₂})
    (hcu : ‖c + Matrix.toEuclideanLin Q (boxCenter s₀ k)‖ + ‖u‖ ≤ Nk ^ M')
    (hfr : (∑ e : Fin 2, ∑ e' : Fin 2, (|subFrame Q s₀ e e'| + |(subFrame Q s₀)⁻¹ e e'|)) ≤
      Nk ^ M') :
    gchart Nk M' D' κ' (T + s₀) (subIdx s₀ j₀ jj : ℝ) r₂ Bv Ev
      (c + Matrix.toEuclideanLin Q (boxCenter s₀ k)) u (subFrame Q s₀) R₂ A₂ F₂ True := by
  have hdet : Q.det ≠ 0 := h.1
  have hpow : Nk ^ M ≤ Nk ^ M' := pow_le_pow_right₀ hNk hM
  have h0 := h
  obtain ⟨-, -, -, hQs, -, -, -, -, -, hAl, -⟩ := h0
  refine ⟨det_subFrame_ne_zero hdet s₀, hcu, hfr, ?_, hdeg, hcoef, hmA, hmF, hfmt, ?_, hF₂, trivial⟩
  · rw [sum_abs_subFrame]
    have hs := side_pos s₀
    have hκ : 0 ≤ κ := by
      by_contra hneg
      push Not at hneg
      have : (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) < 0 :=
        lt_of_le_of_lt hQs (div_neg_of_neg_of_pos hneg (by positivity))
      exact absurd this (not_lt.mpr (by positivity))
    calc side s₀ * (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ side s₀ * (κ / (2 : ℝ) ^ T) :=
          mul_le_mul_of_nonneg_left hQs hs.le
      _ = κ / (2 : ℝ) ^ (T + s₀) := by unfold side; rw [pow_add]; field_simp
      _ ≤ κ' / (2 : ℝ) ^ (T + s₀) := div_le_div_of_nonneg_right (by linarith) (by positivity)
  · intro l hl
    obtain ⟨hlA, hbox⟩ := hA₂ l hl
    obtain ⟨h1, h2, -⟩ := hAl l hlA
    refine ⟨h1.trans hpow, fun e => (h2 e).trans hpow, fun t ht => ?_⟩
    obtain ⟨a1, a2, a3⟩ := htests l hl t ht
    have hfr' := subFrame_bound h hlA hbox ht
    exact ⟨hfr'.trans hκ', a1, a2, a3⟩

end Submission.Obl.k4_clean_cover_graph_atlas
