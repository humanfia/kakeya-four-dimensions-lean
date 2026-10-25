-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/RegionGeometry.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.PacketCoords
import Submission.Obl.k4_clean_cover_graph_atlas.Entries

/-!
# Comparison regions of entries

For an old chart at resolution `T`, block `j₀`, a sub-block `jj` and a box `k`, the normalized base
point `(2^T t - j₀, z_l(t))` of every line of the chart whose midpoint position lies in the box
stays within `(κ + 2) 2^{-s₀}` of the box centre `(s_mid, z_box)` on the whole sub-block
(`normBase_near_center`). Here `s_mid = (jj + 1/2) 2^{-s₀}`.
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The normalized base point of a line at a time, as a point of `ℝ³`. -/
noncomputable def normBase (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 ^ T * t - j, (zc Q c u l t) 0, (zc Q c u l t) 1]

/-- The centre of a sub-box in normalized coordinates. -/
noncomputable def subBoxCenter (s₀ jj : ℕ) (k : Fin 2 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![((jj : ℝ) + 1 / 2) * side s₀, (boxCenter s₀ k) 0, (boxCenter s₀ k) 1]

theorem normBase_eq_init (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    (fun i : Fin 3 => normBase T j c u Q l t i) = Fin.init (normPt T j c u Q B l t) := by
  funext i
  fin_cases i <;> simp [normBase, normPt, Fin.init]

/-- The normalized time of a point of the sub-block is within `ℓ/2` of the sub-block midpoint. -/
theorem normTime_near_mid {T s₀ j₀ jj : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀))
      (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀))) :
    |(2 ^ T * t - j₀) - ((jj : ℝ) + 1 / 2) * side s₀| ≤ side s₀ / 2 := by
  have h := abs_sub_subMid_le ht
  have h2 : (0 : ℝ) < 2 ^ T := by positivity
  have hmid : 2 ^ T * subMid T s₀ j₀ jj - j₀ = ((jj : ℝ) + 1 / 2) * side s₀ := by
    unfold subMid subIdx side
    push_cast
    rw [pow_add]
    field_simp
    ring
  rw [← hmid]
  have e : (2 ^ T * t - j₀) - (2 ^ T * subMid T s₀ j₀ jj - j₀) = 2 ^ T * (t - subMid T s₀ j₀ jj) := by
    ring
  rw [e, abs_mul, abs_of_pos h2]
  calc 2 ^ T * |t - subMid T s₀ j₀ jj| ≤ 2 ^ T * (side s₀ / 2 / 2 ^ T) :=
        mul_le_mul_of_nonneg_left h h2.le
    _ = side s₀ / 2 := by field_simp

/-- The normalized spatial point stays within `ℓ (κ + 1)` of the box centre. -/
theorem zc_near_boxCenter {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j₀ : ℕ} {r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T (j₀ : ℝ) r Bv Ev c u Q R A F ex) {s₀ jj : ℕ} {k : Fin 2 → ℤ}
    {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ A) (hbox : inBox s₀ k (zc Q c u l (subMid T s₀ j₀ jj)))
    {t : ℝ} (ht : t ∈ Set.Icc ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀))
        (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀))) :
    ‖zc Q c u l t - boxCenter s₀ k‖ ≤ side s₀ * (κ + 1) := by
  have hv := gchart_velocity h hl
  set tm := subMid T s₀ j₀ jj
  have hz : zc Q c u l t = zc Q c u l tm + (t - tm) • Matrix.toEuclideanLin Q⁻¹ (gv l - u) := by
    unfold zc
    rw [gy_offset_eq l c u tm t, map_add, map_smul]
  have hmove : ‖(t - tm) • Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ ≤ side s₀ * κ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hd := abs_sub_subMid_le ht
    calc |t - tm| * ‖Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖
        ≤ side s₀ / 2 / (2 : ℝ) ^ T * (2 * κ * (2 : ℝ) ^ T) :=
          mul_le_mul hd hv (norm_nonneg _)
            (div_nonneg (div_nonneg (side_pos s₀).le (by norm_num)) (by positivity))
      _ = side s₀ * κ := by field_simp
  have hcen := norm_sub_boxCenter_le hbox
  rw [hz]
  calc ‖zc Q c u l tm + (t - tm) • Matrix.toEuclideanLin Q⁻¹ (gv l - u) - boxCenter s₀ k‖
      = ‖(zc Q c u l tm - boxCenter s₀ k) + (t - tm) • Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ := by
        congr 1; abel
    _ ≤ ‖zc Q c u l tm - boxCenter s₀ k‖ + ‖(t - tm) • Matrix.toEuclideanLin Q⁻¹ (gv l - u)‖ :=
        norm_add_le _ _
    _ ≤ side s₀ + side s₀ * κ := add_le_add hcen hmove
    _ = side s₀ * (κ + 1) := by ring

/-- **The comparison region.** On its sub-block, the normalized base point of a line whose
midpoint position lies in the box stays within `(κ + 2) ℓ` of the sub-box centre. -/
theorem normBase_near_center {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j₀ : ℕ} {r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T (j₀ : ℝ) r Bv Ev c u Q R A F ex) {s₀ jj : ℕ} {k : Fin 2 → ℤ}
    {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ A) (hbox : inBox s₀ k (zc Q c u l (subMid T s₀ j₀ jj)))
    {t : ℝ} (ht : t ∈ Set.Icc ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀))
        (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀))) :
    ‖normBase T j₀ c u Q l t - subBoxCenter s₀ jj k‖ ≤ side s₀ * (κ + 2) := by
  have h1 := normTime_near_mid ht
  have h2 := zc_near_boxCenter h hl hbox ht
  have hs := side_pos s₀
  -- coordinatewise bounds
  have hz0 : |(zc Q c u l t - boxCenter s₀ k) 0| ≤ side s₀ * (κ + 1) := by
    have := PiLp.norm_apply_le (zc Q c u l t - boxCenter s₀ k) 0
    rw [Real.norm_eq_abs] at this
    exact this.trans h2
  have hz1 : |(zc Q c u l t - boxCenter s₀ k) 1| ≤ side s₀ * (κ + 1) := by
    have := PiLp.norm_apply_le (zc Q c u l t - boxCenter s₀ k) 1
    rw [Real.norm_eq_abs] at this
    exact this.trans h2
  have hsq : ‖zc Q c u l t - boxCenter s₀ k‖ ^ 2 =
      (zc Q c u l t - boxCenter s₀ k) 0 ^ 2 + (zc Q c u l t - boxCenter s₀ k) 1 ^ 2 :=
    norm_sq_fin2 _
  have hκ : 0 ≤ κ + 1 := by
    have := (norm_nonneg _).trans h2
    nlinarith
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (mul_nonneg hs.le (by linarith))]
  rw [Fin.sum_univ_three]
  simp only [normBase, subBoxCenter, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have e0 := abs_le.mp h1
  have hz0' : ((zc Q c u l t) 0 - (boxCenter s₀ k) 0) ^ 2 + ((zc Q c u l t) 1 - (boxCenter s₀ k) 1) ^ 2
      ≤ (side s₀ * (κ + 1)) ^ 2 := by
    have := h2
    have hn : ‖zc Q c u l t - boxCenter s₀ k‖ ^ 2 ≤ (side s₀ * (κ + 1)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [hsq] at hn
    simpa [PiLp.sub_apply] using hn
  have e0' : ((2 : ℝ) ^ T * t - j₀ - ((jj : ℝ) + 1 / 2) * side s₀) ^ 2 ≤ (side s₀ / 2) ^ 2 :=
    sq_le_sq' (by linarith [e0.1]) (by linarith [e0.2])
  have hfin : (side s₀ / 2) ^ 2 + (side s₀ * (κ + 1)) ^ 2 ≤ (side s₀ * (κ + 2)) ^ 2 := by
    nlinarith [sq_nonneg (side s₀), mul_nonneg (sq_nonneg (side s₀)) hκ]
  nlinarith

end Submission.Obl.k4_clean_cover_graph_atlas
