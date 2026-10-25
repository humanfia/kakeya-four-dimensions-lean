-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.Transverse; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254, session x0900; uses the accepted library
   Submission.Lib.K4HiddenQuadratic (eval_update_add, eval_pderiv_pderiv_eq) and
   Submission.Obl.k4_scalar_grid_parameter_preparation.PolynomialLipschitz of this checkout. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Setup
import Submission.Lib.K4HiddenQuadratic
import Submission.Obl.k4_scalar_grid_parameter_preparation.PolynomialLipschitz
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Kernels.CoefficientAgreement

/-!
# Transverse expansion of projected quadratics

For a projected quadratic `G(t, Y)` of total degree at most two and a tilted transverse
center `Y(t, Z)`, the value on the tilted plane `Y(t, Z) + w U` is exactly
`transA + transB U + transD U²` (`agree_eval_tilted`). The coefficients `transA`, `transB` are
Lipschitz in the base point (`agree_transA_sub_le`, `agree_transB_sub_le`) and bounded
(`agree_transB_abs_le`, `agree_transD_abs_le`) in terms of a coefficient bound of `G`.

`agree_tilted_match`: two incidences whose native signals agree, each fitted by its own quadratic
and offset, give frozen transverse quadratics that agree up to the offset difference.
`agree_gap_of_pair_disagree`: a disagreement of two transverse pairs at a nearby point is a
nonconstant coefficient gap of the frozen quadratics.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MvPolynomial

noncomputable section

/-- **Exact transverse expansion** of a projected quadratic on the tilted plane. -/
theorem agree_eval_tilted (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) (Y : ℝ → ℝ → ℝ)
    (w t Z U : ℝ) :
    eval ![t, Y t Z + w * U] G = transA G Y t Z + transB G Y w t Z * U + transD G w * U ^ 2 := by
  have h := Submission.Lib.K4HiddenQuadratic.eval_update_add G hG ![t, Y t Z] 1 (w * U)
  have hv : Function.update ![t, Y t Z] 1 (![t, Y t Z] 1 + w * U) = ![t, Y t Z + w * U] := by
    ext i
    fin_cases i <;> simp [Function.update]
  rw [hv] at h
  rw [h, Submission.Lib.K4HiddenQuadratic.eval_pderiv_pderiv_eq G hG 1 ![t, Y t Z] ![0, 0]]
  simp only [transA, transB, transD]
  ring

/-- The partial derivative of a quadratic is of total degree at most two. -/
theorem agree_totalDegree_pderiv_le_two (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    (i : Fin 2) : (pderiv i G).totalDegree ≤ 2 :=
  (Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred G i).trans (by omega)

/-- The coefficients of a partial derivative of a quadratic are bounded by three times
those of the quadratic. -/
theorem agree_pderiv_coeff_le_three (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    {B : ℝ} (hB : 0 ≤ B) (hc : ∀ b, |G.coeff b| ≤ B) (i : Fin 2) :
    ∀ b, |(pderiv i G).coeff b| ≤ 3 * B := by
  intro b
  have h := Submission.Obl.k4_scalar_grid_parameter_preparation.pderiv_coefficients_bound
    G 2 hG hB hc i b
  norm_num at h
  linarith

/-- The distance of two points of the plane is at most the sum of the coordinate differences. -/
theorem agree_dist_pair_le (t Y t' Y' : ℝ) :
    dist (![t, Y] : Fin 2 → ℝ) ![t', Y'] ≤ |t - t'| + |Y - Y'| := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  fin_cases i
  · simp only [Real.dist_eq, Fin.zero_eta, Matrix.cons_val_zero]
    linarith [abs_nonneg (Y - Y')]
  · simp only [Real.dist_eq, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith [abs_nonneg (t - t')]

/-- Coordinates of a bounded planar point. -/
theorem agree_pair_coord_le {t Y R : ℝ} (ht : |t| ≤ R) (hY : |Y| ≤ R) :
    ∀ i, |(![t, Y] : Fin 2 → ℝ) i| ≤ R := by
  intro i
  fin_cases i
  · simpa using ht
  · simpa using hY

/-- Lipschitz bound of the transverse constant coefficient in the base point. -/
theorem agree_transA_sub_le (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) {B R : ℝ}
    (hB : 0 ≤ B) (hR : 1 ≤ R) (hc : ∀ b, |G.coeff b| ≤ B) (Y : ℝ → ℝ → ℝ)
    {t Z t' Z' : ℝ} (ht : |t| ≤ R) (ht' : |t'| ≤ R) (hY : |Y t Z| ≤ R) (hY' : |Y t' Z'| ≤ R) :
    |transA G Y t Z - transA G Y t' Z'| ≤ 54 * B * R ^ 4 * (|t - t'| + |Y t Z - Y t' Z'|) := by
  have h := Submission.Obl.k4_scalar_grid_parameter_preparation.binary_polynomial_lipschitz
    G 2 hG hB hR hc ![t, Y t Z] ![t', Y t' Z'] (agree_pair_coord_le ht hY) (agree_pair_coord_le ht' hY')
  have hd := agree_dist_pair_le t (Y t Z) t' (Y t' Z')
  have hpos : 0 ≤ 2 * ((2 : ℕ) + 1 : ℝ) ^ 3 * B * R ^ (2 * 2) := by
    have : 0 ≤ R := by linarith
    positivity
  calc
    |transA G Y t Z - transA G Y t' Z'| ≤
        2 * ((2 : ℕ) + 1 : ℝ) ^ 3 * B * R ^ (2 * 2) * dist (![t, Y t Z] : Fin 2 → ℝ)
          ![t', Y t' Z'] := h
    _ ≤ 2 * ((2 : ℕ) + 1 : ℝ) ^ 3 * B * R ^ (2 * 2) * (|t - t'| + |Y t Z - Y t' Z'|) :=
      mul_le_mul_of_nonneg_left hd hpos
    _ = 54 * B * R ^ 4 * (|t - t'| + |Y t Z - Y t' Z'|) := by push_cast; ring

/-- Lipschitz bound of the transverse slope coefficient in the base point. -/
theorem agree_transB_sub_le (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) {B R : ℝ}
    (hB : 0 ≤ B) (hR : 1 ≤ R) (hc : ∀ b, |G.coeff b| ≤ B) (Y : ℝ → ℝ → ℝ)
    {t Z t' Z' : ℝ} (ht : |t| ≤ R) (ht' : |t'| ≤ R) (hY : |Y t Z| ≤ R) (hY' : |Y t' Z'| ≤ R)
    (w : ℝ) :
    |transB G Y w t Z - transB G Y w t' Z'| ≤
      162 * B * R ^ 4 * |w| * (|t - t'| + |Y t Z - Y t' Z'|) := by
  have h := Submission.Obl.k4_scalar_grid_parameter_preparation.binary_polynomial_lipschitz
    (pderiv 1 G) 2 (agree_totalDegree_pderiv_le_two G hG 1) (by linarith : (0 : ℝ) ≤ 3 * B) hR
    (agree_pderiv_coeff_le_three G hG hB hc 1) ![t, Y t Z] ![t', Y t' Z']
    (agree_pair_coord_le ht hY) (agree_pair_coord_le ht' hY')
  have hd := agree_dist_pair_le t (Y t Z) t' (Y t' Z')
  have hpos : 0 ≤ 2 * ((2 : ℕ) + 1 : ℝ) ^ 3 * (3 * B) * R ^ (2 * 2) := by
    have : 0 ≤ R := by linarith
    positivity
  have h' : |eval ![t, Y t Z] (pderiv 1 G) - eval ![t', Y t' Z'] (pderiv 1 G)| ≤
      162 * B * R ^ 4 * (|t - t'| + |Y t Z - Y t' Z'|) := by
    calc
      _ ≤ 2 * ((2 : ℕ) + 1 : ℝ) ^ 3 * (3 * B) * R ^ (2 * 2) *
          dist (![t, Y t Z] : Fin 2 → ℝ) ![t', Y t' Z'] := h
      _ ≤ 2 * ((2 : ℕ) + 1 : ℝ) ^ 3 * (3 * B) * R ^ (2 * 2) *
          (|t - t'| + |Y t Z - Y t' Z'|) := mul_le_mul_of_nonneg_left hd hpos
      _ = 162 * B * R ^ 4 * (|t - t'| + |Y t Z - Y t' Z'|) := by push_cast; ring
  have heq : transB G Y w t Z - transB G Y w t' Z' =
      w * (eval ![t, Y t Z] (pderiv 1 G) - eval ![t', Y t' Z'] (pderiv 1 G)) := by
    simp only [transB]
    ring
  rw [heq, abs_mul]
  calc
    |w| * |eval ![t, Y t Z] (pderiv 1 G) - eval ![t', Y t' Z'] (pderiv 1 G)| ≤
        |w| * (162 * B * R ^ 4 * (|t - t'| + |Y t Z - Y t' Z'|)) :=
      mul_le_mul_of_nonneg_left h' (abs_nonneg w)
    _ = 162 * B * R ^ 4 * |w| * (|t - t'| + |Y t Z - Y t' Z'|) := by ring

/-- Size of the transverse slope coefficient. -/
theorem agree_transB_abs_le (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) {B R : ℝ}
    (hB : 0 ≤ B) (hR : 1 ≤ R) (hc : ∀ b, |G.coeff b| ≤ B) (Y : ℝ → ℝ → ℝ) (w : ℝ)
    {t Z : ℝ} (ht : |t| ≤ R) (hY : |Y t Z| ≤ R) :
    |transB G Y w t Z| ≤ 27 * B * R ^ 4 * |w| := by
  have h := Submission.Obl.k4_scalar_grid_parameter_preparation.binary_polynomial_eval_bound
    (pderiv 1 G) 2 (agree_totalDegree_pderiv_le_two G hG 1) (by linarith : (0 : ℝ) ≤ 3 * B) hR
    (agree_pderiv_coeff_le_three G hG hB hc 1) ![t, Y t Z] (agree_pair_coord_le ht hY)
  have h' : |eval ![t, Y t Z] (pderiv 1 G)| ≤ 27 * B * R ^ 4 := by
    calc
      _ ≤ ((2 : ℕ) + 1 : ℝ) ^ 2 * (3 * B) * R ^ (2 * 2) := h
      _ = 27 * B * R ^ 4 := by push_cast; ring
  simp only [transB, abs_mul]
  calc
    |w| * |eval ![t, Y t Z] (pderiv 1 G)| ≤ |w| * (27 * B * R ^ 4) :=
      mul_le_mul_of_nonneg_left h' (abs_nonneg w)
    _ = 27 * B * R ^ 4 * |w| := by ring

/-- Size of the transverse curvature coefficient. -/
theorem agree_transD_abs_le (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) {B : ℝ}
    (hB : 0 ≤ B) (hc : ∀ b, |G.coeff b| ≤ B) (w : ℝ) :
    |transD G w| ≤ 81 * B * w ^ 2 := by
  have hc2 : ∀ b, |(pderiv 1 (pderiv 1 G)).coeff b| ≤ 3 * (3 * B) :=
    agree_pderiv_coeff_le_three (pderiv 1 G) (agree_totalDegree_pderiv_le_two G hG 1)
      (by linarith : (0 : ℝ) ≤ 3 * B) (agree_pderiv_coeff_le_three G hG hB hc 1) 1
  have h := Submission.Obl.k4_scalar_grid_parameter_preparation.binary_polynomial_eval_bound
    (pderiv 1 (pderiv 1 G)) 2
    (agree_totalDegree_pderiv_le_two (pderiv 1 G) (agree_totalDegree_pderiv_le_two G hG 1) 1)
    (by linarith : (0 : ℝ) ≤ 3 * (3 * B)) le_rfl hc2 ![0, 0]
    (agree_pair_coord_le (by simp) (by simp))
  have h' : |eval ![0, 0] (pderiv 1 (pderiv 1 G))| ≤ 81 * B := by
    calc
      _ ≤ ((2 : ℕ) + 1 : ℝ) ^ 2 * (3 * (3 * B)) * 1 ^ (2 * 2) := h
      _ = 81 * B := by push_cast; ring
  simp only [transD, abs_mul]
  have hw : |w ^ 2 / 2| = w ^ 2 / 2 := abs_of_nonneg (by positivity)
  rw [hw]
  have hw0 : 0 ≤ w ^ 2 / 2 := by positivity
  calc
    w ^ 2 / 2 * |eval ![0, 0] (pderiv 1 (pderiv 1 G))| ≤ w ^ 2 / 2 * (81 * B) :=
      mul_le_mul_of_nonneg_left h' hw0
    _ ≤ 81 * B * w ^ 2 := by nlinarith [sq_nonneg w]

/-- **Agreement of frozen transverse quadratics.** Two incidences at base points `(t, Z)`,
`(t', Z')` and transverse coordinates `U`, `U'`, whose native signals `X`, `X'` are fitted by
`G` and `G'` with offsets `o`, `o'` to `a₁` and agree to `a₂`, give transverse quadratics frozen
at `(ts, Zs)` that agree at `U` up to the offset difference, within `2 a₁ + a₂` plus the
freezing errors. -/
theorem agree_tilted_match (G G' : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    (hG' : G'.totalDegree ≤ 2)
    (Y : ℝ → ℝ → ℝ) (w : ℝ) {t Z t' Z' ts Zs U U' X X' o o' a₁ a₂ δ L ε : ℝ}
    (hX : |X - eval ![t, Y t Z + w * U] G - o| ≤ a₁)
    (hX' : |X' - eval ![t', Y t' Z' + w * U'] G' - o'| ≤ a₁)
    (hXX : |X - X'| ≤ a₂) (hUU : |U - U'| ≤ δ) (hU : |U| ≤ L) (hU' : |U'| ≤ L)
    (hfreeze : |transA G Y t Z - transA G Y ts Zs| + L * |transB G Y w t Z - transB G Y w ts Zs| +
        |transA G' Y t' Z' - transA G' Y ts Zs| + L * |transB G' Y w t' Z' - transB G' Y w ts Zs| +
        (|transB G' Y w ts Zs| + 2 * L * |transD G' w|) * δ ≤ ε) :
    |(transA G Y ts Zs + transB G Y w ts Zs * U + transD G w * U ^ 2) -
        (transA G' Y ts Zs + transB G' Y w ts Zs * U + transD G' w * U ^ 2) - (o' - o)| ≤
      2 * a₁ + a₂ + ε := by
  rw [agree_eval_tilted G hG Y w t Z U] at hX
  rw [agree_eval_tilted G' hG' Y w t' Z' U'] at hX'
  set A := transA G Y t Z with hA
  set Bv := transB G Y w t Z with hBv
  set Dv := transD G w with hDv
  set As := transA G Y ts Zs with hAs
  set Bs := transB G Y w ts Zs with hBs
  set A' := transA G' Y t' Z' with hA'
  set B' := transB G' Y w t' Z' with hB'
  set D' := transD G' w with hD'
  set As' := transA G' Y ts Zs with hAs'
  set Bs' := transB G' Y w ts Zs with hBs'
  have hL : 0 ≤ L := (abs_nonneg U).trans hU
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hUU
  have key : (As + Bs * U + Dv * U ^ 2) - (As' + Bs' * U + D' * U ^ 2) - (o' - o) =
      (As - A) + (Bs - Bv) * U + (X - X') - (X - (A + Bv * U + Dv * U ^ 2) - o) +
        (X' - (A' + B' * U' + D' * U' ^ 2) - o') + (A' - As') + (B' - Bs') * U' +
        Bs' * (U' - U) + D' * ((U' - U) * (U' + U)) := by ring
  rw [key]
  -- bounds of the pieces
  have h1 : |As - A| = |A - As| := abs_sub_comm _ _
  have h2 : |(Bs - Bv) * U| ≤ L * |Bv - Bs| := by
    rw [abs_mul, abs_sub_comm Bs Bv]
    calc
      |Bv - Bs| * |U| ≤ |Bv - Bs| * L := mul_le_mul_of_nonneg_left hU (abs_nonneg _)
      _ = L * |Bv - Bs| := by ring
  have h6 : |A' - As'| = |A' - As'| := rfl
  have h7 : |(B' - Bs') * U'| ≤ L * |B' - Bs'| := by
    rw [abs_mul]
    calc
      |B' - Bs'| * |U'| ≤ |B' - Bs'| * L := mul_le_mul_of_nonneg_left hU' (abs_nonneg _)
      _ = L * |B' - Bs'| := by ring
  have h8 : |Bs' * (U' - U)| ≤ |Bs'| * δ := by
    rw [abs_mul, abs_sub_comm U' U]
    exact mul_le_mul_of_nonneg_left hUU (abs_nonneg _)
  have h9 : |D' * ((U' - U) * (U' + U))| ≤ 2 * L * |D'| * δ := by
    rw [abs_mul, abs_mul, abs_sub_comm U' U]
    have hsum : |U' + U| ≤ 2 * L := by
      calc
        |U' + U| ≤ |U'| + |U| := abs_add_le _ _
        _ ≤ 2 * L := by linarith
    calc
      |D'| * (|U - U'| * |U' + U|) ≤ |D'| * (δ * (2 * L)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact mul_le_mul hUU hsum (abs_nonneg _) hδ
      _ = 2 * L * |D'| * δ := by ring
  have hfreeze' : |A - As| + L * |Bv - Bs| + |A' - As'| + L * |B' - Bs'| +
      |Bs'| * δ + 2 * L * |D'| * δ ≤ ε := by
    have heq : (|Bs'| + 2 * L * |D'|) * δ = |Bs'| * δ + 2 * L * |D'| * δ := by ring
    linarith
  -- triangle inequality over the nine pieces
  have htri : |(As - A) + (Bs - Bv) * U + (X - X') - (X - (A + Bv * U + Dv * U ^ 2) - o) +
        (X' - (A' + B' * U' + D' * U' ^ 2) - o') + (A' - As') + (B' - Bs') * U' +
        Bs' * (U' - U) + D' * ((U' - U) * (U' + U))| ≤
      |As - A| + |(Bs - Bv) * U| + |X - X'| + |X - (A + Bv * U + Dv * U ^ 2) - o| +
        |X' - (A' + B' * U' + D' * U' ^ 2) - o'| + |A' - As'| + |(B' - Bs') * U'| +
        |Bs' * (U' - U)| + |D' * ((U' - U) * (U' + U))| := by
    have t1 := abs_add_le ((As - A) + (Bs - Bv) * U + (X - X') -
        (X - (A + Bv * U + Dv * U ^ 2) - o) + (X' - (A' + B' * U' + D' * U' ^ 2) - o') +
        (A' - As') + (B' - Bs') * U' + Bs' * (U' - U)) (D' * ((U' - U) * (U' + U)))
    have t2 := abs_add_le ((As - A) + (Bs - Bv) * U + (X - X') -
        (X - (A + Bv * U + Dv * U ^ 2) - o) + (X' - (A' + B' * U' + D' * U' ^ 2) - o') +
        (A' - As') + (B' - Bs') * U') (Bs' * (U' - U))
    have t3 := abs_add_le ((As - A) + (Bs - Bv) * U + (X - X') -
        (X - (A + Bv * U + Dv * U ^ 2) - o) + (X' - (A' + B' * U' + D' * U' ^ 2) - o') +
        (A' - As')) ((B' - Bs') * U')
    have t4 := abs_add_le ((As - A) + (Bs - Bv) * U + (X - X') -
        (X - (A + Bv * U + Dv * U ^ 2) - o) + (X' - (A' + B' * U' + D' * U' ^ 2) - o'))
        (A' - As')
    have t5 := abs_add_le ((As - A) + (Bs - Bv) * U + (X - X') -
        (X - (A + Bv * U + Dv * U ^ 2) - o)) (X' - (A' + B' * U' + D' * U' ^ 2) - o')
    have t6 := abs_sub ((As - A) + (Bs - Bv) * U + (X - X'))
        (X - (A + Bv * U + Dv * U ^ 2) - o)
    have t7 := abs_add_le ((As - A) + (Bs - Bv) * U) (X - X')
    have t8 := abs_add_le (As - A) ((Bs - Bv) * U)
    linarith
  linarith

/-- **A disagreement of transverse pairs is a coefficient gap.** If two transverse pairs `x`,
`y` differ by more than `E / 2` in some coordinate, and the frozen quadratics `P`, `Q` have
slope coefficients within `εB ≤ E / 8` of them and the same curvature coefficients, then the
nonconstant coefficient gap of `P` and `Q` is at least `E / 4`. -/
theorem agree_gap_of_pair_disagree {P Q : Fin 3 → ℝ} {x y : Fin 2 → ℝ} {E εB : ℝ}
    (hbad : ¬ ∀ c : Fin 2, |x c - y c| ≤ E / 2)
    (h0 : |x 0 - P 1| ≤ εB) (h0' : |y 0 - Q 1| ≤ εB) (h1 : x 1 = P 2) (h1' : y 1 = Q 2)
    (hε : εB ≤ E / 8) : E / 4 ≤ Kernels.coeffGap P Q := by
  push Not at hbad
  obtain ⟨c, hc⟩ := hbad
  have hg1 : 0 ≤ |P 1 - Q 1| := abs_nonneg _
  have hg2 : 0 ≤ |P 2 - Q 2| := abs_nonneg _
  simp only [Kernels.coeffGap]
  fin_cases c
  · simp only [Fin.zero_eta] at hc
    have htri : |x 0 - y 0| ≤ |x 0 - P 1| + |P 1 - Q 1| + |Q 1 - y 0| := by
      have e1 := abs_sub_le (x 0) (P 1) (y 0)
      have e2 := abs_sub_le (P 1) (Q 1) (y 0)
      linarith
    have h0'' : |Q 1 - y 0| ≤ εB := by rw [abs_sub_comm]; exact h0'
    linarith
  · simp only [Fin.mk_one] at hc
    rw [h1, h1'] at hc
    linarith

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
