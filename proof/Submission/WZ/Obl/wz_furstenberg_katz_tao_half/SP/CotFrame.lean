-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.CotFrame.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CircleGeometry

/-!
# Cotangent coordinates relative to a line

Fix a line `ℓ₀` through `p₀` with unit normal `n` and direction `perp n`. A point `q` has
coordinates `X q = ⟪q - p₀, perp n⟫` (along) and `Y q = ⟪q - p₀, n⟫` (across). A unit normal
`e` of a line not parallel to `ℓ₀` has cotangent `cotNormal n e = -⟪e, n⟫ / ⟪e, perp n⟫`.

If `q` lies within `r` of the line through a pin `p` (near `ℓ₀`) with normal `e`, then
`(X q - X p) / Y q` is within `2 r / (|Y q| |⟪e, perp n⟫|)` of `cotNormal n e`. Sending `ℓ₀`
to infinity by `q ↦ ((X q - h₁) / Y q, (X q - h₂) / Y q)` turns the pencils of pins on `ℓ₀`
into parallel families (`cot_linear_identity`), and `cotNormal` is expanding on a half circle
(`cotNormal_expanding`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- The coordinate of `q` along the line through `p₀` with unit normal `n`. -/
noncomputable def alongCoord (n p₀ q : Plane) : ℝ := inner ℝ (q - p₀) (perp n)

/-- The coordinate of `q` across the line through `p₀` with unit normal `n`. -/
noncomputable def acrossCoord (n p₀ q : Plane) : ℝ := inner ℝ (q - p₀) n

/-- The cotangent of a unit normal `e` relative to the frame `(perp n, n)`. -/
noncomputable def cotNormal (n e : Plane) : ℝ := -(inner ℝ e n) / inner ℝ e (perp n)

theorem perp_perp (v : Plane) : perp (perp v) = -v := by
  ext i
  fin_cases i <;> simp [perp]

theorem inner_perp_perp (x v : Plane) : inner ℝ (perp x) (perp v) = inner ℝ x v := by
  simp only [plane_inner, perp]
  simp
  ring

/-- Expansion of an inner product in the orthonormal frame `(perp n, n)`. -/
theorem inner_frame {n : Plane} (hn : ‖n‖ = 1) (x y : Plane) :
    inner ℝ x y = inner ℝ x (perp n) * inner ℝ y (perp n) + inner ℝ x n * inner ℝ y n := by
  have hn2 : n 0 ^ 2 + n 1 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq n
    rw [hn, Fin.sum_univ_two] at h
    linarith
  simp only [plane_inner, perp]
  simp
  have e : (x 0 * y 0 + x 1 * y 1) * (n 0 ^ 2 + n 1 ^ 2) =
      (-(x 0 * n 1) + x 1 * n 0) * (-(y 0 * n 1) + y 1 * n 0) +
        (x 0 * n 0 + x 1 * n 1) * (y 0 * n 0 + y 1 * n 1) := by ring
  rw [hn2, mul_one] at e
  linarith

theorem frame_sq {n : Plane} (hn : ‖n‖ = 1) (e : Plane) (he : ‖e‖ = 1) :
    inner ℝ e (perp n) ^ 2 + inner ℝ e n ^ 2 = 1 := by
  have h := inner_sq_add_perp_inner_sq e n
  rw [he, hn] at h
  linarith

theorem alongCoord_sub (n p₀ q p : Plane) :
    alongCoord n p₀ q - alongCoord n p₀ p = inner ℝ (q - p) (perp n) := by
  simp only [alongCoord, ← inner_sub_left]
  congr 1
  abel

theorem acrossCoord_sub (n p₀ q p : Plane) :
    acrossCoord n p₀ q - acrossCoord n p₀ p = inner ℝ (q - p) n := by
  simp only [acrossCoord, ← inner_sub_left]
  congr 1
  abel

/-- A pin `q` near the line through `p` with normal `e` has `(X q - X p) / Y q` close to
the cotangent of `e`. -/
theorem joined_cot {n p₀ p q e : Plane} {r c c' : ℝ} (hn : ‖n‖ = 1) (he : ‖e‖ = 1)
    (hc : 0 < c) (hc' : 0 < c')
    (hjoin : |inner ℝ (q - p) e| ≤ r) (hp : |acrossCoord n p₀ p| ≤ r)
    (hq : c ≤ |acrossCoord n p₀ q|) (hew : c' ≤ |inner ℝ e (perp n)|) :
    |cotNormal n e - (alongCoord n p₀ q - alongCoord n p₀ p) / acrossCoord n p₀ q| ≤
      2 * r / (c * c') := by
  have hY : acrossCoord n p₀ q ≠ 0 := by
    intro h
    rw [h, abs_zero] at hq
    linarith
  have hw : inner ℝ e (perp n) ≠ 0 := by
    intro h
    rw [h, abs_zero] at hew
    linarith
  have hexp := inner_frame hn (q - p) e
  rw [(alongCoord_sub n p₀ q p).symm, (acrossCoord_sub n p₀ q p).symm] at hexp
  have hen : |inner ℝ e n| ≤ 1 := by
    have := frame_sq hn e he
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (inner ℝ e (perp n))]
  set X := alongCoord n p₀ q - alongCoord n p₀ p with hX
  set Yq := acrossCoord n p₀ q
  set Yp := acrossCoord n p₀ p
  set w := inner ℝ e (perp n)
  set m := inner ℝ e n
  -- X w + Yq m = ⟪q - p, e⟫ + Yp m
  have hkey : cotNormal n e - X / Yq = -(inner ℝ (q - p) e + Yp * m) / (Yq * w) := by
    simp only [cotNormal]
    change -m / w - X / Yq = -(inner ℝ (q - p) e + Yp * m) / (Yq * w)
    rw [hexp]
    field_simp
    ring
  rw [hkey, abs_div, abs_neg, abs_mul]
  have hnum : |inner ℝ (q - p) e + Yp * m| ≤ 2 * r := by
    have h1 : |Yp * m| ≤ r := by
      rw [abs_mul]
      calc |Yp| * |m| ≤ r * 1 := mul_le_mul hp hen (abs_nonneg _) ((abs_nonneg _).trans hp)
        _ = r := mul_one r
    calc |inner ℝ (q - p) e + Yp * m| ≤ |inner ℝ (q - p) e| + |Yp * m| := abs_add_le _ _
      _ ≤ 2 * r := by linarith
  have hden : c * c' ≤ |Yq| * |w| := mul_le_mul hq hew hc'.le ((hc.le).trans hq)
  have hr : 0 ≤ r := (abs_nonneg _).trans hjoin
  calc |inner ℝ (q - p) e + Yp * m| / (|Yq| * |w|) ≤ 2 * r / (|Yq| * |w|) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ 2 * r / (c * c') := div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-- A line through a pin near `ℓ₀` which passes near a point far from `ℓ₀` is not nearly
parallel to `ℓ₀`. -/
theorem normal_along_lower {n p₀ p q e : Plane} {r c : ℝ} (hn : ‖n‖ = 1) (he : ‖e‖ = 1)
    (hc : 0 < c) (hc16 : c ≤ 16) (hr : r ≤ c / 8)
    (hjoin : |inner ℝ (q - p) e| ≤ r) (hp : |acrossCoord n p₀ p| ≤ r)
    (hq : c ≤ |acrossCoord n p₀ q|) (hdist : ‖q - p‖ ≤ 16) :
    c / 64 ≤ |inner ℝ e (perp n)| := by
  by_contra hlt
  push Not at hlt
  have hexp := inner_frame hn (q - p) e
  rw [(alongCoord_sub n p₀ q p).symm, (acrossCoord_sub n p₀ q p).symm] at hexp
  have hsq := frame_sq hn e he
  set w := inner ℝ e (perp n)
  set m := inner ℝ e n
  have hw2 : w ^ 2 ≤ (c / 64) ^ 2 := by
    have := abs_le_abs_of_nonneg (abs_nonneg w) hlt.le
    nlinarith [sq_abs w, abs_nonneg w]
  have hm : 1 / 2 ≤ |m| := by
    have hm2 : 1 / 4 ≤ m ^ 2 := by nlinarith
    nlinarith [sq_abs m, abs_nonneg m]
  have hX : |alongCoord n p₀ q - alongCoord n p₀ p| ≤ 16 := by
    rw [alongCoord_sub]
    calc |inner ℝ (q - p) (perp n)| ≤ ‖q - p‖ * ‖perp n‖ := abs_real_inner_le_norm _ _
      _ = ‖q - p‖ := by rw [perp_norm, hn, mul_one]
      _ ≤ 16 := hdist
  have hY : 7 * c / 8 ≤ |acrossCoord n p₀ q - acrossCoord n p₀ p| := by
    have := abs_sub_abs_le_abs_sub (acrossCoord n p₀ q) (acrossCoord n p₀ p)
    linarith
  have h1 : |(acrossCoord n p₀ q - acrossCoord n p₀ p) * m| ≥ 7 * c / 16 := by
    rw [abs_mul]
    nlinarith [abs_nonneg m]
  have h2 : |(alongCoord n p₀ q - alongCoord n p₀ p) * w| ≤ c / 4 := by
    rw [abs_mul]
    calc |alongCoord n p₀ q - alongCoord n p₀ p| * |w| ≤ 16 * (c / 64) :=
          mul_le_mul hX hlt.le (abs_nonneg _) (by norm_num)
      _ = c / 4 := by ring
  have h3 : |inner ℝ (q - p) e| ≥ 7 * c / 16 - c / 4 := by
    rw [hexp]
    have := abs_sub_abs_le_abs_sub ((acrossCoord n p₀ q - acrossCoord n p₀ p) * m)
      (-((alongCoord n p₀ q - alongCoord n p₀ p) * w))
    rw [abs_neg] at this
    have e2 : (acrossCoord n p₀ q - acrossCoord n p₀ p) * m -
        -((alongCoord n p₀ q - alongCoord n p₀ p) * w) =
        (alongCoord n p₀ q - alongCoord n p₀ p) * w +
          (acrossCoord n p₀ q - acrossCoord n p₀ p) * m := by ring
    rw [e2] at this
    linarith
  linarith

/-- The pencils of pins on `ℓ₀` become parallel families: the cotangent from a pin at
position `h` is an affine combination of the cotangents from the pins at `h₁`, `h₂`. -/
theorem cot_linear_identity {X Y h h₁ h₂ : ℝ} (hY : Y ≠ 0) (h12 : h₁ ≠ h₂) :
    (X - h) / Y = ((h₂ - h) * ((X - h₁) / Y) + (h - h₁) * ((X - h₂) / Y)) / (h₂ - h₁) := by
  have h12' : h₂ - h₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  field_simp
  ring

/-- `cotNormal` is expanding on each half circle: for unit normals with
`⟪e, perp n⟫, ⟪e', perp n⟫ ≥ c'`, `c' ‖e - e'‖ ≤ |cot e - cot e'|`. -/
theorem cotNormal_expanding {n e e' : Plane} {c' : ℝ} (hn : ‖n‖ = 1) (he : ‖e‖ = 1)
    (he' : ‖e'‖ = 1) (hc' : 0 < c') (hw : c' ≤ inner ℝ e (perp n))
    (hw' : c' ≤ inner ℝ e' (perp n)) :
    c' * ‖e - e'‖ ≤ |cotNormal n e - cotNormal n e'| := by
  have hs := frame_sq hn e he
  have hs' := frame_sq hn e' he'
  set a := inner ℝ e (perp n)
  set b := inner ℝ e n
  set a' := inner ℝ e' (perp n)
  set b' := inner ℝ e' n
  have ha : 0 < a := hc'.trans_le hw
  have ha' : 0 < a' := hc'.trans_le hw'
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg b]
  have ha1' : a' ≤ 1 := by nlinarith [sq_nonneg b']
  -- ‖e - e'‖² in the frame
  have hnorm : ‖e - e'‖ ^ 2 = (a - a') ^ 2 + (b - b') ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_frame hn]
    simp only [inner_sub_left]
    ring
  have hcot : cotNormal n e - cotNormal n e' = (a * b' - a' * b) / (a * a') := by
    simp only [cotNormal]
    change -b / a - -b' / a' = (a * b' - a' * b) / (a * a')
    field_simp
    ring
  -- the Lagrange identity: (a b' - a' b)² = ‖e - e'‖² ‖e + e'‖² / 4
  have e1 : (a - a') ^ 2 + (b - b') ^ 2 = 2 - 2 * (a * a' + b * b') := by
    linear_combination hs + hs'
  have e2 : (a + a') ^ 2 + (b + b') ^ 2 = 2 + 2 * (a * a' + b * b') := by
    linear_combination hs + hs'
  have hlag : (a * b' - a' * b) ^ 2 =
      ((a - a') ^ 2 + (b - b') ^ 2) * ((a + a') ^ 2 + (b + b') ^ 2) / 4 := by
    have h1 : (a * b' - a' * b) ^ 2 =
        (a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2) - (a * a' + b * b') ^ 2 := by ring
    rw [h1, hs, hs', e1, e2]
    ring
  have hsum : 4 * c' ^ 2 ≤ (a + a') ^ 2 + (b + b') ^ 2 := by
    have h2 : 2 * c' ≤ a + a' := by linarith
    have h3 := mul_self_le_mul_self (by positivity) h2
    nlinarith [sq_nonneg (b + b')]
  have hdet : c' * ‖e - e'‖ ≤ |a * b' - a' * b| := by
    have hsq : (c' * ‖e - e'‖) ^ 2 ≤ (a * b' - a' * b) ^ 2 := by
      rw [hlag, mul_pow, hnorm]
      have hD : 0 ≤ (a - a') ^ 2 + (b - b') ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hsum hD
      nlinarith
    have h0 : 0 ≤ c' * ‖e - e'‖ := by positivity
    calc c' * ‖e - e'‖ = |c' * ‖e - e'‖| := (abs_of_nonneg h0).symm
      _ ≤ |a * b' - a' * b| := sq_le_sq.mp hsq
  rw [hcot, abs_div, abs_of_pos (mul_pos ha ha')]
  have haa : a * a' ≤ 1 := by nlinarith
  have hpos : 0 < a * a' := mul_pos ha ha'
  rw [le_div_iff₀ hpos]
  have h0 : 0 ≤ c' * ‖e - e'‖ := by positivity
  calc c' * ‖e - e'‖ * (a * a') ≤ c' * ‖e - e'‖ * 1 :=
        mul_le_mul_of_nonneg_left haa h0
    _ = c' * ‖e - e'‖ := mul_one _
    _ ≤ |a * b' - a' * b| := hdet

theorem cotNormal_neg (n e : Plane) : cotNormal n (-e) = cotNormal n e := by
  simp only [cotNormal, inner_neg_left, neg_neg]
  rw [div_neg, neg_div]

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
