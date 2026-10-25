-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.RoundBox.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.PrismGeometry

-- Copied from session x0338 (o070 branch, commit 6d10f34, file RoundBox.lean), namespace renamed.
/-!
# Unit tubes in a thin box meet boundedly many grid cells

Two unit segments inside a box with half-widths `a ≤ b` and half-length `2` have almost
parallel directions (`‖v - v'‖ ≤ 7 b` up to the sign of `v'`) and almost equal lines: the feet of
the perpendiculars from the origin differ by at most `60 b`.  So the tubes of a family that lie
in such a box meet at most `(120 b / s + 2)³ (14 b / s + 2)³` cells of the grid of size `s` in
(foot, direction) space, and their number is at most that many cell populations.

This is the round-box hypothesis of x0318's `fibre_dichotomy` (o070/x0318,
`FibreDichotomy.lean`), for the grid of o038/x0305 (`NetCover.lineCell`): `lineFoot`,
`gridCell` and `lineGridCell` below have the same bodies as x0305's `foot`, `cellIdx` and
`lineCell`.  No alignment of the tubes is needed for the count, only unit directions, tubes in
the unit ball and no antipodal pairs.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set Metric
open scoped RealInnerProductSpace

/-- The foot of the perpendicular from the origin to the line through `x` with direction `v`
(the `foot` of o038/x0305's `Canonical.lean`). -/
noncomputable def lineFoot (x v : Space) : Space := x - (⟪x, v⟫) • v

/-- Grid cell of a point at size `s` (o038/x0305's `cellIdx`). -/
noncomputable def gridCell (s : ℝ) (y : Space) : Fin 3 → ℤ := fun c => ⌊y c / s⌋

/-- Grid cell of a line given by a point and a unit direction (o038/x0305's `lineCell`). -/
noncomputable def lineGridCell (s : ℝ) (x v : Space) : (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  (gridCell s (lineFoot x v), gridCell s v)

lemma lineFoot_add_smul {x v : Space} (hv : ‖v‖ = 1) (t : ℝ) :
    lineFoot (x + t • v) v = lineFoot x v := by
  unfold lineFoot
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv, add_smul]
  simp only [one_pow, mul_one]
  abel

lemma lineFoot_neg (x v : Space) : lineFoot x (-v) = lineFoot x v := by
  unfold lineFoot
  rw [inner_neg_right, neg_smul_neg]

/-- Feet of two lines through `y`, `m` with unit directions `v`, `w`. -/
lemma lineFoot_sub_le {y m v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖lineFoot y v - lineFoot m w‖ ≤ 2 * ‖y - m‖ + (‖y‖ + ‖m‖) * ‖v - w‖ := by
  have hdecomp : lineFoot y v - lineFoot m w =
      (y - m) - (⟪y, v⟫ • (v - w) + (⟪y - m, v⟫ + ⟪m, v - w⟫) • w) := by
    unfold lineFoot
    rw [inner_sub_left, inner_sub_right]
    module
  rw [hdecomp]
  have h1 : ‖⟪y, v⟫ • (v - w)‖ ≤ ‖y‖ * ‖v - w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    simpa [hv] using abs_real_inner_le_norm y v
  have h2 : |⟪y - m, v⟫| ≤ ‖y - m‖ := by simpa [hv] using abs_real_inner_le_norm (y - m) v
  have h3 : |⟪m, v - w⟫| ≤ ‖m‖ * ‖v - w‖ := abs_real_inner_le_norm m (v - w)
  have h4 : ‖(⟪y - m, v⟫ + ⟪m, v - w⟫) • w‖ ≤ ‖y - m‖ + ‖m‖ * ‖v - w‖ := by
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add h2 h3)
  calc ‖(y - m) - (⟪y, v⟫ • (v - w) + (⟪y - m, v⟫ + ⟪m, v - w⟫) • w)‖
      ≤ ‖y - m‖ + (‖⟪y, v⟫ • (v - w)‖ + ‖(⟪y - m, v⟫ + ⟪m, v - w⟫) • w‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ ‖y - m‖ + (‖y‖ * ‖v - w‖ + (‖y - m‖ + ‖m‖ * ‖v - w‖)) := by gcongr
    _ = 2 * ‖y - m‖ + (‖y‖ + ‖m‖) * ‖v - w‖ := by ring

/-- Parseval in an orthonormal frame of the three-dimensional space. -/
lemma frame_norm_sq {f₀ f₁ f₂ : Space} (hf : Orthonormal ℝ ![f₀, f₁, f₂]) (w : Space) :
    ‖w‖ ^ 2 = ⟪f₀, w⟫ ^ 2 + ⟪f₁, w⟫ ^ 2 + ⟪f₂, w⟫ ^ 2 := by
  obtain ⟨B, h0, h1, h2⟩ := basis_of_frame hf
  rw [← B.sum_sq_inner_right w, Fin.sum_univ_three, h0, h1, h2]

/-- Membership in the closed box with orthonormal frame `f₀, f₁, f₂`, centre `c` and
half-widths `a, b, L`. -/
def InFrameBox (a b L : ℝ) (c f₀ f₁ f₂ y : Space) : Prop :=
  |⟪f₀, y - c⟫| ≤ a ∧ |⟪f₁, y - c⟫| ≤ b ∧ |⟪f₂, y - c⟫| ≤ L

/-- The boxes `e '' {|y 0| ≤ a, |y 1| ≤ b, |y 2| ≤ 2}` of the accepted convex factorization
(x0318's `factorBox a b`) are frame boxes. -/
lemma factorBox_frame (a b : ℝ) (e : Space ≃ᵃⁱ[ℝ] Space) :
    ∃ c f₀ f₁ f₂ : Space, Orthonormal ℝ ![f₀, f₁, f₂] ∧
      ∀ y ∈ e '' {z : Space | |z 0| ≤ a ∧ |z 1| ≤ b ∧ |z 2| ≤ 2},
        InFrameBox a b 2 c f₀ f₁ f₂ y := by
  let B₀ := EuclideanSpace.basisFun (Fin 3) ℝ
  let B := B₀.map e.linearIsometryEquiv
  have hB : Orthonormal ℝ ![B 0, B 1, B 2] := by
    convert B.orthonormal using 1
    ext i
    fin_cases i <;> rfl
  refine ⟨e 0, B 0, B 1, B 2, hB, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have he (i : Fin 3) : ⟪B i, e z - e 0⟫ = z i := by
    have hez : e z - e 0 = e.linearIsometryEquiv z := by
      simpa only [vsub_eq_sub, sub_zero] using (e.map_vsub z 0).symm
    rw [hez]
    change ⟪e.linearIsometryEquiv (B₀ i), e.linearIsometryEquiv z⟫ = z i
    rw [e.linearIsometryEquiv.inner_map_map, ← OrthonormalBasis.repr_apply_apply]
    rfl
  exact ⟨by simpa only [he] using hz.1, by simpa only [he] using hz.2.1,
    by simpa only [he] using hz.2.2⟩

/-- The direction of a segment with both ends in a frame box. -/
lemma dir_coords_of_endpoints {a b L : ℝ} {c f₀ f₁ f₂ x v : Space}
    (h0 : InFrameBox a b L c f₀ f₁ f₂ x) (h1 : InFrameBox a b L c f₀ f₁ f₂ (x + v)) :
    |⟪f₀, v⟫| ≤ 2 * a ∧ |⟪f₁, v⟫| ≤ 2 * b ∧ |⟪f₂, v⟫| ≤ 2 * L := by
  have e (f : Space) : ⟪f, v⟫ = ⟪f, x + v - c⟫ - ⟪f, x - c⟫ := by
    rw [← inner_sub_right]
    congr 1
    abel
  obtain ⟨h00, h01, h02⟩ := h0
  obtain ⟨h10, h11, h12⟩ := h1
  refine ⟨?_, ?_, ?_⟩
  · rw [e]; exact (abs_sub _ _).trans (by linarith)
  · rw [e]; exact (abs_sub _ _).trans (by linarith)
  · rw [e]; exact (abs_sub _ _).trans (by linarith)

/-- The midpoint of a segment with both ends in a frame box is in the box. -/
lemma mid_inFrameBox {a b L : ℝ} {c f₀ f₁ f₂ x v : Space}
    (h0 : InFrameBox a b L c f₀ f₁ f₂ x) (h1 : InFrameBox a b L c f₀ f₁ f₂ (x + v)) :
    InFrameBox a b L c f₀ f₁ f₂ (x + (1 / 2 : ℝ) • v) := by
  have e (f : Space) : ⟪f, x + (1 / 2 : ℝ) • v - c⟫ =
      (⟪f, x - c⟫ + ⟪f, x + v - c⟫) / 2 := by
    have : x + (1 / 2 : ℝ) • v - c = (1 / 2 : ℝ) • ((x - c) + (x + v - c)) := by
      rw [smul_add]
      module
    rw [this, real_inner_smul_right, inner_add_right]
    ring
  obtain ⟨h00, h01, h02⟩ := h0
  obtain ⟨h10, h11, h12⟩ := h1
  refine ⟨?_, ?_, ?_⟩
  · rw [e, abs_div, abs_two, div_le_iff₀ two_pos]
    exact (abs_add_le _ _).trans (by linarith)
  · rw [e, abs_div, abs_two, div_le_iff₀ two_pos]
    exact (abs_add_le _ _).trans (by linarith)
  · rw [e, abs_div, abs_two, div_le_iff₀ two_pos]
    exact (abs_add_le _ _).trans (by linarith)

lemma sq_sub_le_abs_sq_sub {p q : ℝ} (h : 0 ≤ p * q) : (p - q) ^ 2 ≤ |p ^ 2 - q ^ 2| := by
  have hle : |p - q| ≤ |p + q| := by
    rcases mul_nonneg_iff.mp h with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [abs_of_nonneg (by linarith : 0 ≤ p + q)]
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    · rw [abs_of_nonpos (by linarith : p + q ≤ 0)]
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  calc (p - q) ^ 2 = |p - q| * |p - q| := by rw [abs_mul_abs_self, sq]
    _ ≤ |p - q| * |p + q| := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ = |p ^ 2 - q ^ 2| := by rw [← abs_mul]; congr 1; ring

/-- Unit vectors whose first two frame coordinates are small are close up to sign. -/
lemma dirs_close {a b : ℝ} {f₀ f₁ f₂ v v' : Space} (hf : Orthonormal ℝ ![f₀, f₁, f₂])
    (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) (hab : a ≤ b)
    (h0 : |⟪f₀, v⟫| ≤ 2 * a) (h1 : |⟪f₁, v⟫| ≤ 2 * b)
    (h0' : |⟪f₀, v'⟫| ≤ 2 * a) (h1' : |⟪f₁, v'⟫| ≤ 2 * b) :
    ‖v - v'‖ ≤ 7 * b ∨ ‖v + v'‖ ≤ 7 * b := by
  have ha : 0 ≤ a := by linarith [abs_nonneg ⟪f₀, v⟫]
  have hb : 0 ≤ b := ha.trans hab
  have nv := frame_norm_sq hf v
  have nv' := frame_norm_sq hf v'
  rw [hv] at nv
  rw [hv'] at nv'
  set u₀ := ⟪f₀, v⟫
  set u₁ := ⟪f₁, v⟫
  set u₂ := ⟪f₂, v⟫
  set w₀ := ⟪f₀, v'⟫
  set w₁ := ⟪f₁, v'⟫
  set w₂ := ⟪f₂, v'⟫
  have su₀ : u₀ ^ 2 ≤ 4 * b ^ 2 := by
    have := sq_le_sq' (abs_le.mp h0).1 (abs_le.mp h0).2; nlinarith
  have su₁ : u₁ ^ 2 ≤ 4 * b ^ 2 := by
    have := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2; nlinarith
  have sw₀ : w₀ ^ 2 ≤ 4 * b ^ 2 := by
    have := sq_le_sq' (abs_le.mp h0').1 (abs_le.mp h0').2; nlinarith
  have sw₁ : w₁ ^ 2 ≤ 4 * b ^ 2 := by
    have := sq_le_sq' (abs_le.mp h1').1 (abs_le.mp h1').2; nlinarith
  have hdiff : |u₂ ^ 2 - w₂ ^ 2| ≤ 8 * b ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg u₀, sq_nonneg u₁, sq_nonneg w₀, sq_nonneg w₁]
  have hc0 : (u₀ - w₀) ^ 2 ≤ 16 * b ^ 2 := by
    have : |u₀ - w₀| ≤ 4 * b := (abs_sub _ _).trans (by linarith)
    have := sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2; nlinarith
  have hc1 : (u₁ - w₁) ^ 2 ≤ 16 * b ^ 2 := by
    have : |u₁ - w₁| ≤ 4 * b := (abs_sub _ _).trans (by linarith)
    have := sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2; nlinarith
  have hd0 : (u₀ + w₀) ^ 2 ≤ 16 * b ^ 2 := by
    have : |u₀ + w₀| ≤ 4 * b := (abs_add_le _ _).trans (by linarith)
    have := sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2; nlinarith
  have hd1 : (u₁ + w₁) ^ 2 ≤ 16 * b ^ 2 := by
    have : |u₁ + w₁| ≤ 4 * b := (abs_add_le _ _).trans (by linarith)
    have := sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2; nlinarith
  rcases le_total 0 (u₂ * w₂) with hs | hs
  · left
    have h2 : (u₂ - w₂) ^ 2 ≤ 8 * b ^ 2 := (sq_sub_le_abs_sq_sub hs).trans hdiff
    have hn := frame_norm_sq hf (v - v')
    simp only [inner_sub_right] at hn
    have hsq : ‖v - v'‖ ^ 2 ≤ (7 * b) ^ 2 := by rw [hn]; nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  · right
    have hs' : 0 ≤ u₂ * (-w₂) := by linarith
    have h2 : (u₂ + w₂) ^ 2 ≤ 8 * b ^ 2 := by
      have h3 := sq_sub_le_abs_sq_sub hs'
      rw [neg_sq, sub_neg_eq_add] at h3
      exact h3.trans hdiff
    have hn := frame_norm_sq hf (v + v')
    simp only [inner_add_right] at hn
    have hsq : ‖v + v'‖ ^ 2 ≤ (7 * b) ^ 2 := by rw [hn]; nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **Lines of unit segments in a thin box are close.**  Two unit segments with all four
endpoints in a frame box of half-widths `a ≤ b ≤ 1/10` and half-length `2`, the second with its
midpoint in the closed unit ball, have feet within `60 b`. -/
theorem feet_close_of_box {a b : ℝ} {c f₀ f₁ f₂ x v x' v' : Space}
    (hf : Orthonormal ℝ ![f₀, f₁, f₂]) (hab : a ≤ b) (hb : b ≤ 1 / 10)
    (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hx : InFrameBox a b 2 c f₀ f₁ f₂ x) (hxv : InFrameBox a b 2 c f₀ f₁ f₂ (x + v))
    (hx' : InFrameBox a b 2 c f₀ f₁ f₂ x') (hxv' : InFrameBox a b 2 c f₀ f₁ f₂ (x' + v'))
    (hmid : ‖x' + (1 / 2 : ℝ) • v'‖ ≤ 1) :
    ‖lineFoot x v - lineFoot x' v'‖ ≤ 60 * b := by
  obtain ⟨hu₀, hu₁, -⟩ := dir_coords_of_endpoints hx hxv
  obtain ⟨hw₀, hw₁, -⟩ := dir_coords_of_endpoints hx' hxv'
  have ha : 0 ≤ a := by linarith [abs_nonneg ⟪f₀, v⟫]
  have hb0 : 0 ≤ b := ha.trans hab
  set m := x' + (1 / 2 : ℝ) • v' with hm
  have hmbox : InFrameBox a b 2 c f₀ f₁ f₂ m := mid_inFrameBox hx' hxv'
  -- the longitudinal coordinate of `v` is bounded below
  have nv := frame_norm_sq hf v
  rw [hv] at nv
  set u₀ := ⟪f₀, v⟫
  set u₁ := ⟪f₁, v⟫
  set u₂ := ⟪f₂, v⟫
  have su₀ : u₀ ^ 2 ≤ 4 * b ^ 2 := by
    have := sq_le_sq' (abs_le.mp hu₀).1 (abs_le.mp hu₀).2; nlinarith
  have su₁ : u₁ ^ 2 ≤ 4 * b ^ 2 := by
    have := sq_le_sq' (abs_le.mp hu₁).1 (abs_le.mp hu₁).2; nlinarith
  have hu₂sq : (9 / 10 : ℝ) ^ 2 ≤ |u₂| ^ 2 := by
    rw [sq_abs]; nlinarith
  have hu₂ : (9 / 10 : ℝ) ≤ |u₂| :=
    (pow_le_pow_iff_left₀ (by norm_num) (abs_nonneg _) two_ne_zero).mp hu₂sq
  have hu₂ne : u₂ ≠ 0 := by
    intro h; rw [h, abs_zero] at hu₂; norm_num at hu₂
  -- the point of the first line level with `m`
  set t := ⟪f₂, m - x⟫ / u₂ with ht
  set y := x + t • v with hy
  have hmx : |⟪f₂, m - x⟫| ≤ 4 := by
    have : ⟪f₂, m - x⟫ = ⟪f₂, m - c⟫ - ⟪f₂, x - c⟫ := by
      rw [← inner_sub_right]; congr 1; abel
    rw [this]
    exact (abs_sub _ _).trans (by linarith [hmbox.2.2, hx.2.2])
  have htb : |t| ≤ 9 / 2 := by
    rw [ht, abs_div, div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg u₂]
  have hcoord (f : Space) : ⟪f, y - m⟫ = ⟪f, x - c⟫ - ⟪f, m - c⟫ + t * ⟪f, v⟫ := by
    have : y - m = (x - c) - (m - c) + t • v := by rw [hy]; abel
    rw [this, inner_add_right, inner_sub_right, real_inner_smul_right]
  have hy2 : ⟪f₂, y - m⟫ = 0 := by
    have hsplit : ⟪f₂, x - c⟫ - ⟪f₂, m - c⟫ = -⟪f₂, m - x⟫ := by
      rw [← inner_sub_right, ← inner_neg_right]; congr 1; abel
    rw [hcoord, hsplit, ht, div_mul_cancel₀ _ hu₂ne]
    ring
  have hy0 : |⟪f₀, y - m⟫| ≤ 11 * b := by
    rw [hcoord]
    have h1 : |t * u₀| ≤ 9 / 2 * (2 * a) := by
      rw [abs_mul]; exact mul_le_mul htb hu₀ (abs_nonneg _) (by norm_num)
    calc |⟪f₀, x - c⟫ - ⟪f₀, m - c⟫ + t * u₀|
        ≤ |⟪f₀, x - c⟫| + |⟪f₀, m - c⟫| + |t * u₀| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ a + a + 9 / 2 * (2 * a) := add_le_add (add_le_add hx.1 hmbox.1) h1
      _ ≤ 11 * b := by linarith
  have hy1 : |⟪f₁, y - m⟫| ≤ 11 * b := by
    rw [hcoord]
    have h1 : |t * u₁| ≤ 9 / 2 * (2 * b) := by
      rw [abs_mul]; exact mul_le_mul htb hu₁ (abs_nonneg _) (by norm_num)
    calc |⟪f₁, x - c⟫ - ⟪f₁, m - c⟫ + t * u₁|
        ≤ |⟪f₁, x - c⟫| + |⟪f₁, m - c⟫| + |t * u₁| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ b + b + 9 / 2 * (2 * b) := add_le_add (add_le_add hx.2.1 hmbox.2.1) h1
      _ = 11 * b := by ring
  have hym : ‖y - m‖ ≤ 16 * b := by
    have hn := frame_norm_sq hf (y - m)
    rw [hy2] at hn
    have e0 := sq_le_sq' (abs_le.mp hy0).1 (abs_le.mp hy0).2
    have e1 := sq_le_sq' (abs_le.mp hy1).1 (abs_le.mp hy1).2
    have hsq : ‖y - m‖ ^ 2 ≤ (16 * b) ^ 2 := by rw [hn]; nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  -- the feet are those of `y` and `m`
  have hfoot₁ : lineFoot x v = lineFoot y v := by rw [hy, lineFoot_add_smul hv]
  have hfoot₂ : lineFoot x' v' = lineFoot m v' := by rw [hm, lineFoot_add_smul hv']
  have hyn : ‖y‖ ≤ 1 + 16 * b := by
    have := norm_le_norm_add_norm_sub' y m
    calc ‖y‖ ≤ ‖m‖ + ‖y - m‖ := by
          have h := norm_sub_norm_le y m; linarith
      _ ≤ 1 + 16 * b := add_le_add hmid hym
  -- choose the orientation of `v'` close to `v`
  obtain ⟨w, hw, hfw, hvw⟩ : ∃ w : Space, ‖w‖ = 1 ∧ lineFoot m w = lineFoot m v' ∧
      ‖v - w‖ ≤ 7 * b := by
    rcases dirs_close hf hv hv' hab hu₀ hu₁ hw₀ hw₁ with h | h
    · exact ⟨v', hv', rfl, h⟩
    · refine ⟨-v', by rw [norm_neg, hv'], lineFoot_neg m v', ?_⟩
      simpa [sub_neg_eq_add] using h
  rw [hfoot₁, hfoot₂, ← hfw]
  calc ‖lineFoot y v - lineFoot m w‖ ≤ 2 * ‖y - m‖ + (‖y‖ + ‖m‖) * ‖v - w‖ :=
        lineFoot_sub_le hv hw
    _ ≤ 2 * (16 * b) + ((1 + 16 * b) + 1) * (7 * b) := by
        gcongr
    _ ≤ 60 * b := by nlinarith

/-- Two unit tubes in one box `e '' {|y 0| ≤ a, |y 1| ≤ b, |y 2| ≤ 2}` (`a ≤ b ≤ 1/10`), the second
in the unit ball: their feet are within `60 b` and their directions within `7 b` up to sign. -/
theorem tube_params_close_of_box {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (hb : b ≤ 1 / 10)
    (e : Space ≃ᵃⁱ[ℝ] Space) {x v x' v' : Space} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hT' : Tube δ x' v' ⊆ Metric.ball 0 1)
    (h : Tube δ x v ⊆ e '' {z : Space | |z 0| ≤ a ∧ |z 1| ≤ b ∧ |z 2| ≤ 2})
    (h' : Tube δ x' v' ⊆ e '' {z : Space | |z 0| ≤ a ∧ |z 1| ≤ b ∧ |z 2| ≤ 2}) :
    ‖lineFoot x v - lineFoot x' v'‖ ≤ 60 * b ∧ (‖v - v'‖ ≤ 7 * b ∨ ‖v + v'‖ ≤ 7 * b) := by
  obtain ⟨c, f₀, f₁, f₂, hf, hbox⟩ := factorBox_frame a b e
  have mem (p q : Space) (hpq : Tube δ p q ⊆ e '' {z : Space | |z 0| ≤ a ∧ |z 1| ≤ b ∧ |z 2| ≤ 2})
      (y : Space) (hy : y ∈ segment ℝ p (p + q)) : InFrameBox a b 2 c f₀ f₁ f₂ y :=
    hbox y (hpq (self_subset_thickening hδ _ hy))
  have hx := mem x v h x (left_mem_segment ℝ _ _)
  have hxv := mem x v h (x + v) (right_mem_segment ℝ _ _)
  have hx' := mem x' v' h' x' (left_mem_segment ℝ _ _)
  have hxv' := mem x' v' h' (x' + v') (right_mem_segment ℝ _ _)
  have hmid : ‖x' + (1 / 2 : ℝ) • v'‖ ≤ 1 := by
    have hseg : x' + (1 / 2 : ℝ) • v' ∈ segment ℝ x' (x' + v') := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      rw [smul_add]
      module
    have := hT' (self_subset_thickening hδ _ hseg)
    exact (mem_ball_zero_iff.mp this).le
  obtain ⟨hu₀, hu₁, -⟩ := dir_coords_of_endpoints hx hxv
  obtain ⟨hw₀, hw₁, -⟩ := dir_coords_of_endpoints hx' hxv'
  exact ⟨feet_close_of_box hf hab hb hv hv' hx hxv hx' hxv' hmid,
    dirs_close hf hv hv' hab hu₀ hu₁ hw₀ hw₁⟩

/-! ### Counting grid cells -/

lemma card_Icc_floor_le {P D s : ℝ} (hs : 0 < s) (hD : 0 ≤ D) :
    ((Finset.Icc ⌊(P - D) / s⌋ ⌊(P + D) / s⌋).card : ℝ) ≤ 2 * D / s + 2 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le ((P + D) / s)
  have h2 := Int.lt_floor_add_one ((P - D) / s)
  have hlt : ((⌊(P + D) / s⌋ + 1 - ⌊(P - D) / s⌋ : ℤ) : ℝ) < 2 * D / s + 2 := by
    push_cast
    have : (P + D) / s - (P - D) / s = 2 * D / s := by ring
    linarith
  have hpos : (0 : ℝ) ≤ 2 * D / s + 2 := by positivity
  rcases le_total 0 (⌊(P + D) / s⌋ + 1 - ⌊(P - D) / s⌋) with hz | hz
  · rw [show ((Int.toNat (⌊(P + D) / s⌋ + 1 - ⌊(P - D) / s⌋) : ℕ) : ℝ) =
        ((⌊(P + D) / s⌋ + 1 - ⌊(P - D) / s⌋ : ℤ) : ℝ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]]
    exact hlt.le
  · rw [Int.toNat_eq_zero.mpr hz]
    simpa using hpos

lemma floor_mem_Icc {P D s y : ℝ} (hs : 0 < s) (hy : |y - P| ≤ D) :
    ⌊y / s⌋ ∈ Finset.Icc ⌊(P - D) / s⌋ ⌊(P + D) / s⌋ := by
  rw [Finset.mem_Icc]
  obtain ⟨h1, h2⟩ := abs_le.mp hy
  constructor
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hs.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hs.le)

/-- A set of points of diameter at most `D` meets at most `(2 D / s + 2)³` grid cells of size
`s`. -/
lemma card_gridCell_image_le {ι : Type*} (S : Finset ι) (p : ι → Space) {D s : ℝ}
    (hs : 0 < s) (hp : ∀ i ∈ S, ∀ j ∈ S, ‖p i - p j‖ ≤ D) (i₀ : ι)
    (hi₀ : i₀ ∈ S) :
    S.image (fun i => gridCell s (p i)) ⊆
      Fintype.piFinset (fun c : Fin 3 => Finset.Icc ⌊(p i₀ c - D) / s⌋ ⌊(p i₀ c + D) / s⌋) := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
  rw [Fintype.mem_piFinset]
  intro c
  apply floor_mem_Icc hs
  have h := PiLp.norm_apply_le (p i - p i₀) c
  rw [PiLp.sub_apply, Real.norm_eq_abs] at h
  exact h.trans (hp i hi i₀ hi₀)

lemma card_piFinset_Icc_le {P : Fin 3 → ℝ} {D s : ℝ} (hs : 0 < s) (hD : 0 ≤ D) :
    ((Fintype.piFinset (fun c : Fin 3 => Finset.Icc ⌊(P c - D) / s⌋ ⌊(P c + D) / s⌋)).card : ℝ)
      ≤ (2 * D / s + 2) ^ 3 := by
  rw [Fintype.card_piFinset, Nat.cast_prod, Fin.prod_univ_three]
  have h0 := card_Icc_floor_le (P := P 0) hs hD
  have h1 := card_Icc_floor_le (P := P 1) hs hD
  have h2 := card_Icc_floor_le (P := P 2) hs hD
  calc _ ≤ (2 * D / s + 2) * (2 * D / s + 2) * (2 * D / s + 2) := by gcongr
    _ = (2 * D / s + 2) ^ 3 := by ring

/-- **Cell count.**  If the feet of a finite family of lines have diameter `≤ D₁` and their
directions diameter `≤ D₂`, the lines meet at most `(2 D₁ / s + 2)³ (2 D₂ / s + 2)³` cells of the
grid of size `s`. -/
theorem card_lineCells_le {ι : Type*} (S : Finset ι) (p q : ι → Space) {D₁ D₂ s : ℝ}
    (hs : 0 < s) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hp : ∀ i ∈ S, ∀ j ∈ S, ‖p i - p j‖ ≤ D₁) (hq : ∀ i ∈ S, ∀ j ∈ S, ‖q i - q j‖ ≤ D₂) :
    ((S.image (fun i => (gridCell s (p i), gridCell s (q i)))).card : ℝ) ≤
      (2 * D₁ / s + 2) ^ 3 * (2 * D₂ / s + 2) ^ 3 := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
  · subst hS
    simp only [Finset.image_empty, Finset.card_empty, Nat.cast_zero]
    positivity
  have hsub : S.image (fun i => (gridCell s (p i), gridCell s (q i))) ⊆
      (S.image (fun i => gridCell s (p i))) ×ˢ (S.image (fun i => gridCell s (q i))) := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi, Finset.mem_image_of_mem _ hi⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_product] at hc
  have hP := Finset.card_le_card (card_gridCell_image_le S p hs hp i₀ hi₀)
  have hQ := Finset.card_le_card (card_gridCell_image_le S q hs hq i₀ hi₀)
  have hP' := card_piFinset_Icc_le (P := fun c => p i₀ c) hs hD₁
  have hQ' := card_piFinset_Icc_le (P := fun c => q i₀ c) hs hD₂
  calc ((S.image (fun i => (gridCell s (p i), gridCell s (q i)))).card : ℝ)
      ≤ ((S.image (fun i => gridCell s (p i))).card : ℝ) *
          ((S.image (fun i => gridCell s (q i))).card : ℝ) := by exact_mod_cast hc
    _ ≤ (2 * D₁ / s + 2) ^ 3 * (2 * D₂ / s + 2) ^ 3 := by
        gcongr
        · exact (Nat.cast_le.mpr hP).trans hP'
        · exact (Nat.cast_le.mpr hQ).trans hQ'

open Classical in
/-- **Round-box count.**  Let `S` be a finite family of unit `δ`-tubes in the unit ball with no
antipodal pair of directions, and let every grid cell of size `s` in (foot, direction) space hold
at most `P` tubes of `S`.  Then every box `e '' {|y 0| ≤ a, |y 1| ≤ b, |y 2| ≤ 2}` with
`a ≤ b ≤ 1/10` contains at most `(120 b / s + 2)³ (14 b / s + 2)³ P` tubes of `S`.  For
`s ≥ 120 b` this is at most `216 P`. -/
theorem card_tubes_in_box_le {n : ℕ} (x v : Fin n → Space) (S : Finset (Fin n))
    {δ a b s P : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 10) (hs : 0 < s)
    (hP : 0 ≤ P)
    (e : Space ≃ᵃⁱ[ℝ] Space)
    (hv : ∀ i ∈ S, ‖v i‖ = 1) (hball : ∀ i ∈ S, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hanti : ∀ i ∈ S, ∀ j ∈ S, 1 ≤ ‖v i + v j‖)
    (hpop : ∀ i ∈ S, ((S.filter (fun j => lineGridCell s (x j) (v j) =
      lineGridCell s (x i) (v i))).card : ℝ) ≤ P) :
    ((S.filter (fun i => Tube δ (x i) (v i) ⊆
      e '' {z : Space | |z 0| ≤ a ∧ |z 1| ≤ b ∧ |z 2| ≤ 2})).card : ℝ) ≤
      (120 * b / s + 2) ^ 3 * (14 * b / s + 2) ^ 3 * P := by
  classical
  set SW := S.filter (fun i => Tube δ (x i) (v i) ⊆
    e '' {z : Space | |z 0| ≤ a ∧ |z 1| ≤ b ∧ |z 2| ≤ 2}) with hSW
  have hmemSW : ∀ i ∈ SW, i ∈ S ∧ Tube δ (x i) (v i) ⊆
      e '' {z : Space | |z 0| ≤ a ∧ |z 1| ≤ b ∧ |z 2| ≤ 2} := fun i hi =>
    Finset.mem_filter.mp hi
  have hb0 : 0 ≤ b := ha.trans hab
  have hclose : ∀ i ∈ SW, ∀ j ∈ SW,
      ‖lineFoot (x i) (v i) - lineFoot (x j) (v j)‖ ≤ 60 * b ∧ ‖v i - v j‖ ≤ 7 * b := by
    intro i hi j hj
    obtain ⟨hiS, hiW⟩ := hmemSW i hi
    obtain ⟨hjS, hjW⟩ := hmemSW j hj
    obtain ⟨hfoot, hdir⟩ := tube_params_close_of_box hδ hab hb e (hv i hiS) (hv j hjS)
      (hball j hjS) hiW hjW
    refine ⟨hfoot, ?_⟩
    rcases hdir with h | h
    · exact h
    · have := hanti i hiS j hjS
      linarith
  have himg := card_lineCells_le SW (fun i => lineFoot (x i) (v i)) v hs
    (by positivity : (0 : ℝ) ≤ 60 * b) (by positivity : (0 : ℝ) ≤ 7 * b)
    (fun i hi j hj => (hclose i hi j hj).1) (fun i hi j hj => (hclose i hi j hj).2)
  -- each cell holds at most `P` tubes of `SW`
  set f : Fin n → (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun i => lineGridCell s (x i) (v i) with hf
  have hcard : (SW.card : ℝ) ≤ ((SW.image f).card : ℝ) * P := by
    rw [Finset.card_eq_sum_card_image f SW]
    push_cast
    calc ∑ g ∈ SW.image f, ((SW.filter (fun i => f i = g)).card : ℝ)
        ≤ ∑ _g ∈ SW.image f, P := by
          apply Finset.sum_le_sum
          intro g hg
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
          have hiS := (hmemSW i hi).1
          refine le_trans ?_ (hpop i hiS)
          exact_mod_cast Finset.card_le_card (fun j hj => by
            obtain ⟨hjSW, hji⟩ := Finset.mem_filter.mp hj
            exact Finset.mem_filter.mpr ⟨(hmemSW j hjSW).1, hji⟩)
      _ = ((SW.image f).card : ℝ) * P := by rw [Finset.sum_const, nsmul_eq_mul]
  have himg' : ((SW.image f).card : ℝ) ≤ (120 * b / s + 2) ^ 3 * (14 * b / s + 2) ^ 3 := by
    have e1 : (2 * (60 * b) / s + 2) = 120 * b / s + 2 := by ring
    have e2 : (2 * (7 * b) / s + 2) = 14 * b / s + 2 := by ring
    rw [← e1, ← e2]
    exact himg
  calc (SW.card : ℝ) ≤ ((SW.image f).card : ℝ) * P := hcard
    _ ≤ (120 * b / s + 2) ^ 3 * (14 * b / s + 2) ^ 3 * P :=
        mul_le_mul_of_nonneg_right himg' hP

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
