-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.Plates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Basic
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file Plates.lean), namespace renamed.

/-!
# Level-i plates: a tube in the standard prism, rescaled

`scaleLin a b = diag(1/a, 1/b, 1)` maps the standard prism `[-a,a]×[-b,b]×[-1,1]` to the unit
cube. `plate_sandwich`: a `δ`-tube contained in `stdBox a b` (with `δ ≤ a ≤ b ≤ 1`, `a ≤ 1/4`)
is mapped to a convex body which contains a box with half widths
`(δ/(5b))/10, (3δ/(5a))/10, 1/10` and lies in the concentric box with half widths
`10·δ/(5b), 10·3δ/(5a), 10`, in an orthonormal frame `e₁, e₂, e₃`.
-/

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

noncomputable section

/-- Diagonal scaling `diag(1/a, 1/b, 1)` in standard coordinates. -/
def scaleLin (a b : ℝ) : Space →ₗ[ℝ] Space :=
  ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm : (Fin 3 → ℝ) →ₗ[ℝ] Space) ∘ₗ
    Matrix.toLin' (Matrix.diagonal ![a⁻¹, b⁻¹, 1]) ∘ₗ
      ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.symm : Space →ₗ[ℝ] (Fin 3 → ℝ))

lemma scaleLin_apply (a b : ℝ) (p : Space) :
    scaleLin a b p = WithLp.toLp 2 ![p 0 / a, p 1 / b, p 2] := by
  ext i
  fin_cases i <;> simp [scaleLin, Matrix.toLin'_apply, Matrix.mulVec_diagonal] <;> ring

lemma scaleLin_coord (a b : ℝ) (p : Space) :
    scaleLin a b p 0 = p 0 / a ∧ scaleLin a b p 1 = p 1 / b ∧ scaleLin a b p 2 = p 2 := by
  rw [scaleLin_apply]
  simp

lemma scaleLin_det (a b : ℝ) : LinearMap.det (scaleLin a b) = a⁻¹ * b⁻¹ := by
  unfold scaleLin
  rw [LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_three]
  simp

lemma volume_scaleLin_image {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (S : Set Space) :
    volume (scaleLin a b '' S) = ENNReal.ofReal (a * b)⁻¹ * volume S := by
  rw [Measure.addHaar_image_linearMap, scaleLin_det, mul_inv]
  congr 2
  rw [abs_of_pos (by positivity)]

lemma inner_coords (p q : Space) : inner ℝ p q = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_three]
  ring

lemma norm_sq_coords (p : Space) : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

end

noncomputable section

lemma norm_sub_inner_smul_sq {q v : Space} (hv : ‖v‖ = 1) :
    ‖q - inner ℝ q v • v‖ ^ 2 = ‖q‖ ^ 2 - (inner ℝ q v) ^ 2 := by
  rw [@norm_sub_sq_real, inner_smul_right, norm_smul, hv]
  simp only [Real.norm_eq_abs, mul_one, sq_abs]
  ring

lemma vec3_apply (α β γ : ℝ) :
    (WithLp.toLp 2 ![α, β, γ] : Space) 0 = α ∧ (WithLp.toLp 2 ![α, β, γ] : Space) 1 = β ∧
      (WithLp.toLp 2 ![α, β, γ] : Space) 2 = γ := by
  simp

lemma vec3_ext (p : Space) : p = WithLp.toLp 2 ![p 0, p 1, p 2] := by
  ext i
  fin_cases i <;> simp


end

noncomputable section

/-- Expansion in an orthonormal triple. -/
lemma eq_sum_triple {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) (q : Space) :
    q = inner ℝ e₁ q • e₁ + inner ℝ e₂ q • e₂ + inner ℝ e₃ q • e₃ := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ Space := by simp
  let B := OrthonormalBasis.mk he
    (Submodule.eq_top_of_finrank_eq (by
      rw [finrank_span_eq_card he.linearIndependent]
      simp)).ge
  have h := B.sum_repr' q
  rw [Fin.sum_univ_three] at h
  simp only [B, OrthonormalBasis.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  exact h.symm

lemma scaleLin_inv_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (p : Space) :
    scaleLin a b (scaleLin a⁻¹ b⁻¹ p) = p := by
  rw [scaleLin_apply, scaleLin_apply]
  ext i
  fin_cases i <;> simp <;> field_simp

lemma inner_scaleLin_comm (a b : ℝ) (p q : Space) :
    inner ℝ p (scaleLin a b q) = inner ℝ (scaleLin a b p) q := by
  rw [inner_coords, inner_coords, scaleLin_apply, scaleLin_apply]
  simp
  ring

end

noncomputable section

/-- Real algebra behind the plate frame. -/
structure PlateReal (a b v0 v1 v2 : ℝ) : Prop where
  ha : 0 < a
  hab : a ≤ b
  hb1 : b ≤ 1
  ha4 : a ≤ 1 / 4
  hv : v0 ^ 2 + v1 ^ 2 + v2 ^ 2 = 1
  h0 : |v0| ≤ 2 * a
  h1 : |v1| ≤ 2 * b

namespace PlateReal

variable {a b v0 v1 v2 : ℝ} (h : PlateReal a b v0 v1 v2)
include h

lemma hb : 0 < b := h.ha.trans_le h.hab

lemma v0sq : v0 ^ 2 ≤ 4 * a ^ 2 := by
  have := h.h0; have ha := h.ha
  nlinarith [abs_nonneg v0, sq_abs v0]

lemma v1sq : v1 ^ 2 ≤ 4 * b ^ 2 := by
  have := h.h1; have hb := h.hb
  nlinarith [abs_nonneg v1, sq_abs v1]

/-- `S = v1²/b² + v2²`. -/
lemma S_ge : 3 / 4 ≤ v1 ^ 2 / b ^ 2 + v2 ^ 2 := by
  have hb := h.hb
  have h1 : v1 ^ 2 ≤ v1 ^ 2 / b ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg v1, h.hb1, sq_nonneg b, pow_le_one₀ hb.le h.hb1 (n := 2)]
  have h2 := h.v0sq; have h3 := h.hv
  have h4 : a ^ 2 ≤ 1 / 16 := by nlinarith [h.ha, h.ha4]
  nlinarith

lemma S_le : v1 ^ 2 / b ^ 2 + v2 ^ 2 ≤ 5 := by
  have hb := h.hb
  have h1 : v1 ^ 2 / b ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    exact h.v1sq
  nlinarith [h.hv, sq_nonneg v0, sq_nonneg v1]

lemma v0a_le : v0 ^ 2 / a ^ 2 ≤ 4 := by
  rw [div_le_iff₀ (by have := h.ha; positivity)]
  exact h.v0sq

/-- `Λ² ≥ 1`. -/
lemma lam_sq_ge : 1 ≤ v0 ^ 2 / a ^ 2 + (v1 ^ 2 / b ^ 2 + v2 ^ 2) := by
  have ha := h.ha; have hb := h.hb
  have e0 : v0 ^ 2 ≤ v0 ^ 2 / a ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg v0, pow_le_one₀ ha.le (h.hab.trans h.hb1) (n := 2)]
  have e1 : v1 ^ 2 ≤ v1 ^ 2 / b ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg v1, pow_le_one₀ hb.le h.hb1 (n := 2)]
  nlinarith [h.hv]

end PlateReal

end

noncomputable section

/-- Orthonormality of the explicit plate frame. -/
lemma plate_frame_orthonormal {a b v0 v1 v2 S rS L Λ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hS : S = v1 ^ 2 / b ^ 2 + v2 ^ 2) (hrS : rS ^ 2 = S) (hrS0 : 0 < rS)
    (hL : L = v0 ^ 2 / a ^ 2 + S) (hΛ : Λ ^ 2 = L) (hΛ0 : 0 < Λ) :
    Orthonormal ℝ ![(WithLp.toLp 2 ![0, v2 / rS, -(v1 / (b * rS))] : Space),
      WithLp.toLp 2 ![rS / Λ, -(v0 * v1 / (a * b * Λ * rS)), -(v0 * v2 / (a * Λ * rS))],
      WithLp.toLp 2 ![v0 / (a * Λ), v1 / (b * Λ), v2 / Λ]] := by
  have hne : rS ≠ 0 := hrS0.ne'
  have hΛne : Λ ≠ 0 := hΛ0.ne'
  have hb2 : b ^ 2 ≠ 0 := by positivity
  have ha2 : a ^ 2 ≠ 0 := by positivity
  have hrS2 : rS ^ 2 * b ^ 2 = v1 ^ 2 + b ^ 2 * v2 ^ 2 := by
    rw [hrS, hS]; field_simp
  have hΛ2 : Λ ^ 2 * a ^ 2 * b ^ 2 = v0 ^ 2 * b ^ 2 + a ^ 2 * (v1 ^ 2 + b ^ 2 * v2 ^ 2) := by
    rw [hΛ, hL, hS]; field_simp
  have unit (p : Space) (hp : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1) : ‖p‖ = 1 := by
    have h := norm_sq_coords p
    rw [hp] at h
    have h0 : 0 ≤ ‖p‖ := norm_nonneg p
    nlinarith
  rw [orthonormal_iff_ite]
  intro i j
  have hSpos : 0 < S := by rw [← hrS]; positivity
  have hLpos : 0 < L := by rw [← hΛ]; positivity
  have n1 : (0 : ℝ) ^ 2 + (v2 / rS) ^ 2 + (-(v1 / (b * rS))) ^ 2 = 1 := by
    have e : (0 : ℝ) ^ 2 + (v2 / rS) ^ 2 + (-(v1 / (b * rS))) ^ 2 =
        (v1 ^ 2 / b ^ 2 + v2 ^ 2) / rS ^ 2 := by field_simp; ring
    rw [e, hrS, ← hS, div_self hSpos.ne']
  have n3 : (v0 / (a * Λ)) ^ 2 + (v1 / (b * Λ)) ^ 2 + (v2 / Λ) ^ 2 = 1 := by
    have e : (v0 / (a * Λ)) ^ 2 + (v1 / (b * Λ)) ^ 2 + (v2 / Λ) ^ 2 =
        (v0 ^ 2 / a ^ 2 + (v1 ^ 2 / b ^ 2 + v2 ^ 2)) / Λ ^ 2 := by field_simp; ring
    rw [e, hΛ, ← hS, ← hL, div_self hLpos.ne']
  have n2 : (rS / Λ) ^ 2 + (-(v0 * v1 / (a * b * Λ * rS))) ^ 2 +
      (-(v0 * v2 / (a * Λ * rS))) ^ 2 = 1 := by
    have e : (rS / Λ) ^ 2 + (-(v0 * v1 / (a * b * Λ * rS))) ^ 2 +
        (-(v0 * v2 / (a * Λ * rS))) ^ 2 =
        (rS ^ 2 + v0 ^ 2 / a ^ 2 * (v1 ^ 2 / b ^ 2 + v2 ^ 2) / rS ^ 2) / Λ ^ 2 := by
      field_simp; ring
    rw [e, ← hS, hrS, mul_div_assoc, div_self hSpos.ne', mul_one, add_comm, ← hL, hΛ,
      div_self hLpos.ne']
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, ite_true]
    rw [real_inner_self_eq_norm_sq, unit _ (by simpa using n1)]
    norm_num
  · simp [inner_coords]; field_simp; ring
  · simp [inner_coords]; field_simp; ring
  · simp [inner_coords]; field_simp; ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, ite_true]
    rw [real_inner_self_eq_norm_sq, unit _ (by simpa using n2)]
    norm_num
  · simp [inner_coords]; field_simp; linear_combination v0 * hrS2
  · simp [inner_coords]; field_simp; ring
  · simp [inner_coords]; field_simp; linear_combination v0 * hrS2
  · simp only [Fin.reduceFinMk, Matrix.cons_val, ite_true]
    rw [real_inner_self_eq_norm_sq, unit _ (by simpa using n3)]
    norm_num

end

noncomputable section

namespace PlateReal

variable {a b v0 v1 v2 : ℝ} (h : PlateReal a b v0 v1 v2)
include h

/-- `‖P_{v⊥} D⁻¹ e₁‖² ≤ 9 b²`, in the form `num ≤ 9 b² S`. -/
lemma thin_reach :
    b ^ 2 * v2 ^ 2 + v1 ^ 2 / b ^ 2 - v1 ^ 2 * v2 ^ 2 * (b - 1 / b) ^ 2 ≤
      9 * b ^ 2 * (v1 ^ 2 / b ^ 2 + v2 ^ 2) := by
  have hb := h.hb
  set S := v1 ^ 2 / b ^ 2 + v2 ^ 2 with hSdef
  have hid : b ^ 2 * v2 ^ 2 + v1 ^ 2 / b ^ 2 - v1 ^ 2 * v2 ^ 2 * (b - 1 / b) ^ 2 =
      b ^ 2 * S ^ 2 + v0 ^ 2 * (v1 ^ 2 / b ^ 2 + b ^ 2 * v2 ^ 2) := by
    have hv0 : v0 ^ 2 = 1 - v1 ^ 2 - v2 ^ 2 := by linarith [h.hv]
    rw [hv0, hSdef]
    field_simp
    ring
  have hS0 : 0 ≤ S := by positivity
  have hS5 := h.S_le
  have hX : v1 ^ 2 / b ^ 2 + b ^ 2 * v2 ^ 2 ≤ S := by
    have : b ^ 2 ≤ 1 := pow_le_one₀ hb.le h.hb1
    rw [hSdef]
    nlinarith [sq_nonneg v2]
  have hv0 := h.v0sq
  have hab2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ h.ha.le h.hab 2
  rw [hid]
  have h1 : b ^ 2 * S ^ 2 ≤ 5 * b ^ 2 * S := by
    have := mul_le_mul_of_nonneg_left hS5 (by positivity : 0 ≤ b ^ 2 * S)
    nlinarith
  have h2 : v0 ^ 2 * (v1 ^ 2 / b ^ 2 + b ^ 2 * v2 ^ 2) ≤ 4 * b ^ 2 * S := by
    have := mul_le_mul hv0 hX (by positivity) (by positivity)
    nlinarith
  linarith

/-- `‖P_{v⊥} D⁻¹ e₂‖² ≤ 5 a²`, in the form `W Λ² ≤ 5 S` with `W = v1² + v2²`. -/
lemma wide_reach :
    (v1 ^ 2 + v2 ^ 2) * (v0 ^ 2 / a ^ 2 + (v1 ^ 2 / b ^ 2 + v2 ^ 2)) ≤
      5 * (v1 ^ 2 / b ^ 2 + v2 ^ 2) := by
  have hb := h.hb
  have hW : v1 ^ 2 + v2 ^ 2 ≤ v1 ^ 2 / b ^ 2 + v2 ^ 2 := by
    have : v1 ^ 2 ≤ v1 ^ 2 / b ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg v1, pow_le_one₀ hb.le h.hb1 (n := 2)]
    linarith
  have hW1 : v1 ^ 2 + v2 ^ 2 ≤ 1 := by nlinarith [h.hv, sq_nonneg v0]
  have h4 := h.v0a_le
  have hS0 : 0 ≤ v1 ^ 2 / b ^ 2 + v2 ^ 2 := by positivity
  have ha' : (v1 ^ 2 + v2 ^ 2) * (v0 ^ 2 / a ^ 2) ≤ (v1 ^ 2 / b ^ 2 + v2 ^ 2) * 4 :=
    mul_le_mul hW h4 (by positivity) hS0
  have hb' : (v1 ^ 2 + v2 ^ 2) * (v1 ^ 2 / b ^ 2 + v2 ^ 2) ≤ 1 * (v1 ^ 2 / b ^ 2 + v2 ^ 2) :=
    mul_le_mul_of_nonneg_right hW1 hS0
  rw [mul_add]
  linarith

end PlateReal

end

noncomputable section

lemma scaleLin_inv_apply' (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (p : Space) :
    scaleLin a⁻¹ b⁻¹ (scaleLin a b p) = p := by
  rw [scaleLin_apply, scaleLin_apply]
  ext i
  fin_cases i <;> simp <;> field_simp

lemma norm_le_of_sq_le {p : Space} {K : ℝ} (hK : 0 ≤ K) (h : ‖p‖ ^ 2 ≤ K ^ 2) : ‖p‖ ≤ K := by
  nlinarith [norm_nonneg p]

lemma norm_vec3_sq (α β γ : ℝ) : ‖(WithLp.toLp 2 ![α, β, γ] : Space)‖ ^ 2 = α ^ 2 + β ^ 2 + γ ^ 2 := by
  rw [norm_sq_coords]; simp

/-- The standard prism `[-a,a] × [-b,b] × [-1,1]`. -/
def stdBox (a b : ℝ) : Set Space := {p | |p 0| ≤ a ∧ |p 1| ≤ b ∧ |p 2| ≤ 1}

lemma coord_add (x v : Space) (i : Fin 3) : (x + v) i = x i + v i := rfl

lemma dir_bounds {a b δ : ℝ} (hδ : 0 < δ) {x v : Space}
    (hT : thickening δ (segment ℝ x (x + v)) ⊆ stdBox a b) :
    |v 0| ≤ 2 * a ∧ |v 1| ≤ 2 * b := by
  have hx := hT (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have hxv := hT (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  simp only [stdBox, Set.mem_ofPred_eq, coord_add] at hx hxv
  constructor
  · have : v 0 = (x 0 + v 0) - x 0 := by ring
    rw [this]
    exact (abs_sub _ _).trans (by linarith [hx.1, hxv.1])
  · have : v 1 = (x 1 + v 1) - x 1 := by ring
    rw [this]
    exact (abs_sub _ _).trans (by linarith [hx.2.1, hxv.2.1])

end

noncomputable section


noncomputable section

lemma De1_sq {a b v1 v2 S rS : ℝ} (hb : 0 < b) (hrS : rS ^ 2 = S) (hrS0 : 0 < rS)
    (hW : v1 ^ 2 + v2 ^ 2 ≤ S) :
    (0 / a) ^ 2 + (v2 / rS / b) ^ 2 + (-(v1 / (b * rS))) ^ 2 ≤ (1 / b) ^ 2 := by
  have e : (0 / a) ^ 2 + (v2 / rS / b) ^ 2 + (-(v1 / (b * rS))) ^ 2 =
      (v1 ^ 2 + v2 ^ 2) / (b ^ 2 * rS ^ 2) := by
    rw [zero_div]; field_simp; ring
  have hS0 : 0 < S := by rw [← hrS]; positivity
  rw [e, hrS, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma De2_sq {a b v0 v1 v2 S rS L Λ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hrS : rS ^ 2 = S) (hrS0 : 0 < rS) (hΛ : Λ ^ 2 = L) (hΛ0 : 0 < Λ)
    (hS : S = v1 ^ 2 / b ^ 2 + v2 ^ 2) (hSL : S ≤ L) (hL1 : 1 ≤ L) (hv0 : v0 ^ 2 ≤ 4 * a ^ 2) :
    (rS / Λ / a) ^ 2 + (-(v0 * v1 / (a * b * Λ * rS)) / b) ^ 2 +
      (-(v0 * v2 / (a * Λ * rS))) ^ 2 ≤ (3 / a) ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hS0 : 0 < S := by rw [← hrS]; positivity
  have e : (rS / Λ / a) ^ 2 + (-(v0 * v1 / (a * b * Λ * rS)) / b) ^ 2 +
      (-(v0 * v2 / (a * Λ * rS))) ^ 2 =
      (rS ^ 2 * rS ^ 2 + v0 ^ 2 * (v1 ^ 2 / b ^ 4 + v2 ^ 2)) / (a ^ 2 * Λ ^ 2 * rS ^ 2) := by
    field_simp; ring
  have hq1 : v1 ^ 2 / b ^ 4 + v2 ^ 2 ≤ S / b ^ 2 := by
    have hb2 : b ^ 2 ≤ 1 := pow_le_one₀ hb.le hb1
    rw [hS, add_div, show b ^ 4 = b ^ 2 * b ^ 2 by ring, ← div_div]
    have : v2 ^ 2 ≤ v2 ^ 2 / b ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg v2]
    linarith
  have hab2 : a ^ 2 / b ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr (pow_le_pow_left₀ ha.le hab 2)
  have hq2 : v0 ^ 2 * (v1 ^ 2 / b ^ 4 + v2 ^ 2) ≤ 4 * S := by
    have h1 := mul_le_mul hv0 hq1 (by positivity) (by positivity)
    have h2 : 4 * a ^ 2 * (S / b ^ 2) = 4 * S * (a ^ 2 / b ^ 2) := by ring
    have h3 : 4 * S * (a ^ 2 / b ^ 2) ≤ 4 * S := by
      have := mul_le_mul_of_nonneg_left hab2 (by positivity : 0 ≤ 4 * S)
      linarith
    linarith
  have hLpos : 0 < L := by linarith
  rw [e, hrS, hΛ, div_pow, div_le_div_iff₀ (mul_pos (mul_pos (pow_pos ha 2) hLpos) hS0)
    (by positivity)]
  have h4 : S * S ≤ S * L := mul_le_mul_of_nonneg_left hSL hS0.le
  have h5 : 4 * S ≤ 4 * S * L := by
    have := mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ 4 * S)
    linarith
  have h6 : S * S + v0 ^ 2 * (v1 ^ 2 / b ^ 4 + v2 ^ 2) ≤ 9 * (L * S) := by nlinarith
  have := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ a ^ 2)
  nlinarith

lemma De3_sq {a b v0 v1 v2 L Λ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hΛ : Λ ^ 2 = L) (hΛ0 : 0 < Λ) (hL : L = v0 ^ 2 / a ^ 2 + (v1 ^ 2 / b ^ 2 + v2 ^ 2)) :
    (v0 / (a * Λ) / a) ^ 2 + (v1 / (b * Λ) / b) ^ 2 + (v2 / Λ) ^ 2 ≤ (1 / a) ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have e : (v0 / (a * Λ) / a) ^ 2 + (v1 / (b * Λ) / b) ^ 2 + (v2 / Λ) ^ 2 =
      (v0 ^ 2 / a ^ 4 + v1 ^ 2 / b ^ 4 + v2 ^ 2) / Λ ^ 2 := by field_simp
  have t1 : v1 ^ 2 / b ^ 4 ≤ (v1 ^ 2 / b ^ 2) / a ^ 2 := by
    rw [show b ^ 4 = b ^ 2 * b ^ 2 by ring, ← div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ ha.le hab 2
  have t2 : v2 ^ 2 ≤ v2 ^ 2 / a ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg v2, pow_le_one₀ ha.le (hab.trans hb1) (n := 2)]
  have hsum : v0 ^ 2 / a ^ 4 + v1 ^ 2 / b ^ 4 + v2 ^ 2 ≤ L / a ^ 2 := by
    have : L / a ^ 2 = (v0 ^ 2 / a ^ 2) / a ^ 2 + (v1 ^ 2 / b ^ 2) / a ^ 2 + v2 ^ 2 / a ^ 2 := by
      rw [hL]; ring
    rw [this, show v0 ^ 2 / a ^ 4 = (v0 ^ 2 / a ^ 2) / a ^ 2 by ring]
    linarith
  have hLpos : 0 < L := by rw [← hΛ]; positivity
  rw [e, hΛ, div_pow, one_pow, div_le_div_iff₀ hLpos (by positivity)]
  have := mul_le_mul_of_nonneg_right hsum (by positivity : (0 : ℝ) ≤ a ^ 2)
  rw [div_mul_cancel₀ _ (by positivity)] at this
  linarith

end


noncomputable section

/-- `‖P_{v⊥} g₁‖² = num / S` for the thin frame vector. -/
lemma thin_proj_sq {b v0 v1 v2 S rS : ℝ} (hb : 0 < b) (hrS : rS ^ 2 = S) (hrS0 : 0 < rS) :
    (0 : ℝ) ^ 2 + (b * (v2 / rS)) ^ 2 + (-(v1 / (b * rS))) ^ 2 -
      (0 * v0 + b * (v2 / rS) * v1 + -(v1 / (b * rS)) * v2) ^ 2 =
    (b ^ 2 * v2 ^ 2 + v1 ^ 2 / b ^ 2 - v1 ^ 2 * v2 ^ 2 * (b - 1 / b) ^ 2) / S := by
  rw [← hrS]
  field_simp
  ring

/-- `‖P_{v⊥} g₂‖² = W a² L / S` for the wide frame vector. -/
lemma wide_proj_sq {a v0 v1 v2 S rS L Λ : ℝ} (ha : 0 < a) (hrS : rS ^ 2 = S) (hrS0 : 0 < rS)
    (hΛ : Λ ^ 2 = L) (hΛ0 : 0 < Λ) (hL : L = v0 ^ 2 / a ^ 2 + S)
    (hv : v0 ^ 2 + v1 ^ 2 + v2 ^ 2 = 1) :
    (a * (rS / Λ)) ^ 2 + (-(v0 * v1 / (a * Λ * rS))) ^ 2 + (-(v0 * v2 / (a * Λ * rS))) ^ 2 -
      (a * (rS / Λ) * v0 + -(v0 * v1 / (a * Λ * rS)) * v1 + -(v0 * v2 / (a * Λ * rS)) * v2) ^ 2 =
    (v1 ^ 2 + v2 ^ 2) * a ^ 2 * L / S := by
  have hS0 : 0 < S := by rw [← hrS]; positivity
  have hW : v1 ^ 2 + v2 ^ 2 = 1 - v0 ^ 2 := by linarith
  have hL' : L * a ^ 2 = v0 ^ 2 + a ^ 2 * S := by rw [hL]; field_simp
  rw [← hrS] at hL' ⊢
  rw [← hΛ] at hL' ⊢
  field_simp
  rw [hW]
  have hW' : v1 ^ 2 = 1 - v0 ^ 2 - v2 ^ 2 := by linarith
  rw [hW']
  linear_combination (-(1 - v0 ^ 2) * (a ^ 2 * rS ^ 2 + v0 ^ 2 + Λ ^ 2 * a ^ 2)) * hL'

end


/-- `S = v₁²/b² + v₂²`. -/
def plateS (b : ℝ) (v : Space) : ℝ := v 1 ^ 2 / b ^ 2 + v 2 ^ 2
/-- `Λ² = v₀²/a² + S`. -/
def plateL (a b : ℝ) (v : Space) : ℝ := v 0 ^ 2 / a ^ 2 + plateS b v
/-- The thin direction. -/
def plateE1 (b : ℝ) (v : Space) : Space :=
  WithLp.toLp 2 ![0, v 2 / Real.sqrt (plateS b v), -(v 1 / (b * Real.sqrt (plateS b v)))]
/-- The wide direction. -/
def plateE2 (a b : ℝ) (v : Space) : Space :=
  WithLp.toLp 2 ![Real.sqrt (plateS b v) / Real.sqrt (plateL a b v),
    -(v 0 * v 1 / (a * b * Real.sqrt (plateL a b v) * Real.sqrt (plateS b v))),
    -(v 0 * v 2 / (a * Real.sqrt (plateL a b v) * Real.sqrt (plateS b v)))]
/-- The long direction. -/
def plateE3 (a b : ℝ) (v : Space) : Space :=
  WithLp.toLp 2 ![v 0 / (a * Real.sqrt (plateL a b v)), v 1 / (b * Real.sqrt (plateL a b v)),
    v 2 / Real.sqrt (plateL a b v)]
/-- The centre of the plate. -/
def plateC (a b : ℝ) (x v : Space) : Space := scaleLin a b (x + (1 / 2 : ℝ) • v)

lemma plate_orth {a b δ : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (ha4 : a ≤ 1 / 4) {x v : Space} (hv : ‖v‖ = 1)
    (hT : thickening δ (segment ℝ x (x + v)) ⊆ stdBox a b) :
    Orthonormal ℝ ![plateE1 b v, plateE2 a b v, plateE3 a b v] := by
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨h0, h1⟩ := dir_bounds hδ hT
  have hvsq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by rw [← norm_sq_coords, hv]; norm_num
  have hR : PlateReal a b (v 0) (v 1) (v 2) := ⟨ha, hab, hb1, ha4, hvsq, h0, h1⟩
  set v0 := v 0 with hv0
  set v1 := v 1 with hv1
  set v2 := v 2 with hv2
  set S := v1 ^ 2 / b ^ 2 + v2 ^ 2 with hSdef
  have hSdef' : plateS b v = S := rfl
  have hS34 : 3 / 4 ≤ S := hR.S_ge
  have hS5 : S ≤ 5 := hR.S_le
  have hS0 : 0 < S := by linarith
  set L := v0 ^ 2 / a ^ 2 + S with hLdef
  have hLdef' : plateL a b v = L := rfl
  have hL1 : 1 ≤ L := hR.lam_sq_ge
  have hL9 : L ≤ 9 := by have := hR.v0a_le; linarith
  set rS := Real.sqrt S with hrSdef
  set Λ := Real.sqrt L with hΛdef
  have hrS : rS ^ 2 = S := Real.sq_sqrt hS0.le
  have hΛ : Λ ^ 2 = L := Real.sq_sqrt (by linarith)
  have hrS0 : 0 < rS := Real.sqrt_pos.mpr hS0
  have hΛ0 : 0 < Λ := Real.sqrt_pos.mpr (by linarith)
  have hΛ1 : 1 ≤ Λ := by nlinarith
  have hΛ3 : Λ ≤ 3 := by nlinarith
  set e₁ : Space := WithLp.toLp 2 ![0, v2 / rS, -(v1 / (b * rS))] with he₁
  have he₁' : plateE1 b v = e₁ := rfl
  set e₂ : Space := WithLp.toLp 2 ![rS / Λ, -(v0 * v1 / (a * b * Λ * rS)), -(v0 * v2 / (a * Λ * rS))]
    with he₂
  have he₂' : plateE2 a b v = e₂ := rfl
  set e₃ : Space := WithLp.toLp 2 ![v0 / (a * Λ), v1 / (b * Λ), v2 / Λ] with he₃
  have he₃' : plateE3 a b v = e₃ := rfl
  have horth : Orthonormal ℝ ![e₁, e₂, e₃] :=
    plate_frame_orthonormal ha hb hSdef hrS hrS0 hLdef hΛ hΛ0
  set c : Space := scaleLin a b (x + (1 / 2 : ℝ) • v) with hc
  have hc' : plateC a b x v = c := rfl
  have hDv : scaleLin a b v = Λ • e₃ := by
    rw [scaleLin_apply, he₃]
    ext i
    fin_cases i <;> simp [hv0, hv1, hv2] <;> field_simp
  have i13 : inner ℝ e₁ e₃ = 0 := by
    have := horth.2 (show (0 : Fin 3) ≠ 2 by decide); simpa using this
  have i23 : inner ℝ e₂ e₃ = 0 := by
    have := horth.2 (show (1 : Fin 3) ≠ 2 by decide); simpa using this
  have n3 : ‖e₃‖ = 1 := by simpa using horth.1 2
  have i33 : inner ℝ e₃ e₃ = 1 := by
    rw [real_inner_self_eq_norm_sq, n3]; norm_num
  rw [he₁', he₂', he₃']
  exact horth

set_option maxHeartbeats 1000000 in
lemma plate_inner {a b δ : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (ha4 : a ≤ 1 / 4) {x v : Space} (hv : ‖v‖ = 1)
    (hT : thickening δ (segment ℝ x (x + v)) ⊆ stdBox a b) :
    {y | |inner ℝ (plateE1 b v) (y - plateC a b x v)| ≤ δ / (5 * b) / 10 ∧
        |inner ℝ (plateE2 a b v) (y - plateC a b x v)| ≤ 3 * δ / (5 * a) / 10 ∧
        |inner ℝ (plateE3 a b v) (y - plateC a b x v)| ≤ 1 / 10} ⊆
      scaleLin a b '' thickening δ (segment ℝ x (x + v)) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨h0, h1⟩ := dir_bounds hδ hT
  have hvsq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by rw [← norm_sq_coords, hv]; norm_num
  have hR : PlateReal a b (v 0) (v 1) (v 2) := ⟨ha, hab, hb1, ha4, hvsq, h0, h1⟩
  set v0 := v 0 with hv0
  set v1 := v 1 with hv1
  set v2 := v 2 with hv2
  set S := v1 ^ 2 / b ^ 2 + v2 ^ 2 with hSdef
  have hSdef' : plateS b v = S := rfl
  have hS34 : 3 / 4 ≤ S := hR.S_ge
  have hS5 : S ≤ 5 := hR.S_le
  have hS0 : 0 < S := by linarith
  set L := v0 ^ 2 / a ^ 2 + S with hLdef
  have hLdef' : plateL a b v = L := rfl
  have hL1 : 1 ≤ L := hR.lam_sq_ge
  have hL9 : L ≤ 9 := by have := hR.v0a_le; linarith
  set rS := Real.sqrt S with hrSdef
  set Λ := Real.sqrt L with hΛdef
  have hrS : rS ^ 2 = S := Real.sq_sqrt hS0.le
  have hΛ : Λ ^ 2 = L := Real.sq_sqrt (by linarith)
  have hrS0 : 0 < rS := Real.sqrt_pos.mpr hS0
  have hΛ0 : 0 < Λ := Real.sqrt_pos.mpr (by linarith)
  have hΛ1 : 1 ≤ Λ := by nlinarith
  have hΛ3 : Λ ≤ 3 := by nlinarith
  set e₁ : Space := WithLp.toLp 2 ![0, v2 / rS, -(v1 / (b * rS))] with he₁
  have he₁' : plateE1 b v = e₁ := rfl
  set e₂ : Space := WithLp.toLp 2 ![rS / Λ, -(v0 * v1 / (a * b * Λ * rS)), -(v0 * v2 / (a * Λ * rS))]
    with he₂
  have he₂' : plateE2 a b v = e₂ := rfl
  set e₃ : Space := WithLp.toLp 2 ![v0 / (a * Λ), v1 / (b * Λ), v2 / Λ] with he₃
  have he₃' : plateE3 a b v = e₃ := rfl
  have horth : Orthonormal ℝ ![e₁, e₂, e₃] :=
    plate_frame_orthonormal ha hb hSdef hrS hrS0 hLdef hΛ hΛ0
  set c : Space := scaleLin a b (x + (1 / 2 : ℝ) • v) with hc
  have hc' : plateC a b x v = c := rfl
  have hDv : scaleLin a b v = Λ • e₃ := by
    rw [scaleLin_apply, he₃]
    ext i
    fin_cases i <;> simp [hv0, hv1, hv2] <;> field_simp
  have i13 : inner ℝ e₁ e₃ = 0 := by
    have := horth.2 (show (0 : Fin 3) ≠ 2 by decide); simpa using this
  have i23 : inner ℝ e₂ e₃ = 0 := by
    have := horth.2 (show (1 : Fin 3) ≠ 2 by decide); simpa using this
  have n3 : ‖e₃‖ = 1 := by simpa using horth.1 2
  have i33 : inner ℝ e₃ e₃ = 1 := by
    rw [real_inner_self_eq_norm_sq, n3]; norm_num
  rw [he₁', he₂', he₃', hc']
  rintro y ⟨hy1, hy2, hy3⟩
  set β₁ := inner ℝ e₁ (y - c) with hβ₁
  set β₂ := inner ℝ e₂ (y - c) with hβ₂
  set β₃ := inner ℝ e₃ (y - c) with hβ₃
  have hexp : y - c = β₁ • e₁ + β₂ • e₂ + β₃ • e₃ := eq_sum_triple horth (y - c)
  refine ⟨scaleLin a⁻¹ b⁻¹ y, ?_, scaleLin_inv_apply a b ha.ne' hb.ne' y⟩
  set g₁ := scaleLin a⁻¹ b⁻¹ e₁ with hg₁
  set g₂ := scaleLin a⁻¹ b⁻¹ e₂ with hg₂
  have hg3 : scaleLin a⁻¹ b⁻¹ e₃ = Λ⁻¹ • v := by
    rw [scaleLin_apply, he₃]
    ext i
    fin_cases i <;> simp [hv0, hv1, hv2] <;> field_simp
  have hcinv : scaleLin a⁻¹ b⁻¹ c = x + (1 / 2 : ℝ) • v :=
    scaleLin_inv_apply' a b ha.ne' hb.ne' _
  set c₁ := inner ℝ g₁ v with hc₁
  set c₂ := inner ℝ g₂ v with hc₂
  set w := β₁ • (g₁ - c₁ • v) + β₂ • (g₂ - c₂ • v) with hw
  set τ := 1 / 2 + β₃ / Λ + β₁ * c₁ + β₂ * c₂ with hτ
  have hz : scaleLin a⁻¹ b⁻¹ y = x + τ • v + w := by
    have hy : y = c + (β₁ • e₁ + β₂ • e₂ + β₃ • e₃) := by rw [← hexp]; abel
    rw [hy, map_add, hcinv, map_add, map_add, map_smul, map_smul, map_smul, hg3, hw, hτ]
    module
  -- the thin and wide reaches
  have hg1c : g₁ = WithLp.toLp 2 ![0, b * (v2 / rS), -(v1 / (b * rS))] := by
    rw [hg₁, scaleLin_apply, he₁]
    ext i
    fin_cases i <;> simp <;> ring
  have hg2c : g₂ = WithLp.toLp 2 ![a * (rS / Λ), -(v0 * v1 / (a * Λ * rS)),
      -(v0 * v2 / (a * Λ * rS))] := by
    rw [hg₂, scaleLin_apply, he₂]
    ext i
    fin_cases i <;> simp <;> field_simp
  have hP1 : ‖g₁ - c₁ • v‖ ≤ 3 * b := by
    apply norm_le_of_sq_le (by positivity)
    rw [norm_sub_inner_smul_sq hv, hg1c, norm_vec3_sq, inner_coords]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← hv0, ← hv1, ← hv2, thin_proj_sq hb hrS hrS0, div_le_iff₀ hS0]
    have := hR.thin_reach
    rw [← hSdef] at this
    calc _ ≤ 9 * b ^ 2 * S := this
      _ = (3 * b) ^ 2 * S := by ring
  have hP2 : ‖g₂ - c₂ • v‖ ≤ 3 * a := by
    apply norm_le_of_sq_le (by positivity)
    rw [norm_sub_inner_smul_sq hv, hg2c, norm_vec3_sq, inner_coords]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← hv0, ← hv1, ← hv2, wide_proj_sq ha hrS hrS0 hΛ hΛ0 hLdef hvsq, div_le_iff₀ hS0]
    have := hR.wide_reach
    rw [← hSdef, ← hLdef] at this
    have h9 : (v1 ^ 2 + v2 ^ 2) * L ≤ 9 * S := by linarith
    calc (v1 ^ 2 + v2 ^ 2) * a ^ 2 * L = a ^ 2 * ((v1 ^ 2 + v2 ^ 2) * L) := by ring
      _ ≤ a ^ 2 * (9 * S) := mul_le_mul_of_nonneg_left h9 (by positivity)
      _ = (3 * a) ^ 2 * S := by ring
  have hg1n : ‖g₁‖ ≤ 1 := by
    apply norm_le_of_sq_le zero_le_one
    rw [hg1c, norm_vec3_sq]
    have e : (0 : ℝ) ^ 2 + (b * (v2 / rS)) ^ 2 + (-(v1 / (b * rS))) ^ 2 =
        (b ^ 2 * v2 ^ 2 + v1 ^ 2 / b ^ 2) / rS ^ 2 := by field_simp; ring
    rw [e, hrS, div_le_iff₀ hS0, one_pow, one_mul, hSdef]
    have : b ^ 2 * v2 ^ 2 ≤ v2 ^ 2 := by
      nlinarith [sq_nonneg v2, pow_le_one₀ hb.le hb1 (n := 2)]
    linarith
  have hg2n : ‖g₂‖ ≤ 1 := by
    apply norm_le_of_sq_le zero_le_one
    rw [hg2c, norm_vec3_sq]
    have e : (a * (rS / Λ)) ^ 2 + (-(v0 * v1 / (a * Λ * rS))) ^ 2 +
        (-(v0 * v2 / (a * Λ * rS))) ^ 2 =
        (a ^ 2 * rS ^ 2 + v0 ^ 2 * (v1 ^ 2 + v2 ^ 2) / (a ^ 2 * rS ^ 2)) / Λ ^ 2 := by
      field_simp; ring
    have hW : v1 ^ 2 + v2 ^ 2 ≤ S := by
      have : v1 ^ 2 ≤ v1 ^ 2 / b ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg v1, pow_le_one₀ hb.le hb1 (n := 2)]
      rw [hSdef]; linarith
    rw [e, hrS, hΛ, div_le_iff₀ (by linarith), one_pow, one_mul, hLdef]
    have t1 : a ^ 2 * S ≤ S := by
      nlinarith [pow_le_one₀ ha.le (hab.trans hb1) (n := 2)]
    have t2 : v0 ^ 2 * (v1 ^ 2 + v2 ^ 2) / (a ^ 2 * S) ≤ v0 ^ 2 / a ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hW (by positivity : (0 : ℝ) ≤ v0 ^ 2 * a ^ 2)
      nlinarith
    linarith
  have hc1 : |c₁| ≤ 1 := (abs_real_inner_le_norm g₁ v).trans (by rw [hv, mul_one]; exact hg1n)
  have hc2 : |c₂| ≤ 1 := (abs_real_inner_le_norm g₂ v).trans (by rw [hv, mul_one]; exact hg2n)
  have hδb : δ / b ≤ 1 := (div_le_one hb).mpr (hδa.trans hab)
  have hδa' : δ / a ≤ 1 := (div_le_one ha).mpr hδa
  have hb1' : |β₁| ≤ δ / b / 50 := by
    have : δ / (5 * b) / 10 = δ / b / 50 := by field_simp; ring
    rw [← this]; exact hy1
  have hb2' : |β₂| ≤ 3 * (δ / a) / 50 := by
    have : 3 * δ / (5 * a) / 10 = 3 * (δ / a) / 50 := by field_simp; ring
    rw [← this]; exact hy2
  have hwn : ‖w‖ < δ := by
    calc ‖w‖ ≤ |β₁| * ‖g₁ - c₁ • v‖ + |β₂| * ‖g₂ - c₂ • v‖ := by
          rw [hw]
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
            rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (δ / b / 50) * (3 * b) + (3 * (δ / a) / 50) * (3 * a) :=
          add_le_add (mul_le_mul hb1' hP1 (norm_nonneg _) (by positivity))
            (mul_le_mul hb2' hP2 (norm_nonneg _) (by positivity))
      _ = 12 * δ / 50 := by field_simp; ring
      _ < δ := by linarith
  have hβ3' : |β₃ / Λ| ≤ 1 / 10 := by
    rw [abs_div, abs_of_pos hΛ0, div_le_iff₀ hΛ0]
    exact hy3.trans (le_mul_of_one_le_right (by norm_num) hΛ1)
  have hm1 : |β₁ * c₁| ≤ 1 / 50 := by
    rw [abs_mul]
    calc |β₁| * |c₁| ≤ (δ / b / 50) * 1 := mul_le_mul hb1' hc1 (abs_nonneg _) (by positivity)
      _ ≤ 1 / 50 := by linarith
  have hm2 : |β₂ * c₂| ≤ 3 / 50 := by
    rw [abs_mul]
    calc |β₂| * |c₂| ≤ (3 * (δ / a) / 50) * 1 := mul_le_mul hb2' hc2 (abs_nonneg _) (by positivity)
      _ ≤ 3 / 50 := by linarith
  have hτ0 : 0 ≤ τ := by
    rw [hτ]
    linarith [neg_abs_le (β₃ / Λ), neg_abs_le (β₁ * c₁), neg_abs_le (β₂ * c₂)]
  have hτ1 : τ ≤ 1 := by
    rw [hτ]
    linarith [le_abs_self (β₃ / Λ), le_abs_self (β₁ * c₁), le_abs_self (β₂ * c₂)]
  rw [hz]
  refine mem_thickening_iff.mpr ⟨x + τ • v, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨τ, ⟨hτ0, hτ1⟩, by simp⟩
  · rw [dist_eq_norm, show x + τ • v + w - (x + τ • v) = w by abel]
    exact hwn

set_option maxHeartbeats 1000000 in
lemma plate_outer {a b δ : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (ha4 : a ≤ 1 / 4) {x v : Space} (hv : ‖v‖ = 1)
    (hT : thickening δ (segment ℝ x (x + v)) ⊆ stdBox a b) :
    scaleLin a b '' thickening δ (segment ℝ x (x + v)) ⊆
      {y | |inner ℝ (plateE1 b v) (y - plateC a b x v)| ≤ 10 * (δ / (5 * b)) ∧
        |inner ℝ (plateE2 a b v) (y - plateC a b x v)| ≤ 10 * (3 * δ / (5 * a)) ∧
        |inner ℝ (plateE3 a b v) (y - plateC a b x v)| ≤ 10} := by
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨h0, h1⟩ := dir_bounds hδ hT
  have hvsq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by rw [← norm_sq_coords, hv]; norm_num
  have hR : PlateReal a b (v 0) (v 1) (v 2) := ⟨ha, hab, hb1, ha4, hvsq, h0, h1⟩
  set v0 := v 0 with hv0
  set v1 := v 1 with hv1
  set v2 := v 2 with hv2
  set S := v1 ^ 2 / b ^ 2 + v2 ^ 2 with hSdef
  have hSdef' : plateS b v = S := rfl
  have hS34 : 3 / 4 ≤ S := hR.S_ge
  have hS5 : S ≤ 5 := hR.S_le
  have hS0 : 0 < S := by linarith
  set L := v0 ^ 2 / a ^ 2 + S with hLdef
  have hLdef' : plateL a b v = L := rfl
  have hL1 : 1 ≤ L := hR.lam_sq_ge
  have hL9 : L ≤ 9 := by have := hR.v0a_le; linarith
  set rS := Real.sqrt S with hrSdef
  set Λ := Real.sqrt L with hΛdef
  have hrS : rS ^ 2 = S := Real.sq_sqrt hS0.le
  have hΛ : Λ ^ 2 = L := Real.sq_sqrt (by linarith)
  have hrS0 : 0 < rS := Real.sqrt_pos.mpr hS0
  have hΛ0 : 0 < Λ := Real.sqrt_pos.mpr (by linarith)
  have hΛ1 : 1 ≤ Λ := by nlinarith
  have hΛ3 : Λ ≤ 3 := by nlinarith
  set e₁ : Space := WithLp.toLp 2 ![0, v2 / rS, -(v1 / (b * rS))] with he₁
  have he₁' : plateE1 b v = e₁ := rfl
  set e₂ : Space := WithLp.toLp 2 ![rS / Λ, -(v0 * v1 / (a * b * Λ * rS)), -(v0 * v2 / (a * Λ * rS))]
    with he₂
  have he₂' : plateE2 a b v = e₂ := rfl
  set e₃ : Space := WithLp.toLp 2 ![v0 / (a * Λ), v1 / (b * Λ), v2 / Λ] with he₃
  have he₃' : plateE3 a b v = e₃ := rfl
  have horth : Orthonormal ℝ ![e₁, e₂, e₃] :=
    plate_frame_orthonormal ha hb hSdef hrS hrS0 hLdef hΛ hΛ0
  set c : Space := scaleLin a b (x + (1 / 2 : ℝ) • v) with hc
  have hc' : plateC a b x v = c := rfl
  have hDv : scaleLin a b v = Λ • e₃ := by
    rw [scaleLin_apply, he₃]
    ext i
    fin_cases i <;> simp [hv0, hv1, hv2] <;> field_simp
  have i13 : inner ℝ e₁ e₃ = 0 := by
    have := horth.2 (show (0 : Fin 3) ≠ 2 by decide); simpa using this
  have i23 : inner ℝ e₂ e₃ = 0 := by
    have := horth.2 (show (1 : Fin 3) ≠ 2 by decide); simpa using this
  have n3 : ‖e₃‖ = 1 := by simpa using horth.1 2
  have i33 : inner ℝ e₃ e₃ = 1 := by
    rw [real_inner_self_eq_norm_sq, n3]; norm_num
  rw [he₁', he₂', he₃', hc']
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨q, hq, hzq⟩ := mem_thickening_iff.mp hz
  rw [segment_eq_image'] at hq
  obtain ⟨τ, ⟨hτ0, hτ1⟩, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hzq
  set w := z - (x + τ • v) with hw
  have hwn : ‖w‖ < δ := by rw [hw, ← dist_eq_norm]; exact hzq
  have hdiff : scaleLin a b z - c = (τ - 1 / 2) • (Λ • e₃) + scaleLin a b w := by
    rw [hc, ← hDv, ← map_sub, ← map_smul, ← map_add]
    congr 1
    rw [hw]
    module
  have hW : v1 ^ 2 + v2 ^ 2 ≤ S := by
    have : v1 ^ 2 ≤ v1 ^ 2 / b ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg v1, pow_le_one₀ hb.le hb1 (n := 2)]
    rw [hSdef]; linarith
  have hD1 : ‖scaleLin a b e₁‖ ≤ 1 / b := by
    apply norm_le_of_sq_le (by positivity)
    rw [scaleLin_apply, he₁, norm_vec3_sq]
    simpa using De1_sq (a := a) hb hrS hrS0 hW
  have hSL : S ≤ L := by
    have : 0 ≤ v0 ^ 2 / a ^ 2 := by positivity
    rw [hLdef]; linarith
  have hD2 : ‖scaleLin a b e₂‖ ≤ 3 / a := by
    apply norm_le_of_sq_le (by positivity)
    rw [scaleLin_apply, he₂, norm_vec3_sq]
    simpa using De2_sq ha hab hb1 hrS hrS0 hΛ hΛ0 hSdef hSL hL1 hR.v0sq
  have hD3 : ‖scaleLin a b e₃‖ ≤ 1 / a := by
    apply norm_le_of_sq_le (by positivity)
    rw [scaleLin_apply, he₃, norm_vec3_sq]
    simpa using De3_sq ha hab hb1 hΛ hΛ0 hLdef
  refine ⟨?_, ?_, ?_⟩
  · rw [hdiff, inner_add_right, inner_smul_right, inner_smul_right, i13, mul_zero, mul_zero,
      zero_add, inner_scaleLin_comm]
    calc |inner ℝ (scaleLin a b e₁) w| ≤ ‖scaleLin a b e₁‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ (1 / b) * δ := mul_le_mul hD1 hwn.le (norm_nonneg _) (by positivity)
      _ ≤ 10 * (δ / (5 * b)) := by
          rw [show (1 / b) * δ = δ / b by ring, show 10 * (δ / (5 * b)) = 2 * (δ / b) by
            field_simp; ring]
          have : 0 ≤ δ / b := by positivity
          linarith
  · rw [hdiff, inner_add_right, inner_smul_right, inner_smul_right, i23, mul_zero, mul_zero,
      zero_add, inner_scaleLin_comm]
    calc |inner ℝ (scaleLin a b e₂) w| ≤ ‖scaleLin a b e₂‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ (3 / a) * δ := mul_le_mul hD2 hwn.le (norm_nonneg _) (by positivity)
      _ ≤ 10 * (3 * δ / (5 * a)) := by
          rw [show (3 / a) * δ = 3 * (δ / a) by ring, show 10 * (3 * δ / (5 * a)) = 6 * (δ / a) by
            field_simp; ring]
          have : 0 ≤ δ / a := by positivity
          linarith
  · rw [hdiff, inner_add_right, inner_smul_right, inner_smul_right, i33, mul_one,
      inner_scaleLin_comm]
    have hτ : |τ - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc |(τ - 1 / 2) * Λ + inner ℝ (scaleLin a b e₃) w|
        ≤ |τ - 1 / 2| * Λ + ‖scaleLin a b e₃‖ * ‖w‖ := by
          refine (abs_add_le _ _).trans (add_le_add ?_ (abs_real_inner_le_norm _ _))
          rw [abs_mul, abs_of_pos hΛ0]
      _ ≤ 1 / 2 * 3 + (1 / a) * a := by
          gcongr
          exact hwn.le.trans hδa
      _ ≤ 10 := by field_simp; norm_num



/-- The rescaled tube is sandwiched between two boxes of the plate frame. -/
theorem plate_sandwich {a b δ : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (ha4 : a ≤ 1 / 4) {x v : Space} (hv : ‖v‖ = 1)
    (hT : thickening δ (segment ℝ x (x + v)) ⊆ stdBox a b) :
    ∃ c e₁ e₂ e₃ : Space, Orthonormal ℝ ![e₁, e₂, e₃] ∧
      {y | |inner ℝ e₁ (y - c)| ≤ δ / (5 * b) / 10 ∧
        |inner ℝ e₂ (y - c)| ≤ 3 * δ / (5 * a) / 10 ∧
        |inner ℝ e₃ (y - c)| ≤ 1 / 10} ⊆ scaleLin a b '' thickening δ (segment ℝ x (x + v)) ∧
      scaleLin a b '' thickening δ (segment ℝ x (x + v)) ⊆
        {y | |inner ℝ e₁ (y - c)| ≤ 10 * (δ / (5 * b)) ∧
          |inner ℝ e₂ (y - c)| ≤ 10 * (3 * δ / (5 * a)) ∧ |inner ℝ e₃ (y - c)| ≤ 10} :=
  ⟨plateC a b x v, plateE1 b v, plateE2 a b v, plateE3 a b v,
    plate_orth hδ hδa hab hb1 ha4 hv hT, plate_inner hδ hδa hab hb1 ha4 hv hT,
    plate_outer hδ hδa hab hb1 ha4 hv hT⟩

end

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
