/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ZoomLabel.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.Zoom
import Submission.Lib.K4ContactNormalization.RowNormalization

/-!
# Box constants of a descendant after zoom and row normalization

The contact instance is read in the coordinates

`t' = (t - t₀)/q`, `x₁' = (x₁ - z₀)/q`,
`x₂'' = ((x₂ - c₂ - c₃ t - c₄ x₁)/(q g) - B₀ t' - B₁ x₁') / λ`,

i.e. the parent zoom followed by the row normalization (`skewCoeff`). A
descendant label with box constants `c` (major centre `c₀ + t c₁`, tilted
transverse box `c₂ + c₃ t + c₄ x₁`, velocity strip `c₃ + c₄ b₃`) has, in these
coordinates, the box constants `zoomBox`, and its three box inequalities are
divided exactly by `q`, `q g |λ|` and `g |λ|`.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open Submission.Lib.K4ContactNormalization (point skewCoeff)

noncomputable section

namespace Zoom

/-- Box constants of a descendant after the parent zoom (`w = q g`) and the row
normalization `(B, λ)`. -/
def zoomBox (Z : Zoom) (B : Fin 2 → ℝ) (lam : ℝ) (c : Fin 5 → ℝ) : Fin 5 → ℝ :=
  let g := Z.w / Z.q
  ![(c 0 + Z.t₀ * c 1 - Z.z₀) / Z.q,
    c 1,
    ((c 2 - Z.c₂) + (c 3 - Z.c₃) * Z.t₀ + (c 4 - Z.c₄) * Z.z₀) / (Z.w * lam),
    ((c 3 - Z.c₃) / g - B 0) / lam,
    ((c 4 - Z.c₄) / g - B 1) / lam]

/-- Normalized line coefficients: parent zoom, then row normalization. -/
def nCoeff (Z : Zoom) (B : Fin 2 → ℝ) (lam : ℝ) (b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  skewCoeff B lam (Z.coeff b)

variable {Z : Zoom} {B : Fin 2 → ℝ} {lam : ℝ}

theorem nCoeff_three (b : Fin 6 → ℝ) : nCoeff Z B lam b 3 = b 3 := by
  simp [nCoeff, skewCoeff, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff]

/-- The major box. -/
theorem major_box_zoom (hZ : Z.Ok) {b : Fin 6 → ℝ} {c : Fin 5 → ℝ} {t E : ℝ}
    (h : |b 0 + t * b 3 - c 0 - t * c 1| ≤ E) :
    |nCoeff Z B lam b 0 + Z.time t * nCoeff Z B lam b 3 - zoomBox Z B lam c 0 -
        Z.time t * zoomBox Z B lam c 1| ≤ E / |Z.q| := by
  have hq := hZ.q_ne
  have e : nCoeff Z B lam b 0 + Z.time t * nCoeff Z B lam b 3 - zoomBox Z B lam c 0 -
      Z.time t * zoomBox Z B lam c 1 = (b 0 + t * b 3 - c 0 - t * c 1) / Z.q := by
    simp only [nCoeff, skewCoeff, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff, zoomBox, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.time, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    field_simp
    ring
  rw [e, abs_div]
  exact div_le_div_of_nonneg_right h (abs_nonneg _)

/-- The transverse box. -/
theorem transverse_box_zoom (hZ : Z.Ok) (hlam : lam ≠ 0) {b : Fin 6 → ℝ}
    {c : Fin 5 → ℝ} {t E : ℝ}
    (h : |(b 1 + t * b 4) - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| ≤ E) :
    |(nCoeff Z B lam b 1 + Z.time t * nCoeff Z B lam b 4) - zoomBox Z B lam c 2 -
        Z.time t * zoomBox Z B lam c 3 -
        zoomBox Z B lam c 4 * (nCoeff Z B lam b 0 + Z.time t * nCoeff Z B lam b 3)| ≤
      E / |Z.w * lam| := by
  have hq := hZ.q_ne
  have hw := hZ.w_ne
  have e : (nCoeff Z B lam b 1 + Z.time t * nCoeff Z B lam b 4) - zoomBox Z B lam c 2 -
        Z.time t * zoomBox Z B lam c 3 -
        zoomBox Z B lam c 4 * (nCoeff Z B lam b 0 + Z.time t * nCoeff Z B lam b 3) =
      ((b 1 + t * b 4) - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)) / (Z.w * lam) := by
    simp only [nCoeff, skewCoeff, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff, zoomBox, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.time, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    field_simp
    ring
  rw [e, abs_div]
  exact div_le_div_of_nonneg_right h (abs_nonneg _)

/-- The velocity strip. -/
theorem strip_zoom (hZ : Z.Ok) (hlam : lam ≠ 0) {b : Fin 6 → ℝ} {c : Fin 5 → ℝ} {E : ℝ}
    (h : |b 4 - c 3 - c 4 * b 3| ≤ E) :
    |nCoeff Z B lam b 4 - zoomBox Z B lam c 3 - zoomBox Z B lam c 4 * nCoeff Z B lam b 3| ≤
      E / |Z.w / Z.q * lam| := by
  have hq := hZ.q_ne
  have hw := hZ.w_ne
  have e : nCoeff Z B lam b 4 - zoomBox Z B lam c 3 - zoomBox Z B lam c 4 * nCoeff Z B lam b 3 =
      (b 4 - c 3 - c 4 * b 3) / (Z.w / Z.q * lam) := by
    simp only [nCoeff, skewCoeff, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff, zoomBox, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    field_simp
    ring
  rw [e, abs_div]
  exact div_le_div_of_nonneg_right h (abs_nonneg _)

/-- The normalized contact quantity is the row equation divided by the skew. -/
theorem nCoeff_contact (hlam : lam ≠ 0) (b : Fin 6 → ℝ) :
    nCoeff Z B lam b 4 + nCoeff Z B lam b 0 =
      (Z.coeff b 4 - B 0 - B 1 * b 3 + lam * Z.coeff b 0) / lam := by
  simp only [nCoeff, skewCoeff, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue]
  field_simp

/-! ## Tests through zoom and row normalization -/

open MvPolynomial
open Submission.Lib.K4ContactNormalization (skewSubst unskewSubst skewBudget)
open Submission.Lib.K4ChartLifting (coeffL1)

variable (Z B lam) in
/-- An original test read in normalized coordinates, divided by the hidden width. -/
def nPush (F : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  bind₁ (unskewSubst B lam) (Z.push F)

variable (Z B lam) in
/-- A normalized test read in original coordinates, times the hidden width. -/
def nLift (Q : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  Z.lift (bind₁ (skewSubst B lam) Q)

theorem nPush_degree (F : MvPolynomial (Fin 4) ℝ) :
    (nPush Z B lam F).totalDegree ≤ F.totalDegree :=
  (Submission.Lib.K4ContactNormalization.degree_unskew_pullback B lam _).trans (push_degree F)

theorem nLift_degree (Q : MvPolynomial (Fin 4) ℝ) :
    (nLift Z B lam Q).totalDegree ≤ Q.totalDegree :=
  (lift_degree _).trans (Submission.Lib.K4ContactNormalization.degree_skew_pullback B lam Q)

theorem eval_nPush (hZ : Z.Ok) (hlam : lam ≠ 0) (F : MvPolynomial (Fin 4) ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point (nCoeff Z B lam b) t) (nPush Z B lam F) =
      Z.a⁻¹ * eval (point b (Z.untime t)) F := by
  rw [nPush, nCoeff, Submission.Lib.K4ContactNormalization.eval_unskew_pullback B hlam,
    eval_push, point_untime hZ, unpos_pos hZ]

theorem eval_pderiv_nPush (hZ : Z.Ok) (hlam : lam ≠ 0) (F : MvPolynomial (Fin 4) ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point (nCoeff Z B lam b) t) (pderiv 3 (nPush Z B lam F)) =
      eval (point b (Z.untime t)) (pderiv 3 F) := by
  rw [nPush, Submission.Lib.K4ContactNormalization.pderiv_unskew_pullback, nCoeff,
    Submission.Lib.K4ContactNormalization.eval_unskew_pullback B hlam, pderiv_push hZ,
    Submission.Lib.K4ChartLifting.eval_bind₁', eval_unsubst, point_untime hZ, unpos_pos hZ]

theorem eval_pderiv_pderiv_nPush (hZ : Z.Ok) (hlam : lam ≠ 0) (F : MvPolynomial (Fin 4) ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point (nCoeff Z B lam b) t) (pderiv 3 (pderiv 3 (nPush Z B lam F))) =
      Z.a * eval (point b (Z.untime t)) (pderiv 3 (pderiv 3 F)) := by
  rw [nPush, Submission.Lib.K4ContactNormalization.pderiv_unskew_pullback,
    Submission.Lib.K4ContactNormalization.pderiv_unskew_pullback, nCoeff,
    Submission.Lib.K4ContactNormalization.eval_unskew_pullback B hlam, eval_pderiv_pderiv_push hZ,
    point_untime hZ, unpos_pos hZ]

theorem eval_nLift (Q : MvPolynomial (Fin 4) ℝ) (hZ : Z.Ok) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point b t) (nLift Z B lam Q) =
      Z.a * eval (point (nCoeff Z B lam b) (Z.time t)) Q := by
  rw [nLift, eval_lift, pos_point hZ, Submission.Lib.K4ContactNormalization.eval_skew_pullback,
    nCoeff]

theorem eval_pderiv_nLift (Q : MvPolynomial (Fin 4) ℝ) (hZ : Z.Ok) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point b t) (pderiv 3 (nLift Z B lam Q)) =
      eval (point (nCoeff Z B lam b) (Z.time t)) (pderiv 3 Q) := by
  rw [nLift, eval_pderiv_lift hZ, pos_point hZ,
    Submission.Lib.K4ContactNormalization.pderiv_skew_pullback,
    Submission.Lib.K4ContactNormalization.eval_skew_pullback, nCoeff]

/-- Original fits push to normalized fits at width `c / a`. -/
theorem nPush_fits (hZ : Z.Ok) (ha : 0 < Z.a) (hlam : lam ≠ 0)
    {F : MvPolynomial (Fin 4) ℝ} {b : Fin 6 → ℝ} {I : Set ℝ} {H c : ℝ}
    (h : Fits F b I H c) :
    Fits (nPush Z B lam F) (nCoeff Z B lam b) (Z.untime ⁻¹' I) H (c / Z.a) := by
  have hp := push_fits (Z := Z) hZ ha h
  intro t ht
  obtain ⟨h1, h2, h3⟩ := hp t ht
  simpa only [nPush, Submission.Lib.K4ContactNormalization.pderiv_unskew_pullback, nCoeff,
    Submission.Lib.K4ContactNormalization.eval_unskew_pullback B hlam] using
    (⟨h1, h2, h3⟩ : _ ∧ _ ∧ _)

/-- Normalized fits lift to original fits at width `a * c`. -/
theorem nLift_fits (hZ : Z.Ok) (ha : 0 < Z.a) {Q : MvPolynomial (Fin 4) ℝ}
    {b : Fin 6 → ℝ} {I : Set ℝ} {H c : ℝ}
    (h : Fits Q (nCoeff Z B lam b) I H c) :
    Fits (nLift Z B lam Q) b (Z.time ⁻¹' I) H (Z.a * c) := by
  apply lift_fits hZ ha
  have := (Submission.Lib.K4ContactNormalization.skew_fit_iff B lam Q (Z.coeff b) I H c).mpr h
  exact this

/-- Coefficients of a lifted normalized test. -/
theorem coeff_nLift_le (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2)
    (e : Fin 4 →₀ ℕ) :
    |(nLift Z B lam Q).coeff e| ≤
      |Z.a| * (coeffL1 Q * skewBudget B lam ^ 2 * (((2 + 1) ^ 4 : ℕ) : ℝ)) *
        Z.liftBudget ^ 2 := by
  have hdeg : (bind₁ (skewSubst B lam) Q).totalDegree ≤ 2 :=
    (Submission.Lib.K4ContactNormalization.degree_skew_pullback B lam Q).trans hQ
  have h1 := coeff_lift_le (Z := Z) (bind₁ (skewSubst B lam) Q) hdeg e
  have h2 : coeffL1 (bind₁ (skewSubst B lam) Q) ≤
      coeffL1 Q * skewBudget B lam ^ 2 * (((2 + 1) ^ 4 : ℕ) : ℝ) := by
    have := Submission.Lib.K4ChartLifting.coeffL1_le_of_coeff_le
      (bind₁ (skewSubst B lam) Q) hdeg (coeffL1 Q * skewBudget B lam ^ 2)
      (Submission.Lib.K4ContactNormalization.coeff_skew_pullback_le B lam Q hQ)
    linarith
  calc |(nLift Z B lam Q).coeff e| ≤ |Z.a| * coeffL1 (bind₁ (skewSubst B lam) Q) *
        Z.liftBudget ^ 2 := h1
    _ ≤ |Z.a| * (coeffL1 Q * skewBudget B lam ^ 2 * (((2 + 1) ^ 4 : ℕ) : ℝ)) *
        Z.liftBudget ^ 2 := by
        gcongr

end Zoom

end

end Submission.Obl.k4_row_parent_contact_candidates
