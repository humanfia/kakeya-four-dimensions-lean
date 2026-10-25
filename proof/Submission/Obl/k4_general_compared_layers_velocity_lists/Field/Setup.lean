-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Setup; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Lists.Interface

/-!
# Normalized coordinates of one original true block

For an original true block `Q` at depth `r`, with block length `q = 2^(-T)`,
transverse width `w = q * N^(-ℓ r)` and coefficients `c = p.c k r Q`, an incidence
`(l, t)` has the normalized coordinates

* `τ = (t - t_Q) / q`                       (block time),
* `ζ = (Z - c 0 - c 1 * t) / q`             (major coordinate),
* `U = (Y - c 2 - c 3 * t - c 4 * Z) / w`  (transverse coordinate),

and the native signal `P(x)`. A projected quadratic `G(t, Y)` restricted to the
tilted plane `Y = Y_Q(t, Z) + w U` is `A + B U + D U^2`, where `B` is affine in
`(t, Z)` and `D` is constant (`transA`, `transB`, `transD`).
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Length `2^(-T)` of the original blocks at depth `r`. -/
def blockLen (k : ℕ) (r : ℝ) : ℝ := ((2 : ℝ) ^ p.T k r)⁻¹

/-- Start time of an original block. -/
def blockStart (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) : ℝ :=
  ((p.j k r Q : ℕ) : ℝ) / (2 : ℝ) ^ p.T k r

/-- Transverse width `2^(-T) N^(-ℓ r)` of the original blocks at depth `r`. -/
def blockWidth (k : ℕ) (r : ℝ) : ℝ := p.blockLen k r * p.N k ^ (-p.ℓ * r)

/-- The tilted transverse center `Y_Q(t, Z) = c 2 + c 3 t + c 4 Z`. -/
def tiltY (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (t Z : ℝ) : ℝ :=
  p.c k r Q 2 + p.c k r Q 3 * t + p.c k r Q 4 * Z

/-- Normalized block time. -/
def tauN (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (ω : α × ℝ) : ℝ :=
  (ω.2 - p.blockStart k r Q) / p.blockLen k r

/-- Normalized major coordinate. -/
def zetaN (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (ω : α × ℝ) : ℝ :=
  (p.x k ω.1 ω.2 1 - p.c k r Q 0 - p.c k r Q 1 * ω.2) / p.blockLen k r

/-- Normalized transverse coordinate. -/
def uN (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (ω : α × ℝ) : ℝ :=
  (p.x k ω.1 ω.2 2 - p.tiltY k r Q ω.2 (p.x k ω.1 ω.2 1)) / p.blockWidth k r

/-- The native fine state of an incidence in a block: base cells of side `δb`
in normalized `(τ, ζ, U)` and a native signal bin of width `δs`. -/
def nativeState (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (δb δs : ℝ) (ω : α × ℝ) : Fin 4 → ℤ :=
  ![⌊p.tauN k r Q ω / δb⌋, ⌊p.zetaN k r Q ω / δb⌋, ⌊p.uN k r Q ω / δb⌋,
    ⌊p.signal k ω.1 ω.2 / δs⌋]

theorem measurable_tauN (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) :
    Measurable (p.tauN k r Q) := by
  unfold tauN
  fun_prop

theorem measurable_zetaN {k : ℕ} (hb : Measurable (p.b k)) (r : ℝ) (Q : Fin (p.n k r)) :
    Measurable (p.zetaN k r Q) := by
  unfold zetaN Submission.Obl.k4_critical_intercept_concentration.Data.x
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  fun_prop

theorem measurable_uN {k : ℕ} (hb : Measurable (p.b k)) (r : ℝ) (Q : Fin (p.n k r)) :
    Measurable (p.uN k r Q) := by
  unfold uN tiltY Submission.Obl.k4_critical_intercept_concentration.Data.x
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  fun_prop

theorem measurable_signal {k : ℕ} (hb : Measurable (p.b k)) :
    Measurable (fun ω : α × ℝ => p.signal k ω.1 ω.2) := by
  unfold signal
  have hx : Measurable (fun ω : α × ℝ => p.x k ω.1 ω.2) := by
    unfold Submission.Obl.k4_critical_intercept_concentration.Data.x
    apply Measurable.of_eval
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (MvPolynomial.continuous_eval (p.P k)).measurable.comp hx

theorem measurable_nativeState {k : ℕ} (hb : Measurable (p.b k)) (r : ℝ) (Q : Fin (p.n k r))
    (δb δs : ℝ) : Measurable (p.nativeState k r Q δb δs) := by
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact ((p.measurable_tauN k r Q).div_const δb).floor
  · exact ((p.measurable_zetaN hb r Q).div_const δb).floor
  · exact ((p.measurable_uN hb r Q).div_const δb).floor
  · exact ((p.measurable_signal hb).div_const δs).floor

end Parent

/-- The value of a projected quadratic `G(t, Y)` on the tilted center. -/
def transA (G : MvPolynomial (Fin 2) ℝ) (Y : ℝ → ℝ → ℝ) (t Z : ℝ) : ℝ :=
  eval ![t, Y t Z] G

/-- The transverse slope coefficient: `w * ∂_Y G` on the tilted center. -/
def transB (G : MvPolynomial (Fin 2) ℝ) (Y : ℝ → ℝ → ℝ) (w t Z : ℝ) : ℝ :=
  w * eval ![t, Y t Z] (pderiv 1 G)

/-- The transverse curvature coefficient `w^2 * ∂_Y^2 G / 2` (constant in degree two). -/
def transD (G : MvPolynomial (Fin 2) ℝ) (w : ℝ) : ℝ :=
  w ^ 2 / 2 * eval ![0, 0] (pderiv 1 (pderiv 1 G))

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
