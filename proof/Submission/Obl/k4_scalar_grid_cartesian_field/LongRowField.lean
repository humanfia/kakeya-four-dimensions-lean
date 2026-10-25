import Submission.Lib.K4PolynomialRemez
import Submission.Lib.K4PolynomialPotential.TrajectoryFits

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4PolynomialPotential

/-- The physical derivative minus the polynomial field, expressed in normalized block time. -/
noncomputable def fieldResidual (T : Fin 2 → MvPolynomial (Fin 2) ℝ)
    (l : Fin 5 → ℝ) (a h y₀ : ℝ) : Polynomial ℝ :=
  Polynomial.C (l 3 + 2 * a * l 4) + Polynomial.C (2 * h * l 4) * Polynomial.X -
    scalarLineHom ((l 0 + a * l 1 - y₀) / h) (l 1) (T 0) -
    Polynomial.C (l 1) * scalarLineHom ((l 0 + a * l 1 - y₀) / h) (l 1) (T 1)

theorem fieldResidual_degree (T : Fin 2 → MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hT : ∀ e, (T e).totalDegree ≤ D) (l : Fin 5 → ℝ) (a h y₀ : ℝ) :
    (fieldResidual T l a h y₀).natDegree ≤ D + 1 := by
  unfold fieldResidual
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · rw [Polynomial.natDegree_C]; omega
      · exact Polynomial.natDegree_mul_le.trans (by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]; omega)
    · exact (natDegree_scalarLineHom_le _ _ _).trans ((hT 0).trans (Nat.le_add_right _ _))
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((natDegree_scalarLineHom_le (T 1) _ _).trans
        ((hT 1).trans (Nat.le_add_right _ _)))

theorem eval_fieldResidual (T : Fin 2 → MvPolynomial (Fin 2) ℝ)
    (l : Fin 5 → ℝ) (a h y₀ τ : ℝ) (hh : h ≠ 0) :
    (fieldResidual T l a h y₀).eval τ =
      l 3 + 2 * (a + h * τ) * l 4 -
        ∑ e : Fin 2, MvPolynomial.eval
          (fun e : Fin 2 => ((![a + h * τ, l 0 + (a + h * τ) * l 1] : Fin 2 → ℝ) e -
            (![a, y₀] : Fin 2 → ℝ) e) / h) (T e) * (![1, l 1] : Fin 2 → ℝ) e := by
  have hbase : (fun e : Fin 2 =>
      ((![a + h * τ, l 0 + (a + h * τ) * l 1] : Fin 2 → ℝ) e -
        (![a, y₀] : Fin 2 → ℝ) e) / h) =
      ![τ, (l 0 + a * l 1 - y₀) / h + τ * l 1] := by
    funext e
    fin_cases e <;> simp <;> field_simp <;> ring
  rw [hbase]
  simp only [fieldResidual, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, eval_scalarLineHom,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
  ring

/-- Normalized-time preimages carry the original outer Lebesgue mass with the exact Jacobian. -/
theorem volume_affine_time_preimage (a : ℝ) {h : ℝ} (hh : 0 < h) (S : Set ℝ) :
    volume ((fun τ : ℝ => a + h * τ) ⁻¹' S) = ENNReal.ofReal h⁻¹ * volume S := by
  have hid : (fun τ : ℝ => a + h * τ) ⁻¹' S =
      (fun τ : ℝ => h • τ) ⁻¹' ((fun t : ℝ => t + a) ⁻¹' S) := by
    ext τ
    simp only [mem_preimage, smul_eq_mul, add_comm]
  rw [hid, volume.addHaar_preimage_smul hh.ne', measure_preimage_add_right]
  simp [abs_of_pos hh]

/-- A polynomial field comparison on any original long time row extends to the whole block. -/
theorem field_comparison_of_long_row
    (T : Fin 2 → MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hT : ∀ e, (T e).totalDegree ≤ D) (l : Fin 5 → ℝ) (a h y₀ : ℝ)
    (S : Set ℝ) {η E : ℝ} (hh : 0 < h) (hη : 0 < η) (hη1 : η ≤ 1)
    (hE : 0 ≤ E) (hS : S ⊆ Icc a (a + h))
    (hmass : ENNReal.ofReal (h * η) ≤ volume S)
    (hfit : ∀ t ∈ S,
      |l 3 + 2 * t * l 4 - ∑ e : Fin 2, MvPolynomial.eval
        (fun e : Fin 2 => ((![t, l 0 + t * l 1] : Fin 2 → ℝ) e -
          (![a, y₀] : Fin 2 → ℝ) e) / h) (T e) * (![1, l 1] : Fin 2 → ℝ) e| ≤ E) :
    ∀ t ∈ Icc a (a + h),
      |l 3 + 2 * t * l 4 - ∑ e : Fin 2, MvPolynomial.eval
        (fun e : Fin 2 => ((![t, l 0 + t * l 1] : Fin 2 → ℝ) e -
          (![a, y₀] : Fin 2 → ℝ) e) / h) (T e) * (![1, l 1] : Fin 2 → ℝ) e| ≤
        (8 * ((D : ℝ) + 2) / η) ^ (D + 1) * E := by
  let R := (fun τ : ℝ => a + h * τ) ⁻¹' S
  have hR : R ⊆ Icc (0 : ℝ) 1 := by
    intro τ hτ
    have := hS hτ
    constructor <;> nlinarith [this.1, this.2]
  have hRmass : ENNReal.ofReal η ≤ volume R := by
    rw [volume_affine_time_preimage a hh S]
    calc
      ENNReal.ofReal η = ENNReal.ofReal h⁻¹ * ENNReal.ofReal (h * η) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ h⁻¹)]
        congr 1
        field_simp
      _ ≤ ENNReal.ofReal h⁻¹ * volume S := mul_le_mul' le_rfl hmass
  have hbound : ∀ τ ∈ R, |(fieldResidual T l a h y₀).eval τ| ≤ E := by
    intro τ hτ
    rw [eval_fieldResidual T l a h y₀ τ hh.ne']
    exact hfit _ hτ
  have hremez := Submission.Lib.K4PolynomialRemez.polynomial_remez_unit
    (fieldResidual T l a h y₀) (D + 1) (fieldResidual_degree T D hT l a h y₀)
    R hη hη1 hE hR hRmass hbound
  intro t ht
  have hτ : (t - a) / h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [ht.1]) hh.le
    · exact (div_le_one hh).mpr (by linarith [ht.2])
  have hid : a + h * ((t - a) / h) = t := by field_simp; ring
  have hout := hremez ((t - a) / h) hτ
  rw [eval_fieldResidual T l a h y₀ _ hh.ne', hid] at hout
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc,
    show (1 : ℝ) + 1 = 2 by norm_num] using hout

end Submission.Obl.k4_scalar_grid_cartesian_field
