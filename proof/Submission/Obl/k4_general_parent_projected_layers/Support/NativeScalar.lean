/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/NativeScalar.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ContactAlgebra
import Submission.Obl.k4_uncapped_native_capping.NativeCoordinates
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Scalar coefficients for the unchanged native signal and a cropped transverse coordinate. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set

noncomputable section

local instance nativeScalarPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

open Submission.Obl.k4_uncapped_native_capping (scalarX scalarY nativeCoeff)

/-- Clipping is on a measurable set of original labels; the signal itself is not rescaled. -/
def nativeScalarCoefficients {α : Type} (P : MvPolynomial (Fin 4) ℝ)
    (b : α → Fin 6 → ℝ) (g y₀ y₁ : ℝ) (C : Set α) (l : α) : Fin 5 → ℝ :=
  if l ∈ C then nativeCoeff P 0 1 (-y₀ / g) ![-y₁ / g, 0, g⁻¹] univ (0, b l) else 0

theorem measurable_nativeScalarCoefficients {α : Type} [MeasurableSpace α]
    (P : MvPolynomial (Fin 4) ℝ) {b : α → Fin 6 → ℝ} (hb : Measurable b)
    (g y₀ y₁ : ℝ) {C : Set α} (hC : MeasurableSet C) :
    Measurable (nativeScalarCoefficients P b g y₀ y₁ C) := by
  unfold nativeScalarCoefficients
  apply Measurable.ite hC
  · exact (Submission.Obl.k4_uncapped_native_capping.measurable_nativeCoeff
      P 0 1 (-y₀ / g) ![-y₁ / g, 0, g⁻¹] MeasurableSet.univ).comp
        (measurable_const.prodMk hb)
  · exact measurable_const

theorem nativeScalarCoefficients_y {α : Type} (P : MvPolynomial (Fin 4) ℝ)
    (b : α → Fin 6 → ℝ) (g y₀ y₁ : ℝ) {C : Set α} {l : α} (hl : l ∈ C) (t : ℝ) :
    scalarY (nativeScalarCoefficients P b g y₀ y₁ C l) t =
      (trajectory (b l) t 2 - y₀ - t * y₁) / g := by
  rw [nativeScalarCoefficients, if_pos hl]
  rw [Submission.Obl.k4_uncapped_native_capping.nativeCoeff_scalarY P 0 1
    (-y₀ / g) ![-y₁ / g, 0, g⁻¹] (mem_univ _) t]
  simp [Fin.sum_univ_three, Submission.Obl.k4_finite_width_output_exclusion.x,
    trajectory, Submission.Lib.K4ContactNormalization.point, div_eq_mul_inv]
  ring

theorem nativeScalarCoefficients_x {α : Type} (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (b : α → Fin 6 → ℝ) (g y₀ y₁ : ℝ)
    {C : Set α} {l : α} (hl : l ∈ C) (t : ℝ) :
    scalarX (nativeScalarCoefficients P b g y₀ y₁ C l) t =
      MvPolynomial.eval (trajectory (b l) t) P := by
  rw [nativeScalarCoefficients, if_pos hl]
  simpa [Submission.Obl.k4_finite_width_output_exclusion.x,
    trajectory, Submission.Lib.K4ContactNormalization.point] using
    Submission.Obl.k4_uncapped_native_capping.nativeCoeff_scalarX P hP 0 1
      (-y₀ / g) ![-y₁ / g, 0, g⁻¹] (mem_univ (0, b l)) t

/-- Only the three bounded native sample values enter the global coefficient bound. -/
theorem nativeScalarCoefficients_bound {α : Type} (P : MvPolynomial (Fin 4) ℝ)
    (b : α → Fin 6 → ℝ) {g y₀ y₁ H : ℝ} (hg : 0 < g) (hH : 0 ≤ H)
    {C : Set α}
    (hy : ∀ l ∈ C, |b l 1 - y₀| ≤ H * g ∧ |b l 4 - y₁| ≤ H * g)
    (hx : ∀ l ∈ C, ∀ t ∈ ({0, 1 / 2, 1} : Finset ℝ),
      |MvPolynomial.eval (trajectory (b l) t) P| ≤ H)
    (l : α) (i : Fin 5) :
    |nativeScalarCoefficients P b g y₀ y₁ C l i| ≤ 8 * H := by
  classical
  by_cases hl : l ∈ C
  · have h₀ := hx l hl 0 (by simp)
    have hm := hx l hl (1 / 2) (by simp)
    have h₁ := hx l hl 1 (by simp)
    have hy₀ : |(b l 1 - y₀) / g| ≤ H := by
      rw [abs_div, abs_of_pos hg, div_le_iff₀ hg]
      exact (hy l hl).1
    have hy₁ : |(b l 4 - y₁) / g| ≤ H := by
      rw [abs_div, abs_of_pos hg, div_le_iff₀ hg]
      exact (hy l hl).2
    have hform : nativeScalarCoefficients P b g y₀ y₁ C l =
        ![(b l 1 - y₀) / g, (b l 4 - y₁) / g,
          MvPolynomial.eval (trajectory (b l) 0) P,
          4 * MvPolynomial.eval (trajectory (b l) (1 / 2)) P -
            3 * MvPolynomial.eval (trajectory (b l) 0) P -
              MvPolynomial.eval (trajectory (b l) 1) P,
          2 * (MvPolynomial.eval (trajectory (b l) 1) P +
            MvPolynomial.eval (trajectory (b l) 0) P -
              2 * MvPolynomial.eval (trajectory (b l) (1 / 2)) P)] := by
      ext j
      fin_cases j <;>
        simp [nativeScalarCoefficients, hl, nativeCoeff, Fin.sum_univ_three,
          Submission.Obl.k4_finite_width_output_exclusion.x,
          trajectory, Submission.Lib.K4ContactNormalization.point, div_eq_mul_inv] <;> ring
    rw [hform]
    fin_cases i
    · simpa using hy₀.trans (by linarith : H ≤ 8 * H)
    · simpa using hy₁.trans (by linarith : H ≤ 8 * H)
    · simpa using h₀.trans (by linarith : H ≤ 8 * H)
    · change |4 * MvPolynomial.eval (trajectory (b l) (1 / 2)) P -
        3 * MvPolynomial.eval (trajectory (b l) 0) P -
          MvPolynomial.eval (trajectory (b l) 1) P| ≤ 8 * H
      rw [abs_le] at h₀ hm h₁ ⊢
      constructor <;> linarith
    · change |2 * (MvPolynomial.eval (trajectory (b l) 1) P +
        MvPolynomial.eval (trajectory (b l) 0) P -
          2 * MvPolynomial.eval (trajectory (b l) (1 / 2)) P)| ≤ 8 * H
      rw [abs_le] at h₀ hm h₁ ⊢
      constructor <;> linarith
  · simp only [nativeScalarCoefficients, if_neg hl, Pi.zero_apply, abs_zero]
    positivity

end

end Submission.Obl.k4_general_parent_projected_layers
