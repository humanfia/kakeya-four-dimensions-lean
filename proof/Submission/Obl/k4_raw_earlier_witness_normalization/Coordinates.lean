import Mathlib
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.DensityTransport
import Submission.Lib.K4ChartLifting.Normalize

namespace Submission.Obl.k4_raw_earlier_witness_normalization

open MeasureTheory

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Base := EuclideanSpace ℝ (Fin 3)
abbrev Point := EuclideanSpace ℝ (Fin 4)
abbrev Incidence := (ℕ × (Fin 6 → ℝ)) × ℝ

def rawPlanar (p : Point) : Plane := WithLp.toLp 2 ![p 1, p 2]

def normalTangent (n : Plane) : Plane := WithLp.toLp 2 ![n 1, -n 0]

def baseProjection (p : Point) : Base := WithLp.toLp 2 ![p 0, p 1, p 2]

noncomputable def earlierCoordinates (t₀ q B : ℝ) (c u : Plane)
    (D : Matrix (Fin 2) (Fin 2) ℝ) (p : Point) : Point :=
  WithLp.toLp 2 ![(p 0 - t₀) / q,
    (Matrix.toEuclideanLin D⁻¹ (rawPlanar p - c - p 0 • u)) 0,
    (Matrix.toEuclideanLin D⁻¹ (rawPlanar p - c - p 0 • u)) 1, B * p 3]

theorem continuous_rawPlanar : Continuous rawPlanar := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (by intro i; fin_cases i <;> fun_prop))

theorem continuous_baseProjection : Continuous baseProjection := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (by intro i; fin_cases i <;> fun_prop))

theorem continuous_earlierCoordinates (t₀ q B : ℝ) (c u : Plane)
    (D : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (earlierCoordinates t₀ q B c u D) := by
  have ht : Continuous (fun p : Point => p 0) := PiLp.continuous_apply 2 _ 0
  have hs : Continuous (fun p : Point =>
      Matrix.toEuclideanLin D⁻¹ (rawPlanar p - c - p 0 • u)) :=
    (Matrix.toEuclideanLin D⁻¹).continuous_of_finiteDimensional.comp
      ((continuous_rawPlanar.sub continuous_const).sub (ht.smul continuous_const))
  unfold earlierCoordinates
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact (ht.sub continuous_const).div_const q
  · exact (PiLp.continuous_apply 2 _ 0).comp hs
  · exact (PiLp.continuous_apply 2 _ 1).comp hs
  · exact continuous_const.mul (PiLp.continuous_apply 2 _ 3)

open Submission.Obl.k4_dyadic_crop_affine_laws.Framework in
theorem baseProjection_earlierCoordinates (t₀ q B : ℝ) (c u : Plane)
    (D : Matrix (Fin 2) (Fin 2) ℝ) (hq : q ≠ 0) (hD : D.det ≠ 0) (p : Point) :
    baseProjection (earlierCoordinates t₀ q B c u D p) =
      (chartBaseEquiv t₀ q c u D hq hD).symm (baseProjection p) := by
  apply (chartBaseEquiv t₀ q c u D hq hD).injective
  rw [MeasurableEquiv.apply_symm_apply, chartBaseEquiv_apply]
  have ht : t₀ + q * ((p 0 - t₀) / q) = p 0 := by field_simp; ring
  have hmul := Submission.Lib.K4ChartLifting.Frame.toEuclideanLin_mul_inv_apply
    D (isUnit_iff_ne_zero.mpr hD) (rawPlanar p - c - p 0 • u)
  have h0 := congrArg (fun v : Plane => v 0) hmul
  have h1 := congrArg (fun v : Plane => v 1) hmul
  simp [Matrix.toLpLin_apply, rawPlanar] at h0 h1
  ext i
  fin_cases i <;>
    simp [baseProjection, earlierCoordinates, ht, Matrix.toLpLin_apply, rawPlanar] <;> linarith

end Submission.Obl.k4_raw_earlier_witness_normalization
