-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepBase.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/PrepBase.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepTransport
import Submission.Obl.k4_multilinear_kakeya.Plane

/-!
# Base coordinates as a function of the observation

The frame base point of an incidence depends only on its observed spacetime point
`(obs p).1 = (t, y₁, y₂)`, through the affine map `movingBasePoint`, whose preimages have
volume `(a³ |det Q| / q) · vol` (`q = 2^T`, `a = 100 κ`).

`movingBasePoint` and `volume_movingBasePoint_preimage` are adapted from session x0383's
`BaseJacobian.lean` (o114 repository, branch x0383, after commit 7470a6e; its matrix and
shear calculation follows accepted o148 `BaseVolume`, and the measurable-set kernel is
accepted `k4_multilinear_kakeya.matrix_preimage_volume`), renamed into this namespace.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open MeasureTheory Set
open scoped ENNReal

/-- Physical spacetime to the centered normalized moving-frame base (x0383). -/
noncomputable def movingBasePoint (q j a : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(q * z 0 - j - 1/2) / a,
    (Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - (z 0) • u)) 0 / a,
    (Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - (z 0) • u)) 1 / a]

/-- The inverse Jacobian is independent of the center, velocity and block label (x0383). -/
theorem volume_movingBasePoint_preimage {q a : ℝ} (hq : 0 < q) (ha : 0 < a)
    (j : ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : Q.det ≠ 0) {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : MeasurableSet U) :
    volume (movingBasePoint q j a c u Q ⁻¹' U) =
      ENNReal.ofReal (a^3 * |Q.det| / q) * volume U := by
  let qu := Matrix.toEuclideanLin Q⁻¹ u
  let qc := Matrix.toEuclideanLin Q⁻¹ c
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    !![q, 0, 0; -qu 0, Q⁻¹ 0 0, Q⁻¹ 0 1; -qu 1, Q⁻¹ 1 0, Q⁻¹ 1 1]
  let A : Matrix (Fin 3) (Fin 3) ℝ := a⁻¹ • M
  let b : Fin 3 → ℝ := ![(-j - 1/2)/a, -qc 0/a, -qc 1/a]
  have hdetM : M.det = q * Q.det⁻¹ := by
    calc
      M.det = q * (Q⁻¹).det := by
        rw [Matrix.det_fin_two]
        norm_num [M, Matrix.det_fin_three, Matrix.vecHead, Matrix.vecTail, Function.comp_def]
        ring
      _ = _ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hdet : A.det = a⁻¹^3 * (q * Q.det⁻¹) := by
    rw [show A = a⁻¹ • M from rfl, Matrix.det_smul, Fintype.card_fin, hdetM]
  have hdetA : A.det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ha.ne'))
      (mul_ne_zero hq.ne' (inv_ne_zero hQ))
  have hinv : A.det⁻¹ = a^3 * Q.det / q := by
    rw [hdet]
    field_simp
  have hpoint (z : EuclideanSpace ℝ (Fin 3)) :
      movingBasePoint q j a c u Q z = WithLp.toLp 2 (A.mulVec (WithLp.ofLp z) + b) := by
    ext i
    fin_cases i <;>
      simp [movingBasePoint, A, M, b, qu, qc, Matrix.toEuclideanLin,
        Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        Matrix.vecHead, Matrix.vecTail, Function.comp_def, div_eq_mul_inv] <;> ring
  let V : Set (Fin 3 → ℝ) := (fun v => WithLp.toLp 2 (v + b)) ⁻¹' U
  have hV : MeasurableSet V := hU.preimage (by fun_prop)
  have hvolV : volume V = volume U := by
    change volume ((fun v : Fin 3 → ℝ => v + b) ⁻¹' (WithLp.toLp 2 ⁻¹' U)) = volume U
    rw [measure_preimage_add_right]
    exact (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage hU.nullMeasurableSet
  have hset : movingBasePoint q j a c u Q ⁻¹' U =
      (fun z : EuclideanSpace ℝ (Fin 3) => A.mulVec (WithLp.ofLp z)) ⁻¹' V := by
    ext z
    simp only [mem_preimage, V, hpoint]
  rw [hset, Submission.Obl.k4_multilinear_kakeya.matrix_preimage_volume A hdetA hV,
    hvolV, hinv, abs_div, abs_mul, abs_pow, abs_of_pos ha, abs_of_pos hq]

theorem continuous_movingBasePoint (q j a : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (movingBasePoint q j a c u Q) := by
  unfold movingBasePoint
  fun_prop

theorem measurable_movingBasePoint (q j a : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Measurable (movingBasePoint q j a c u Q) :=
  (continuous_movingBasePoint q j a c u Q).measurable

/-- The frame base point is the moving base point of the observed spacetime point. -/
theorem base_eq_movingBasePoint (T : ℕ) (j κ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B δ : ℝ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    base T j κ c u Q p.1 p.2 =
      movingBasePoint ((2 : ℝ) ^ T) j (100 * κ) c u Q (obs B δ p).1 := by
  have hy : WithLp.toLp 2 ![(obs B δ p).1 1, (obs B δ p).1 2] = y p.1 p.2 := by
    ext i
    fin_cases i <;> simp [obs, y]
  have h0 : (obs B δ p).1 0 = p.2 := by simp [obs]
  unfold movingBasePoint base
  rw [hy, h0]

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
