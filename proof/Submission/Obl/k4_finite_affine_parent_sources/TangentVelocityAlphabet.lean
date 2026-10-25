-- Adapted from this LOT tree, o107/x0734, Submission/Obl/k4_finite_narrowness_path_improvement/TangentVelocityAlphabet.lean; retains only the finite-alphabet estimate, with namespace/imports renamed.
import Submission.Obl.k4_finite_affine_parent_sources.FiniteVectorVelocityCodes

/-! Velocity entropy at the tangent depth unit. Constants and a subpower
velocity range are charged to that unit rather than to a fixed exponent
of the original sample scale. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- The original vector-velocity alphabet has exponent proportional to
the tangent unit. This includes the extra unused code in its cardinality. -/
theorem velocity_vector_alphabet_small_power
    {N mesh R u v : ℝ} (d : ℕ) (hN : 1 < N) (hmesh : 0 < mesh)
    (hR : 0 ≤ R) (hu : 0 < u) (hv : 0 ≤ v)
    (hRN : R ≤ N ^ u) (hresolve : N ^ (-v * u) ≤ mesh)
    (hlarge : 4 ≤ N ^ u) :
    (((Finset.Icc ⌊-R / mesh⌋ ⌊R / mesh⌋).card ^ d + 1 : ℕ) : ℝ) ≤
      N ^ (((d : ℝ) * (v + 2) + 1) * u) := by
  have hN0 : 0 < N := by linarith
  have hinv : mesh⁻¹ ≤ N ^ (v * u) := by
    apply (inv_le_iff_one_le_mul₀ hmesh).mpr
    calc
      1 = N ^ (v * u) * N ^ (-v * u) := by
        rw [← Real.rpow_add hN0]
        simp
      _ ≤ N ^ (v * u) * mesh :=
        mul_le_mul_of_nonneg_left hresolve (Real.rpow_nonneg hN0.le _)
  have hratio : R / mesh ≤ N ^ ((v + 1) * u) := by
    calc
      R / mesh = R * mesh⁻¹ := div_eq_mul_inv _ _
      _ ≤ N ^ u * N ^ (v * u) :=
        mul_le_mul hRN hinv (inv_nonneg.mpr hmesh.le) (Real.rpow_nonneg hN0.le _)
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hone : 1 ≤ N ^ ((v + 1) * u) :=
    Real.one_le_rpow hN.le (mul_nonneg (by linarith) hu.le)
  have hbins : ((Finset.Icc ⌊-R / mesh⌋ ⌊R / mesh⌋).card : ℝ) ≤
      N ^ ((v + 2) * u) := by
    calc
      _ ≤ 2 * R / mesh + 2 := velocity_bin_count hmesh hR
      _ ≤ 4 * N ^ ((v + 1) * u) := by
        rw [show 2 * R / mesh = 2 * (R / mesh) by ring]
        linarith only [hratio, hone]
      _ ≤ N ^ u * N ^ ((v + 1) * u) :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hN0.le _)
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hcount : (((Finset.Icc ⌊-R / mesh⌋ ⌊R / mesh⌋).card ^ d : ℕ) : ℝ) ≤
      N ^ ((d : ℝ) * ((v + 2) * u)) := by
    rw [Nat.cast_pow]
    calc
      _ ≤ (N ^ ((v + 2) * u)) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hbins d
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        congr 1
        ring
  have hcountOne : 1 ≤ N ^ ((d : ℝ) * ((v + 2) * u)) :=
    Real.one_le_rpow hN.le (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith) hu.le))
  rw [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ 2 * N ^ ((d : ℝ) * ((v + 2) * u)) := by linarith only [hcount, hcountOne]
    _ ≤ N ^ u * N ^ ((d : ℝ) * ((v + 2) * u)) :=
      mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ N ^ u)
        (Real.rpow_nonneg hN0.le _)
    _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring

end

end Submission.Obl.k4_finite_affine_parent_sources
