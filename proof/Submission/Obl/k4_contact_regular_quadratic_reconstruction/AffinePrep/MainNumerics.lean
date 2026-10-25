import Mathlib

/-!
# Numerical conditions of the second affine preparation

Pure real inequalities used to discharge the numerical hypotheses of
`affine_candidate_at` at late samples. All subpower factors are collected in an envelope
`E = K * N ^ εc`.
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

noncomputable section

/-- The unit-box size of a centered label. -/
theorem unitBox_le {K J E : ℝ} (hK : 1 ≤ K) (hE : K ≤ E) (hJ : J ≤ 2 * E) (hJ0 : 0 ≤ J) :
    2 * K + 2 * K ^ 2 + 2 * J * K + J ≤ 10 * E ^ 2 := by
  have hE1 : 1 ≤ E := hK.trans hE
  nlinarith [mul_le_mul hJ hE (by linarith) (by linarith)]

/-- The rate identity behind the cancellation of the fine-width density. -/
theorem rpow_mass_identity {N d s v η : ℝ} (hN : 0 < N) :
    N ^ (-d * v - η) * (N ^ (-s)) ^ d = N ^ (-η) * (N ^ (-s - v)) ^ d := by
  rw [← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le, ← Real.rpow_add hN, ← Real.rpow_add hN]
  congr 1
  ring

/-- The volume condition of the filled set. -/
theorem nvol_of {N K q g H Bz hm c d Λ η τ mE : ℝ} (hN : 0 < N) (hK : 1 ≤ K) (hq : 0 < q)
    (hg : 0 < g) (hqg : q ≤ K * g) (hH : 1 ≤ H) (hBz : 0 < Bz) (hhm : 0 < hm) (hc : 0 < c)
    (hΛ : Λ = N ^ τ) (hmE : mE = N ^ (-η) * c ^ d * q ^ 3 * g / K)
    (hbig : 497664 * K ^ 3 * (1 + 4 * H ^ 2) * (6 * K + 5) * Bz ^ 2 * N ^ η ≤ N ^ τ) :
    Λ⁻¹ ≤ mE / 36 * hm ^ 3 /
      (8 * (1 + 4 * H ^ 2) * (27 * (6 * K + 5) * K * ((8 * Bz) ^ 2 * q ^ 4) * (hm ^ 3 * c ^ d))) := by
  have hcd : 0 < c ^ d := Real.rpow_pos_of_pos hc d
  have hNη : 0 < N ^ η := Real.rpow_pos_of_pos hN η
  have hK0 : 0 < K := by linarith
  set D := 8 * (1 + 4 * H ^ 2) * (27 * (6 * K + 5) * K * ((8 * Bz) ^ 2 * q ^ 4) *
      (hm ^ 3 * c ^ d)) with hDdef
  have hD : 0 < D := by rw [hDdef]; positivity
  set P := 497664 * K ^ 3 * (1 + 4 * H ^ 2) * (6 * K + 5) * Bz ^ 2 * N ^ η with hPdef
  have hP : 0 < P := by rw [hPdef]; positivity
  rw [hΛ, hmE, le_div_iff₀ hD, Real.rpow_neg hN.le]
  have hinv : (N ^ τ)⁻¹ ≤ P⁻¹ := inv_anti₀ hP hbig
  calc (N ^ τ)⁻¹ * D ≤ P⁻¹ * D := mul_le_mul_of_nonneg_right hinv hD.le
    _ = q ^ 3 * q * hm ^ 3 * c ^ d / (36 * K ^ 2 * N ^ η) := by
        rw [hPdef, hDdef]; field_simp; ring
    _ ≤ q ^ 3 * (K * g) * hm ^ 3 * c ^ d / (36 * K ^ 2 * N ^ η) := by gcongr
    _ = (N ^ η)⁻¹ * c ^ d * q ^ 3 * g / K / 36 * hm ^ 3 := by field_simp

/-- The velocity-separation condition of the light-cell deletion. -/
theorem nvel_of {N K q g H Bz hm c d rv S η mE : ℝ} (hN : 0 < N) (hK : 1 ≤ K) (hq : 0 < q)
    (hg : 0 < g) (hqg : q ≤ K * g) (hH : 1 ≤ H) (hBz : 0 < Bz) (hhm : 0 < hm) (hc : 0 < c)
    (hrv : 0 < rv) (hmE : mE = N ^ (-η) * c ^ d * q ^ 3 * g / K)
    (hbig : 15925248 * (1 + 4 * H ^ 2) * (6 * K + 5) * K ^ 4 * Bz ^ 2 * rv ^ S * N ^ η < 1) :
    2 * (2 * (8 * (1 + 4 * H ^ 2) * (27 * (6 * K + 5) * K * ((8 * Bz) ^ 2 * q ^ 4) *
      (hm ^ 3 * c ^ d)) * (K * rv ^ S))) < mE * hm ^ 3 / (18 * 16) := by
  have hcd : 0 < c ^ d := Real.rpow_pos_of_pos hc d
  have hNη : 0 < N ^ η := Real.rpow_pos_of_pos hN η
  have hrS : 0 < rv ^ S := Real.rpow_pos_of_pos hrv S
  have hK0 : 0 < K := by linarith
  set P := 15925248 * (1 + 4 * H ^ 2) * (6 * K + 5) * K ^ 4 * Bz ^ 2 * rv ^ S * N ^ η with hPdef
  have hP : 0 < P := by rw [hPdef]; positivity
  set Q := c ^ d * q ^ 3 * hm ^ 3 * g / (288 * K * N ^ η) with hQdef
  have hQ : 0 < Q := by rw [hQdef]; positivity
  rw [hmE, Real.rpow_neg hN.le]
  calc 2 * (2 * (8 * (1 + 4 * H ^ 2) * (27 * (6 * K + 5) * K * ((8 * Bz) ^ 2 * q ^ 4) *
        (hm ^ 3 * c ^ d)) * (K * rv ^ S)))
      = P * (c ^ d * q ^ 3 * hm ^ 3 * q / (288 * K ^ 2 * N ^ η)) := by
        rw [hPdef]; field_simp; ring
    _ ≤ P * (c ^ d * q ^ 3 * hm ^ 3 * (K * g) / (288 * K ^ 2 * N ^ η)) := by gcongr
    _ = P * Q := by rw [hQdef]; field_simp
    _ < 1 * Q := mul_lt_mul_of_pos_right hbig hQ
    _ = (N ^ η)⁻¹ * c ^ d * q ^ 3 * g / K * hm ^ 3 / (18 * 16) := by
        rw [hQdef]; field_simp; ring

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
