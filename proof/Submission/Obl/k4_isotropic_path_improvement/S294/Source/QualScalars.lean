-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.QualScalars, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.QualificationClock

/-!
# The qualification display scalars (session x1082)

The last scalar seam of `Source.samplePost_of_rootPackage` and of x1096's root preparation input:
from the native constants (`H`, degree `M`, child clock ratio `lam`, `N^(ch ε_an)`) and the residual
error budget, choose the grid mesh `θ/(8(M+1))`, the integer coefficient bound, the error `θ` and
the duration `lam N^(-ch ε_an)`, and check every inequality both consumers ask for.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- **The qualification display scalars.** -/
theorem qualification_display_scalars {H lam N ch aE θ K e η : ℝ} {M : ℕ}
    (hH : 1 ≤ H) (hlam : 0 < lam) (hN : 0 < N) (hθ : 0 < θ)
    (hres : e + (1 + 2 * H) * (η + lam ^ ((M : ℝ) + 1 / 8)) ≤ θ / 2)
    (hK1 : Parent.QualificationClock.coefficientCost M *
      (3 * H + (1 + 2 * H) * N ^ (ch * aE) + 3 * (θ / (8 * ((M : ℝ) + 1)))) ≤ K)
    (hK2 : N ^ (ch * aE) ≤ K) :
    let qmesh := θ / (8 * ((M : ℝ) + 1))
    let qbound : ℤ := ⌈(3 * H + (1 + 2 * H) * N ^ (ch * aE)) / qmesh⌉ + 2
    0 < qmesh ∧ 0 ≤ qbound ∧
      3 * H + (1 + 2 * H) * N ^ (ch * aE) ≤ qmesh * ((qbound : ℝ) - 1) ∧
      e + (1 + 2 * H) * (η + lam ^ ((M : ℝ) + 1 / 8)) + ((M : ℝ) + 1) * qmesh ≤ θ ∧
      Parent.QualificationClock.coefficientCost M * (qmesh * (qbound : ℝ)) ≤ K ∧
      1 / K ≤ (lam * N ^ (-(ch * aE))) / lam := by
  intro qmesh qbound
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hqmesh : 0 < qmesh := by positivity
  have hNpow : 0 < N ^ (ch * aE) := Real.rpow_pos_of_pos hN _
  set X := 3 * H + (1 + 2 * H) * N ^ (ch * aE) with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ (1 + 2 * H) * N ^ (ch * aE) := mul_nonneg (by linarith) hNpow.le
    linarith
  have hceil0 : (0 : ℤ) ≤ ⌈X / qmesh⌉ := Int.ceil_nonneg (div_nonneg hX0 hqmesh.le)
  have hle : X / qmesh ≤ (⌈X / qmesh⌉ : ℝ) := Int.le_ceil _
  have hlt : (⌈X / qmesh⌉ : ℝ) < X / qmesh + 1 := Int.ceil_lt_add_one _
  have hqb : (qbound : ℝ) = (⌈X / qmesh⌉ : ℝ) + 2 := by
    simp only [qbound]; push_cast; ring
  have hKpos : 0 < K := lt_of_lt_of_le hNpow hK2
  have hqb0 : (0 : ℤ) ≤ ⌈X / qmesh⌉ + 2 := by omega
  refine ⟨hqmesh, hqb0, ?_, ?_, ?_, ?_⟩
  · rw [hqb]
    have h1 : X = qmesh * (X / qmesh) := by field_simp
    calc X = qmesh * (X / qmesh) := h1
      _ ≤ qmesh * ((⌈X / qmesh⌉ : ℝ) + 2 - 1) := by
          apply mul_le_mul_of_nonneg_left _ hqmesh.le
          linarith
  · have h8 : ((M : ℝ) + 1) * qmesh = θ / 8 := by
      simp only [qmesh]; field_simp
    rw [h8]
    linarith
  · have hbound : qmesh * (qbound : ℝ) ≤ X + 3 * qmesh := by
      rw [hqb]
      have h1 : qmesh * (X / qmesh) = X := by field_simp
      nlinarith
    have hcost : 0 ≤ Parent.QualificationClock.coefficientCost M :=
      (Parent.QualificationClock.coefficientCost_pos M).le
    exact (mul_le_mul_of_nonneg_left hbound hcost).trans hK1
  · rw [mul_div_cancel_left₀ _ hlam.ne', Real.rpow_neg hN.le, one_div]
    exact inv_anti₀ hNpow hK2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
