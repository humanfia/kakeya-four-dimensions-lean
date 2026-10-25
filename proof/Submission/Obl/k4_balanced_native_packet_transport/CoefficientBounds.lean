import Submission.Obl.k4_balanced_native_packet_transport.NativeCoordinates
import Submission.Obl.k4_scalar_normalized_exact_refinement.Coordinates

namespace Submission.Obl.k4_balanced_native_packet_transport

open Set
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

/-- The regularity bound follows from whole-block physical fits by the
accepted interpolation estimate; clipping gives zero outside the assignment. -/
theorem nativeCoeff_bound_of_full_block
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q offset : ℝ) (v : Fin 3 → ℝ) (A : Set Traj)
    {H : ℝ} (hH : 0 ≤ H)
    (hy : ∀ l ∈ A, ∀ τ ∈ Icc (0 : ℝ) 1,
      |offset + ∑ i : Fin 3, v i * x l (t₀ + q * τ) i.castSucc| ≤ H)
    (hx : ∀ l ∈ A, ∀ τ ∈ Icc (0 : ℝ) 1,
      |MvPolynomial.eval (x l (t₀ + q * τ)) P| ≤ H) :
    ∀ l i, |nativeCoeff P t₀ q offset v A l i| ≤ 8 * H := by
  classical
  intro l i
  by_cases hl : l ∈ A
  · apply Submission.Obl.k4_scalar_normalized_exact_refinement.coefficients_bound_of_trajectories
      (0, nativeCoeff P t₀ q offset v A l) hH
    · intro τ hτ
      change |scalarY (nativeCoeff P t₀ q offset v A l) τ| ≤ H
      rw [nativeCoeff_scalarY P t₀ q offset v hl]
      exact hy l hl τ hτ
    · intro τ hτ
      change |scalarX (nativeCoeff P t₀ q offset v A l) τ| ≤ H
      rw [nativeCoeff_scalarX P hP t₀ q offset v hl]
      exact hx l hl τ hτ
  · simp only [nativeCoeff, if_neg hl, Pi.zero_apply, abs_zero]
    positivity

/-- A centered initial value and the old physical tangent slope bound the
whole unsheared scalar tangent on the new unit block. -/
theorem native_retime_tangent_bound
    (P : MvPolynomial (Fin 4) ℝ) (t₀ q offset center : ℝ) (hq : 0 < q)
    (v : Fin 3 → ℝ) {A C : Set Traj} (hAC : A ⊆ C)
    {K H : ℝ} (hK : 0 ≤ K) {l : Traj} (hl : l ∈ A)
    (hslope : |nativeCoeff P 0 1 offset v C l 1| ≤ K)
    (hcenter : |scalarY (nativeCoeff P 0 1 offset v C l) t₀ - center| ≤ q * H)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    |scalarY (nativeCoeff P t₀ q ((offset - center) / q)
      (fun i => v i / q) A l) τ| ≤ H + K := by
  let old := nativeCoeff P 0 1 offset v C l
  let new := nativeCoeff P t₀ q ((offset - center) / q) (fun i => v i / q) A l
  have hvalue : scalarY old (t₀ + q * τ) = center + q * scalarY new τ :=
    nativeCoeff_retime_tangent P t₀ q offset center hq.ne' v hAC hl τ
  have heq : scalarY old (t₀ + q * τ) - center =
      (scalarY old t₀ - center) + q * τ * old 1 := by unfold scalarY; ring
  have hterm : |q * τ * old 1| ≤ q * K := by
    rw [abs_mul, abs_mul, abs_of_pos hq, abs_of_nonneg hτ.1]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hq.le
    calc
      τ * |old 1| ≤ 1 * K := mul_le_mul hτ.2 hslope (abs_nonneg _) (by norm_num)
      _ = K := one_mul _
  have hbound : q * |scalarY new τ| ≤ q * (H + K) := by
    calc
      q * |scalarY new τ| = |q * scalarY new τ| := by rw [abs_mul, abs_of_pos hq]
      _ = |scalarY old (t₀ + q * τ) - center| := by rw [hvalue]; congr 1; ring
      _ = |(scalarY old t₀ - center) + q * τ * old 1| := by rw [heq]
      _ ≤ |scalarY old t₀ - center| + |q * τ * old 1| := abs_add_le _ _
      _ ≤ q * H + q * K := add_le_add hcenter hterm
      _ = q * (H + K) := by ring
  change |scalarY new τ| ≤ H + K
  by_contra hn
  have hpos : 0 < q * (|scalarY new τ| - (H + K)) :=
    mul_pos hq (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith


end
end Submission.Obl.k4_balanced_native_packet_transport
