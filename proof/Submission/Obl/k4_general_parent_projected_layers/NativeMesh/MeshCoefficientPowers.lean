/- Adapted from this LOT tree o222, session x0774, commit 109e510d,
   Submission/Obl/k4_projected_parent_contact_reduction/MeshCoefficientPowers.lean.
   Existing source attributions are retained below. Accepted mesh-saturation
   results are imported from Submission.Lib.K4AffineMeshCaps.Saturation. -/
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.MeshRemez
import Submission.Obl.k4_stable_native_signal_oscillation.PowerBounds

/-! Fixed-power forms of the finite-mesh coefficient calibration. -/

namespace Submission.Obl.k4_general_parent_projected_layers.NativeMesh

open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial

theorem mesh_coefficient_power_control (D m : ℕ) :
    ∃ J n : ℕ, 4 ≤ J ∧ 1 ≤ n ∧
      ∀ K delta : ℝ, 2 ≤ K → 0 < delta → delta ≤ (K ^ J)⁻¹ →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
          (Z : Ω → Fin 3 → ℝ) (condition : Ω → Prop),
          (∀ q : Fin 3 → ℤ,
            μ {p | baseMesh delta (Z p) = q ∧ condition p} ≤
              ENNReal.ofReal (K * delta ^ 3)) →
          ∀ S : Set (Fin 3 → ℝ),
            S ⊆ Icc (fun _ => (1 : ℝ) / 8) (fun _ => (1 : ℝ) / 4) →
            ENNReal.ofReal ((K ^ m)⁻¹) ≤ μ {p | Z p ∈ S ∧ condition p} →
            ∀ E : ℝ, 0 ≤ E →
              ∀ P : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ D →
                (∀ z ∈ S, |eval z P| ≤ E) → ∀ e, |P.coeff e| ≤ K ^ n * E := by
  obtain ⟨A, L, hA, hL, hcalib⟩ := finite_mesh_polynomial_remez D
  let B : ℝ := (32 * ((D : ℝ) + 1)) ^ (3 * D)
  let p : ℕ := (m + 1) * (3 * D)
  obtain ⟨n, hn, hcoef⟩ :=
    Submission.Obl.k4_stable_native_signal_oscillation.exists_nat_power_bound (2 * A * B) p
  obtain ⟨j, hj, hmesh⟩ :=
    Submission.Obl.k4_stable_native_signal_oscillation.exists_nat_power_bound (2 * A * L * B) p
  let J := max 4 j
  refine ⟨J, n, le_max_left _ _, hn, ?_⟩
  intro K delta hK hd hdJ Ω inst μ Z condition hcap S hS hmass E hE P hP hbound e
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have h16 : (16 : ℝ) ≤ K ^ J := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ K ^ 4 := pow_le_pow_left₀ (by norm_num) hK 4
      _ ≤ K ^ J := pow_le_pow_right₀ hK1 (le_max_left _ _)
  have hd16 : delta ≤ 1 / 16 := hdJ.trans (by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 16) h16)
  let eta : ℝ := (K ^ (m + 1))⁻¹
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : eta ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hK1)
  have hmass' : ENNReal.ofReal (K * eta) ≤ μ {w | Z w ∈ S ∧ condition w} := by
    have heq : K * eta = (K ^ m)⁻¹ := by
      dsimp [eta]
      rw [pow_succ]
      field_simp
    simpa only [heq] using hmass
  have hR : (32 * ((D : ℝ) + 1) / eta) ^ (3 * D) = B * K ^ p := by
    dsimp [eta, B, p]
    rw [div_inv_eq_mul, mul_pow, ← pow_mul]
  have hmesh' : 2 * A * L * B * K ^ p ≤ K ^ J := by
    have h := hmesh K hK
    rw [Real.rpow_natCast] at h
    exact h.trans (pow_le_pow_right₀ hK1 (le_max_right _ _))
  have hprod : K ^ J * delta ≤ 1 := by
    rw [mul_comm (K ^ J) delta]
    apply (le_div_iff₀ (pow_pos hK0 J)).mp
    simpa only [one_div] using hdJ
  have hsmall : A * L * (32 * ((D : ℝ) + 1) / eta) ^ (3 * D) * delta ≤ 1 / 2 := by
    rw [hR]
    have h := (mul_le_mul_of_nonneg_right hmesh' hd.le).trans hprod
    nlinarith
  have h := hcalib Ω μ Z condition delta K eta E hd hd16 hK0 heta heta1 hE hsmall
    S hS hcap hmass' P hP hbound e
  rw [hR] at h
  have hcoef' := hcoef K hK
  rw [Real.rpow_natCast] at hcoef'
  calc
    |P.coeff e| ≤ 2 * A * (B * K ^ p) * E := h
    _ = (2 * A * B * K ^ p) * E := by ring
    _ ≤ K ^ n * E := mul_le_mul_of_nonneg_right hcoef' hE

end Submission.Obl.k4_general_parent_projected_layers.NativeMesh
