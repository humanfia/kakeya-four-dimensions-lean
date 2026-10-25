/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ParentMeshPowers.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentScalePowers
import Submission.Obl.k4_critical_affine_derivative_preparation.CriticalScales
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Fixed mesh exponents work uniformly on a compact positive depth interval. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Filter

theorem mesh_le_inverse_filling_power {N H D M : ℝ} {J : ℕ}
    (hN : 1 ≤ N) (hH : 0 < H) (hbound : H ≤ N ^ D) (hM : D * J ≤ M) :
    N ^ (-M) ≤ (H ^ J)⁻¹ := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : H ^ J ≤ N ^ (D * J) := by
    rw [Real.rpow_mul_natCast hNpos.le]
    exact pow_le_pow_left₀ hH.le hbound J
  calc
    _ ≤ N ^ (-(D * J)) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = (N ^ (D * J))⁻¹ := Real.rpow_neg hNpos.le _
    _ ≤ _ := inv_anti₀ (pow_pos hH _) hpow

theorem physical_mesh_over_packet {N qg E r M : ℝ} (hN : 1 ≤ N)
    (hqg : N ^ (-E) ≤ qg) (hr : M + E ≤ r) :
    N ^ (-r) / qg ≤ N ^ (-M) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hqg0 : 0 < N ^ (-E) := Real.rpow_pos_of_pos hNpos _
  calc
    _ ≤ N ^ (-r) / N ^ (-E) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hNpos.le _) hqg0 hqg
    _ = N ^ (-r - -E) := (Real.rpow_sub hNpos _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

theorem native_oscillation_mesh_bound {N H K D A E M B chi qg : ℝ} {C : ℕ}
    (hN : 1 ≤ N) (hH : 0 ≤ H) (hK : 0 ≤ K) (hHbound : H ≤ N ^ D)
    (hKbound : K ≤ N ^ A) (hconstant : 48 ≤ N ^ A)
    (hchi : chi ≤ N ^ (-M)) (hqg : N ^ (-E) ≤ qg)
    (hM : D * C + 3 * A + E + B ≤ M) :
    H ^ C * (24 * K ^ 2 * (N ^ (-M) + chi) / qg) ≤ N ^ (-B) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hqg0 : 0 < qg := (Real.rpow_pos_of_pos hNpos _).trans_le hqg
  have hnum : 24 * K ^ 2 * (N ^ (-M) + chi) ≤ 48 * K ^ 2 * N ^ (-M) := by
    nlinarith only [mul_nonneg (by positivity : 0 ≤ 24 * K ^ 2) (sub_nonneg.mpr hchi)]
  have hnum' : 48 * K ^ 2 * N ^ (-M) ≤ N ^ A * (N ^ A) ^ 2 * N ^ (-M) := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNpos.le _)
    exact mul_le_mul hconstant (pow_le_pow_left₀ hK hKbound 2) (sq_nonneg _) (by positivity)
  have hpower : H ^ C ≤ (N ^ D) ^ C := pow_le_pow_left₀ hH hHbound C
  calc
    _ ≤ H ^ C * ((N ^ A * (N ^ A) ^ 2 * N ^ (-M)) / qg) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hnum.trans hnum') hqg0.le)
        (pow_nonneg hH _)
    _ ≤ (N ^ D) ^ C * ((N ^ A * (N ^ A) ^ 2 * N ^ (-M)) / N ^ (-E)) :=
      mul_le_mul hpower
        (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hNpos _) hqg)
        (by positivity) (by positivity)
    _ = N ^ (D * C + 3 * A - M + E) := by
      rw [← Real.rpow_mul_natCast hNpos.le D C, ← Real.rpow_mul_natCast hNpos.le A 2,
        ← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_sub hNpos,
        ← Real.rpow_add hNpos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

theorem PreparedModel.eventually_q_narrow_lower {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (B : ℝ)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, ∀ R s : ℝ, a.AtlasAt p R k s → s ≤ B →
      p.N k ^ (-(p.kappa + p.ell) * B - eps) ≤ a.q k s * PreparedModel.narrow p k s := by
  filter_upwards [hp.2.2.1.2 eps heps] with k hk
  intro R s hatlas hs
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hN1 : 1 ≤ p.N k := by linarith [hp.1 k]
  have hK : 0 < p.K k := lt_of_lt_of_le zero_lt_one (hp.2.2.1.1 k)
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have htime := (Submission.Obl.k4_critical_affine_derivative_preparation.time_length_comparison
    hN hK hatlas.1 hatlas.2.1).2
  have htime' : p.N k ^ (-p.kappa * s) ≤ p.K k * a.q k s := by
    simpa only [PreparedModel.q, zpow_neg, zpow_natCast] using htime
  have hraw : p.N k ^ (-(p.kappa + p.ell) * s) ≤
      p.K k * (a.q k s * PreparedModel.narrow p k s) := by
    have h := mul_le_mul_of_nonneg_right htime'
      (Real.rpow_nonneg hN.le (-p.ell * s))
    convert h using 1
    · rw [← Real.rpow_add hN]
      congr 1
      ring
    · unfold PreparedModel.narrow
      ring
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hN eps)).mp
  calc
    _ = p.N k ^ (-(p.kappa + p.ell) * B) := by
      rw [← Real.rpow_add hN]
      congr 1
      ring
    _ ≤ p.N k ^ (-(p.kappa + p.ell) * s) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
    _ ≤ p.K k * (a.q k s * PreparedModel.narrow p k s) := hraw
    _ ≤ _ := mul_le_mul_of_nonneg_right hk (by unfold PreparedModel.q PreparedModel.narrow; positivity)

end Submission.Obl.k4_general_parent_projected_layers
