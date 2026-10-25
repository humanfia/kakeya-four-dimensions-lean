-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClippedCarrier.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClippedCarrier.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0708 commit 170d089, ClippedCarrier.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CarrierMap

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (boxAxis boxAxis_norm inner_boxAxis unit_pos_smul)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit norm_smul_unit)

/-- Clipping the normal scale at the old transverse width gives both a
uniform inverse bound and a small change in the old long directions. -/
theorem clipped_carrier_linear_data {a ρ c A B C : ℝ}
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c)
    (hac : a ≤ ρ*c) (hA : 0 < A)
    (z z' : V) (e g : V ≃ₗᵢ[ℝ] V) (L : V ≃ₗ[ℝ] V)
    (hsub : P a (ρ*c) c z e ⊆ P A B C z' g)
    (hcoord : ∀ v i, L v i =
      (![ρ/(4*min A (ρ*c)),(4*c)⁻¹,(4*c)⁻¹] : Fin 3 → ℝ) i * g v i) :
    (∀ v, ‖L.symm v‖ ≤ (4*c)*‖v‖) ∧
    a*‖L (boxAxis e 0)‖ ≤ ρ ∧ (ρ*c)*‖L (boxAxis e 1)‖ ≤ ρ ∧
    ‖L (boxAxis e 2)‖ ≤ c⁻¹ ∧ ‖unit (L (boxAxis e 2))-g (boxAxis e 2)‖ ≤ 2*ρ := by
  refine ⟨carrier_linear_inverse (lt_min hA (mul_pos hρ hc)) hc
    (min_le_right _ _) g L hcoord, ?_⟩
  by_cases hAc : A ≤ ρ*c
  · have hcoord' : ∀ v i, L v i =
        (![ρ/(4*A),(4*c)⁻¹,(4*c)⁻¹] : Fin 3 → ℝ) i * g v i := by
      simpa only [min_eq_left hAc] using hcoord
    obtain ⟨h0, h1, h2⟩ := carrier_grain_linear_bounds ha hρ hc hac hA le_rfl hρ1
      z z' e g L hsub hcoord'
    refine ⟨h0, h1, h2, carrier_unit_direction_error hA hc hAc g L hcoord'
      (boxAxis_norm e 2) ?_⟩
    simpa only [inner_boxAxis] using
      contained_prism_normal_bound ha (mul_pos hρ hc).le hc z z' e g hsub
  · have hAc' : ρ*c ≤ A := le_of_not_ge hAc
    have he (v : V) : L v = (4*c)⁻¹ • g v := by
      ext i
      rw [PiLp.smul_apply, hcoord, min_eq_right hAc']
      have hscale : ρ/(4*(ρ*c)) = (4*c)⁻¹ := by field_simp
      fin_cases i <;> simp [hscale]
    have hn (j : Fin 3) : ‖L (boxAxis e j)‖ = (4*c)⁻¹ := by
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (4*c)⁻¹),
        g.norm_map, boxAxis_norm, mul_one]
    have hmiddle : (ρ*c)*(4*c)⁻¹ ≤ ρ := by
      have heq : (ρ*c)*(4*c)⁻¹ = ρ/4 := by field_simp
      rw [heq]
      linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hn]
      exact (mul_le_mul_of_nonneg_right hac (by positivity)).trans hmiddle
    · rwa [hn]
    · rw [hn]
      exact inv_anti₀ hc (by linarith : c ≤ 4*c)
    · rw [he, unit_pos_smul (by positivity : 0 < (4*c)⁻¹)]
      simp only [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit,
        g.norm_map, boxAxis_norm, inv_one, one_smul, sub_self, norm_zero]
      positivity

/-- The clipped carrier normalization produces round short tubes, whose
unit extensions have the same controlled normalized directions. -/
theorem clipped_carrier_grain_tube {a ρ c A B C : ℝ}
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c)
    (hac : a ≤ ρ*c) (hA : 0 < A)
    (z z₀ z' : V) (e g : V ≃ₗᵢ[ℝ] V)
    (hsub : P a (ρ*c) c z e ⊆ P A B C z' g) :
    let f := carrierAffine (lt_min hA (mul_pos hρ hc)) hc hρ z₀ z' g
    let ν := unit (f.linear (boxAxis e 2))
    ‖ν‖ = 1 ∧ ‖ν-g (boxAxis e 2)‖ ≤ 2*ρ ∧
      (1/4 : ℝ) ≤ ‖c • f.linear (boxAxis e 2)‖ ∧
      ‖c • f.linear (boxAxis e 2)‖ ≤ 1 ∧
      f '' P a (ρ*c) c z e ⊆ T (2*ρ) (f z-(1/2 : ℝ) • ν) ν := by
  dsimp only
  let f := carrierAffine (lt_min hA (mul_pos hρ hc)) hc hρ z₀ z' g
  obtain ⟨hInv, h0, h1, h2, herror⟩ := clipped_carrier_linear_data ha hρ hρ1 hc hac hA
    z z' e g f.linear hsub (carrierAffine_linear _ _ _ _ _ _)
  have hLv : f.linear (boxAxis e 2) ≠ 0 := by
    intro hh
    have hz : boxAxis e 2 = 0 := f.linear.injective (hh.trans (map_zero _).symm)
    have hn := boxAxis_norm e 2
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hnorm : ‖c • f.linear (boxAxis e 2)‖ = c*‖f.linear (boxAxis e 2)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hlo : (1/4 : ℝ) ≤ ‖c • f.linear (boxAxis e 2)‖ := by
    have hh := hInv (f.linear (boxAxis e 2))
    rw [LinearEquiv.symm_apply_apply, boxAxis_norm] at hh
    rw [hnorm]
    linarith
  have hhi : ‖c • f.linear (boxAxis e 2)‖ ≤ 1 := by
    rw [hnorm]
    have hh := mul_le_mul_of_nonneg_left h2 hc.le
    simpa only [mul_inv_cancel₀ hc.ne'] using hh
  refine ⟨norm_unit hLv, herror, hlo, hhi, ?_⟩
  have htube := affine_prism_tube ha (mul_pos hρ hc).le hc hρ z e f h0 h1
  let ν := unit (f.linear (boxAxis e 2))
  have hvec : c • f.linear (boxAxis e 2) = ‖c • f.linear (boxAxis e 2)‖ • ν := by
    have hh := norm_smul_unit (smul_ne_zero hc.ne' hLv)
    rw [unit_pos_smul hc] at hh
    exact hh.symm
  have hmid : f z-(c/2) • f.linear (boxAxis e 2) +
      (1/2 : ℝ) • (c • f.linear (boxAxis e 2)) = f z := by module
  have hh := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.image_tube_extend
    (AffineEquiv.refl ℝ V).toContinuousAffineEquiv (f z-(c/2) • f.linear (boxAxis e 2))
    (c • f.linear (boxAxis e 2)) ν (δ := 2*ρ) (A := 1)
    (by norm_num) (norm_nonneg _) hhi (by simpa using hvec) (by intro p q; simp)
  have hcar : T (2*ρ) (f z-(c/2) • f.linear (boxAxis e 2)) (c • f.linear (boxAxis e 2)) ⊆
      T (2*ρ) (f z-(1/2 : ℝ) • ν) ν := by
    simpa only [AffineEquiv.coe_toContinuousAffineEquiv, AffineEquiv.coe_refl,
      Set.image_id, id_eq, one_mul, hmid, T,
      WangZahlLot.Obl.wz_affine_robust_cluster_estimate.tube] using hh
  exact htube.trans hcar

/-- The normalized unit long axes obey the slab normal estimate needed
for packet enclosures. -/
theorem clipped_carrier_normal_bound {a ρ c A B C : ℝ}
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hc : 0 < c) (hA : 0 < A)
    (z z₀ z' : V) (e g : V ≃ₗᵢ[ℝ] V)
    (hsub : P a (ρ*c) c z e ⊆ P A B C z' g) :
    let f := carrierAffine (lt_min hA (mul_pos hρ hc)) hc hρ z₀ z' g
    |unit (f.linear (boxAxis e 2)) 0| ≤ 4*(ρ*A/(4*min A (ρ*c))) := by
  dsimp only
  let S := min A (ρ*c)
  have hS : 0 < S := lt_min hA (mul_pos hρ hc)
  let f := carrierAffine hS hc hρ z₀ z' g
  have hInv := carrier_linear_inverse hS hc (min_le_right _ _) g f.linear
    (carrierAffine_linear _ _ _ _ _ _)
  have hnorm : 1/(4*c) ≤ ‖f.linear (boxAxis e 2)‖ := by
    have hh := hInv (f.linear (boxAxis e 2))
    rw [LinearEquiv.symm_apply_apply, boxAxis_norm] at hh
    exact (div_le_iff₀ (by positivity : 0 < 4*c)).mpr (by nlinarith only [hh])
  have hnormpos : 0 < ‖f.linear (boxAxis e 2)‖ := (by positivity : 0 < 1/(4*c)).trans_le hnorm
  have hnormal : |g (boxAxis e 2) 0| ≤ A/c := by
    simpa only [inner_boxAxis] using
      contained_prism_normal_bound ha (mul_pos hρ hc).le hc z z' e g hsub
  have hInvNorm : ‖f.linear (boxAxis e 2)‖⁻¹ ≤ 4*c := by
    have hh := inv_anti₀ (by positivity : 0 < 1/(4*c)) hnorm
    simpa only [one_div, inv_inv] using hh
  change |unit (f.linear (boxAxis e 2)) 0| ≤ _
  rw [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit, PiLp.smul_apply,
    smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hnormpos), carrierAffine_linear]
  change ‖f.linear (boxAxis e 2)‖⁻¹ * |(ρ/(4*S))*g (boxAxis e 2) 0| ≤ _
  rw [abs_mul, abs_of_pos (by positivity : 0 < ρ/(4*S))]
  calc
    _ ≤ (4*c)*((ρ/(4*S))*(A/c)) := by gcongr
    _ = 4*(ρ*A/(4*min A (ρ*c))) := by change _ = 4*(ρ*A/(4*S)); field_simp

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
