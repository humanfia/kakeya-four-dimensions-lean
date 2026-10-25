-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_robust_cluster_estimate.Proof.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Types
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Transport
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Tubes
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Counts
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Arithmetic

namespace WangZahlLot.Obl.wz_affine_robust_cluster_estimate
open MeasureTheory Set Metric
open scoped ENNReal
set_option linter.unusedVariables false
noncomputable section

/-- The affine reduction preserves the exponent in the broad estimate. -/
theorem broad_to_robust {K : ℝ} (hK : 1 ≤ K) (H : Broad K) : RobustCluster K := by
  classical
  intro C β α hC hβ hβ1 hα
  obtain ⟨ρ, hρ, hρ1, hρhalf⟩ := exists_robust_radius hC hβ
  have hC0 : 0 < C := by linarith
  let κ : ℝ := 1 / (100 * (C + 4))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκeq : κ * (100 * (C + 4)) = 1 := by dsimp [κ]; field_simp
  have hκ1 : κ ≤ 1 := by nlinarith
  have hκC1 : κ * (C + 1) ≤ 1 := by nlinarith
  have hκC3 : κ * (C + 3) ≤ 1 / 4 := by nlinarith
  let b : ℝ := ρ / (4 * (C + 1) ^ 2)
  have hden : 0 < 4 * (C + 1) ^ 2 := by positivity
  have hb : 0 < b := div_pos hρ hden
  have hb1 : b ≤ 1 := by
    apply (div_le_one hden).mpr
    nlinarith
  have hbeq : 4 * (C + 1) ^ 2 * b = ρ := mul_div_cancel₀ _ hden.ne'
  obtain ⟨a, ha, H⟩ := H α b hα hb hb1
  let c : ℝ := a * κ ^ ((3 / 2 : ℝ) + α) * κ ^ K * (κ⁻¹) ^ (-K) / κ ^ 3
  have hc : 0 < c := by dsimp [c]; positivity
  let s : ℝ := min (1 / 100) ρ
  have hs : 0 < s := lt_min (by norm_num) hρ
  have hs1 : s ≤ 1 / 100 := min_le_left _ _
  have hsρ : s ≤ ρ := min_le_right _ _
  refine ⟨c, hc, s, hs, hs1, ?_⟩
  intro δ θ lam m hδ hδ1 hδθ hθ1 hrel hlam hlam1 hm n x v Y z w hn hv hw hcap hcluster hYm hYT hdenY hconv hrob
  have hθ : 0 < θ := hδ.trans_le hδθ
  have hm0 : 0 < m := by linarith
  have ht : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).mpr hθ1
  have ht0 : 0 < θ⁻¹ := inv_pos.mpr hθ
  have hδ' : 0 < κ * θ⁻¹ * δ := by positivity
  have hδ'1 : κ * θ⁻¹ * δ ≤ 1 / 100 := by
    calc
      κ * θ⁻¹ * δ = κ * (δ / θ) := by ring
      _ ≤ κ * s := by gcongr; exact (div_le_iff₀ hθ).mpr hrel
      _ ≤ 1 * (1 / 100 : ℝ) := mul_le_mul hκ1 hs1 hs.le (by norm_num)
      _ = _ := by ring
  have hlam' : 0 < κ * lam := mul_pos hκ hlam
  have hlam'1 : κ * lam ≤ 1 := by nlinarith
  have hm' : 1 ≤ m / κ := (le_div_iff₀ hκ).mpr (by nlinarith)
  obtain ⟨e, hew⟩ := exists_rotation hw
  let F := affine e (z + (3 : ℝ) • w) κ θ⁻¹ hκ.ne' ht0.ne'
  let v' : Fin n → E := fun i => unit (stretch θ⁻¹ (e (v i)))
  let x' : Fin n → E := fun i => F (x i + (1 / 2 : ℝ) • v i) - (1 / 2 : ℝ) • v' i
  let Y' : Fin n → Set E := fun i => F '' Y i
  have hvol : ∀ W : Set E, volume (F '' W) = ENNReal.ofReal (κ ^ 3 * (θ⁻¹) ^ 2) * volume W :=
    volume_affine e (z + (3 : ℝ) • w) hκ ht0
  have hL : ∀ i, ‖stretch θ⁻¹ (e (v i))‖ ≤ C + 1 := by
    intro i
    have hcap' : pd (e (v i)) axis ≤ C * θ := by
      rw [← hew, pd_isometry]
      exact hcap i
    calc
      ‖stretch θ⁻¹ (e (v i))‖ ≤ 1 + θ⁻¹ * (C * θ) := norm_stretch_cap ht hcap'
      _ = C + 1 := by field_simp; ring
  have hne : ∀ i, stretch θ⁻¹ (e (v i)) ≠ 0 := by
    intro i
    have h := norm_le_stretch ht (e (v i))
    rw [e.norm_map, hv i] at h
    exact norm_ne_zero_iff.mp (by linarith)
  have hv' : ∀ i, ‖v' i‖ = 1 := fun i => norm_unit (hne i)
  have hcover : ∀ i, F '' tube δ (x i) (v i) ⊆ tube (κ * θ⁻¹ * δ) (x' i) (v' i) := by
    intro i
    apply image_tube_extend F (x i) (v i) (v' i) (l := κ * ‖stretch θ⁻¹ (e (v i))‖)
      (mul_pos hκ ht0) (by positivity)
    · exact (mul_le_mul_of_nonneg_left (hL i) hκ.le).trans hκC1
    · change κ • stretch θ⁻¹ (e (v i)) = (κ * ‖stretch θ⁻¹ (e (v i))‖) • unit (stretch θ⁻¹ (e (v i)))
      rw [mul_smul, norm_smul_unit (hne i)]
    · exact affine_dist_le e (z + (3 : ℝ) • w) hκ ht
  have hball : ∀ i, tube (κ * θ⁻¹ * δ) (x' i) (v' i) ⊆ ball (0 : E) 1 := by
    intro i
    apply centered_tube_subset_ball (hv' i) _ hδ'1
    have hp : x i + (1 / 2 : ℝ) • v i ∈ tube δ (x i) (v i) := by
      apply self_subset_thickening hδ
      rw [segment_eq_image']
      exact ⟨1 / 2, by norm_num, by simp⟩
    exact (affine_cylinder_norm e hew hκ hθ hθ1 (hcluster i hp)).le.trans hκC3
  have hYm' : ∀ i, MeasurableSet (Y' i) := by
    intro i
    exact F.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm i)
  have hYT' : ∀ i, Y' i ⊆ tube (κ * θ⁻¹ * δ) (x' i) (v' i) :=
    fun i => (image_mono (hYT i)).trans (hcover i)
  have hden' := density_transport F hκ hvol Y hdenY
  have hconv' := convex_count_transport F hκ hvol x v x' v' hcover hconv
  have hpair : ∀ i j, pd (v i) (v j) ≤
      (2 * (C + 1) ^ 2 * θ) * pd (v' i) (v' j) := by
    intro i j
    have hp := pd_stretch ht (by linarith : 0 ≤ C + 1)
      (by simpa using hv i : ‖e (v i)‖ = 1) (by simpa using hv j : ‖e (v j)‖ = 1) (hL i) (hL j)
    rw [pd_isometry] at hp
    calc
      pd (v i) (v j) = θ * (θ⁻¹ * pd (v i) (v j)) := by field_simp
      _ ≤ θ * (2 * (C + 1) ^ 2 * pd (v' i) (v' j)) := mul_le_mul_of_nonneg_left hp hθ.le
      _ = _ := by ring
  have hbroad : ∀ p u : E, ‖u‖ = 1 →
      ({i | p ∈ Y' i ∧ pd (v' i) u ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y' i}.ncard : ℝ) := by
    intro p u hu
    have hmem (i : Fin n) : p ∈ Y' i ↔ F.symm p ∈ Y i := by
      constructor
      · rintro ⟨q, hq, rfl⟩; simpa using hq
      · intro hp; exact ⟨F.symm p, hp, F.apply_symm_apply p⟩
    simp only [hmem]
    apply cap_count_transfer {i | F.symm p ∈ Y i} v v' hv
      (A := 2 * (C + 1) ^ 2 * θ) (r := ρ * θ) (by positivity) _ hpair _ u
    · nlinarith only [congrArg (fun x : ℝ => x * θ) hbeq]
    · intro u hu
      have hr : δ ≤ ρ * θ := hrel.trans (mul_le_mul_of_nonneg_right hsρ hθ.le)
      have hh := hrob (F.symm p) u (ρ * θ) hu hr
      rw [mul_div_cancel_right₀ _ hθ.ne'] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hρhalf (Nat.cast_nonneg _))
  have hresult := H (κ * θ⁻¹ * δ) (κ * lam) (m / κ) hδ' hδ'1 hlam' hlam'1 hm'
    n x' v' Y' hn hv' hball hYm' hYT' hden' hconv' hbroad
  have hunion : (⋃ i, Y' i) = F '' (⋃ i, Y i) := by simp only [Y', image_iUnion]
  rw [hunion, hvol] at hresult
  apply (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < κ ^ 3 * (θ⁻¹) ^ 2))
    ENNReal.ofReal_ne_top).mp
  rw [← ENNReal.ofReal_mul (by positivity)]
  change ENNReal.ofReal ((κ ^ 3 * (θ⁻¹) ^ 2) *
    ((a * κ ^ ((3 / 2 : ℝ) + α) * κ ^ K * (κ⁻¹) ^ (-K) / κ ^ 3) *
      δ ^ ((3 / 2 : ℝ) + α) * θ ^ ((1 / 2 : ℝ) - α) * lam ^ K * m ^ (-K) *
        (n : ℝ) ^ (1 / 2 : ℝ))) ≤ _
  rw [scaled_power_identity hκ hθ hδ hlam hm0]
  exact hresult

end
end WangZahlLot.Obl.wz_affine_robust_cluster_estimate
