-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.SharpCluster.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.SharpBrush
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

local notation "affineNormalize" => WangZahlLot.Obl.wz_affine_robust_cluster_estimate.affine

lemma sharp_scale_identity {κ θ δ lam m : ℝ}
    (hκ : 0 < κ) (hθ : 0 < θ) (hδ : 0 < δ) (_hlam : 0 < lam) (hm : 0 < m)
    (a α N : ℝ) :
    (κ ^ 3 * (θ⁻¹) ^ 2) *
      ((a * κ ^ ((3 / 2 : ℝ) + α) * (κ⁻¹) ^ (-(1 / 2 : ℝ))) *
        δ ^ ((3 / 2 : ℝ) + α) * θ ^ ((1 / 2 : ℝ) - α) * lam ^ 3 *
          m ^ (-(1 / 2 : ℝ)) * N) =
      a * (κ * θ⁻¹ * δ) ^ ((3 / 2 : ℝ) + α) * (κ * lam) ^ 3 *
        (m / κ) ^ (-(1 / 2 : ℝ)) * N := by
  have ht : (θ⁻¹) ^ 2 * θ ^ ((1 / 2 : ℝ) - α) = (θ⁻¹) ^ ((3 / 2 : ℝ) + α) := by
    rw [← Real.rpow_natCast (θ⁻¹) 2, Real.inv_rpow hθ.le, ← Real.rpow_neg hθ.le,
      ← Real.rpow_add hθ, Real.inv_rpow hθ.le, ← Real.rpow_neg hθ.le]
    congr 1
    norm_num
    ring
  rw [Real.mul_rpow (mul_nonneg hκ.le (inv_nonneg.mpr hθ.le)) hδ.le,
    Real.mul_rpow hκ.le (inv_nonneg.mpr hθ.le), mul_pow,
    div_eq_mul_inv m κ, Real.mul_rpow hm.le (inv_nonneg.mpr hκ.le)]
  calc
    _ = a * κ ^ ((3 / 2 : ℝ) + α) * (κ⁻¹) ^ (-(1 / 2 : ℝ)) *
        δ ^ ((3 / 2 : ℝ) + α) * ((θ⁻¹) ^ 2 * θ ^ ((1 / 2 : ℝ) - α)) *
        κ ^ 3 * lam ^ 3 * m ^ (-(1 / 2 : ℝ)) * N := by ring
    _ = _ := by rw [ht]; ring

def SharpCluster : Prop :=
  ∀ C β α : ℝ, 1 ≤ C → 0 < β → β ≤ 1 → 0 < α →
    ∃ c : ℝ, 0 < c ∧ ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 100 ∧
    ∀ δ θ lam m : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ θ → θ ≤ 1 → δ ≤ s * θ →
      0 < lam → lam ≤ 1 → 1 ≤ m →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (z w : Space), 0 < n →
    (∀ i, ‖v i‖ = 1) → ‖w‖ = 1 →
    (∀ i, min ‖v i - w‖ ‖v i + w‖ ≤ C * θ) →
    (∀ i, tube δ (x i) (v i) ⊆ thickening (C * θ) (segment ℝ z (z + (6 : ℝ) • w))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i) →
    (∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal m * volume W) →
    (∀ p u r, ‖u‖ = 1 → δ ≤ r →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r}.ncard : ℝ) ≤
        C * (r / θ) ^ β * ({i | p ∈ Y i}.ncard : ℝ)) →
    ENNReal.ofReal (c * δ ^ ((3 / 2 : ℝ) + α) * θ ^ ((1 / 2 : ℝ) - α) *
      lam ^ 3 * m ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ)) ≤ volume (⋃ i, Y i)

/-- Apply the accepted affine geometry to the sharper dependence on the counting constant. -/
theorem sharp_cluster : SharpCluster := by
  classical
  intro C β α hC hβ hβ1 hα
  obtain ⟨ρ, hρ, hρ1, hρhalf⟩ :=
    WangZahlLot.Obl.wz_affine_robust_cluster_estimate.exists_robust_radius hC hβ
  let κ : ℝ := 1 / (100 * (C + 4))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκeq : κ * (100 * (C + 4)) = 1 := by dsimp [κ]; field_simp
  have hκ1 : κ ≤ 1 := by nlinarith
  have hκC1 : κ * (C + 1) ≤ 1 := by nlinarith
  have hκC3 : κ * (C + 3) ≤ 1 / 4 := by nlinarith
  let b : ℝ := ρ / (4 * (C + 1) ^ 2)
  have hden : 0 < 4 * (C + 1) ^ 2 := by positivity
  have hb : 0 < b := div_pos hρ hden
  have hb1 : b ≤ 1 := (div_le_one hden).mpr (by nlinarith)
  have hbeq : 4 * (C + 1) ^ 2 * b = ρ := mul_div_cancel₀ _ hden.ne'
  obtain ⟨a, ha, hBroad⟩ := sharp_broad α b hα hb hb1
  let c : ℝ := a * κ ^ ((3 / 2 : ℝ) + α) * (κ⁻¹) ^ (-(1 / 2 : ℝ))
  refine ⟨c, by dsimp [c]; positivity, min (1 / 100) ρ,
    lt_min (by norm_num) hρ, min_le_left _ _, ?_⟩
  intro δ θ lam m hδ hδmax hδθ hθ1 hrel hlam hlam1 hm n x v Y z w hn hv hw
    hcap hcyl hYm hYT hmass hcount hrob
  have hθ : 0 < θ := hδ.trans_le hδθ
  have hθinv : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).mpr hθ1
  have hδ' : 0 < κ * θ⁻¹ * δ := by positivity
  have hδ'max : κ * θ⁻¹ * δ ≤ 1 / 100 := by
    calc
      κ * θ⁻¹ * δ = κ * (δ / θ) := by ring
      _ ≤ κ * min (1 / 100) ρ := by
        gcongr
        exact (div_le_iff₀ hθ).mpr hrel
      _ ≤ 1 * (1 / 100 : ℝ) :=
        mul_le_mul hκ1 (min_le_left _ _) (le_of_lt (lt_min (by norm_num) hρ)) (by norm_num)
      _ = _ := by ring
  have hlam'1 : κ * lam ≤ 1 := by nlinarith
  have hm' : 1 ≤ m / κ := (le_div_iff₀ hκ).mpr (by linarith)
  obtain ⟨e, he⟩ := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.exists_rotation hw
  let F := affineNormalize e (z + (3 : ℝ) • w) κ θ⁻¹ hκ.ne' (inv_pos.mpr hθ).ne'
  let u : Fin n → Space := fun i =>
    WangZahlLot.Obl.wz_affine_robust_cluster_estimate.stretch θ⁻¹ (e (v i))
  let v' : Fin n → Space := fun i => WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit (u i)
  let x' : Fin n → Space := fun i => F (x i + (1 / 2 : ℝ) • v i) - (1 / 2 : ℝ) • v' i
  let Y' : Fin n → Set Space := fun i => F '' Y i
  have hvol : ∀ W : Set Space, volume (F '' W) =
      ENNReal.ofReal (κ ^ 3 * (θ⁻¹) ^ 2) * volume W :=
    WangZahlLot.Obl.wz_affine_robust_cluster_estimate.volume_affine e _ hκ (inv_pos.mpr hθ)
  have hu : ∀ i, ‖u i‖ ≤ C + 1 := by
    intro i
    have hecap : WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd (e (v i))
        WangZahlLot.Obl.wz_affine_robust_cluster_estimate.axis ≤ C * θ := by
      rw [← he, WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd_isometry]
      exact hcap i
    calc
      ‖u i‖ ≤ 1 + θ⁻¹ * (C * θ) :=
        WangZahlLot.Obl.wz_affine_robust_cluster_estimate.norm_stretch_cap hθinv hecap
      _ = C + 1 := by field_simp; ring
  have hune : ∀ i, u i ≠ 0 := by
    intro i
    have h := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.norm_le_stretch hθinv (e (v i))
    rw [e.norm_map, hv i] at h
    exact norm_ne_zero_iff.mp (by linarith)
  have hv' : ∀ i, ‖v' i‖ = 1 := fun i =>
    WangZahlLot.Obl.wz_affine_robust_cluster_estimate.norm_unit (hune i)
  have hcover : ∀ i, F '' tube δ (x i) (v i) ⊆ tube (κ * θ⁻¹ * δ) (x' i) (v' i) := by
    intro i
    apply WangZahlLot.Obl.wz_affine_robust_cluster_estimate.image_tube_extend F (x i) (v i)
      (v' i) (l := κ * ‖u i‖) (by positivity) (by positivity)
    · exact (mul_le_mul_of_nonneg_left (hu i) hκ.le).trans hκC1
    · change κ • u i = (κ * ‖u i‖) • WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit (u i)
      rw [mul_smul, WangZahlLot.Obl.wz_affine_robust_cluster_estimate.norm_smul_unit (hune i)]
    · exact WangZahlLot.Obl.wz_affine_robust_cluster_estimate.affine_dist_le e _ hκ hθinv
  have hball : ∀ i, tube (κ * θ⁻¹ * δ) (x' i) (v' i) ⊆ ball 0 1 := by
    intro i
    apply WangZahlLot.Obl.wz_affine_robust_cluster_estimate.centered_tube_subset_ball
      (hv' i) _ hδ'max
    have hp : x i + (1 / 2 : ℝ) • v i ∈ tube δ (x i) (v i) := by
      apply self_subset_thickening hδ
      rw [segment_eq_image']
      exact ⟨1 / 2, by norm_num, by simp⟩
    exact (WangZahlLot.Obl.wz_affine_robust_cluster_estimate.affine_cylinder_norm
      e he hκ hθ hθ1 (hcyl i hp)).le.trans hκC3
  have hYm' : ∀ i, MeasurableSet (Y' i) := fun i =>
    F.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm i)
  have hYT' : ∀ i, Y' i ⊆ tube (κ * θ⁻¹ * δ) (x' i) (v' i) :=
    fun i => (image_mono (hYT i)).trans (hcover i)
  have hmass' := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.density_transport F hκ hvol Y hmass
  have hcount' := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.convex_count_transport
    F hκ hvol x v x' v' hcover hcount
  have hpair : ∀ i j, WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd (v i) (v j) ≤
      (2 * (C + 1) ^ 2 * θ) * WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd (v' i) (v' j) := by
    intro i j
    have hp := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd_stretch hθinv
      (by linarith : 0 ≤ C + 1) (by simpa using hv i : ‖e (v i)‖ = 1)
      (by simpa using hv j : ‖e (v j)‖ = 1) (hu i) (hu j)
    rw [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd_isometry] at hp
    calc
      _ = θ * (θ⁻¹ * WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd (v i) (v j)) := by field_simp
      _ ≤ θ * (2 * (C + 1) ^ 2 *
          WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd (v' i) (v' j)) :=
        mul_le_mul_of_nonneg_left hp hθ.le
      _ = _ := by ring
  have hbroad : ∀ p q : Space, ‖q‖ = 1 →
      ({i | p ∈ Y' i ∧ min ‖v' i - q‖ ‖v' i + q‖ ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y' i}.ncard : ℝ) := by
    intro p q hq
    have hmem (i : Fin n) : p ∈ Y' i ↔ F.symm p ∈ Y i := by
      constructor
      · rintro ⟨y, hy, rfl⟩; simpa using hy
      · intro hp; exact ⟨F.symm p, hp, F.apply_symm_apply p⟩
    simp only [hmem]
    apply WangZahlLot.Obl.wz_affine_robust_cluster_estimate.cap_count_transfer
      {i | F.symm p ∈ Y i} v v' hv (A := 2 * (C + 1) ^ 2 * θ) (r := ρ * θ)
      (by positivity) _ hpair _ q
    · nlinarith only [congrArg (fun t : ℝ => t * θ) hbeq]
    · intro q hq
      have hδρ : δ ≤ ρ * θ :=
        hrel.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hθ.le)
      have hh := hrob (F.symm p) q (ρ * θ) hq hδρ
      rw [mul_div_cancel_right₀ _ hθ.ne'] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hρhalf (Nat.cast_nonneg _))
  have hresult := hBroad (κ * θ⁻¹ * δ) (κ * lam) (m / κ) hδ' hδ'max
    (mul_pos hκ hlam) hlam'1 hm' n x' v' Y' hn hv' hball hYm' hYT' hmass' hcount' hbroad
  have hUE : (⋃ i, Y' i) = F '' (⋃ i, Y i) := by simp only [Y', image_iUnion]
  rw [hUE, hvol] at hresult
  apply (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < κ ^ 3 * (θ⁻¹) ^ 2))
    ENNReal.ofReal_ne_top).mp
  rw [← ENNReal.ofReal_mul (by positivity)]
  dsimp [c]
  rw [sharp_scale_identity hκ hθ hδ hlam (by linarith : 0 < m)]
  exact hresult

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
