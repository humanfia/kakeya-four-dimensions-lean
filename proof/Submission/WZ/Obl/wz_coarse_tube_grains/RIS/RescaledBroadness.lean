-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaledBroadness.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleGeometry
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Incidence

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set
open wz_affine_robust_cluster_estimate
open wz_extremal_lipschitz_grains

/-- Transverse normalization expands all projective distances in a covered
fiber by at least the reciprocal coarse radius, up to an absolute constant. -/
theorem pd_le_rescaledDir (e : Space ≃ₗᵢ[ℝ] Space) {w : Space}
    (hew : e w = axis) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huw : pd u w < 4 * ρ) (hvw : pd v w < 4 * ρ) :
    pd u v ≤ 50 * ρ * pd (rescaledDir e ρ u) (rescaledDir e ρ v) := by
  have hh := pd_stretch ((one_le_inv₀ hρ).mpr hρ1) (by norm_num : (0 : ℝ) ≤ 5)
    (by simpa using hu : ‖e u‖ = 1) (by simpa using hv : ‖e v‖ = 1)
    (stretch_dir_norm_le e hew hρ hρ1 huw) (stretch_dir_norm_le e hew hρ hρ1 hvw)
  rw [pd_isometry] at hh
  change ρ⁻¹ * pd u v ≤ 2 * 5 ^ 2 * pd (rescaledDir e ρ u) (rescaledDir e ρ v) at hh
  have hh' := mul_le_mul_of_nonneg_left hh hρ.le
  calc
    pd u v = ρ * (ρ⁻¹ * pd u v) := by field_simp
    _ ≤ ρ * (2 * 5 ^ 2 * pd (rescaledDir e ρ u) (rescaledDir e ρ v)) := hh'
    _ = _ := by ring

/-- A cap around an arbitrary rescaled direction pulls back to a cap about
any one of its occupied directions. -/
theorem rescaled_cap_pair_bound (e : Space ≃ₗᵢ[ℝ] Space) {w : Space}
    (hew : e w = axis) {ρ s : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {u v z : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huw : pd u w < 4 * ρ) (hvw : pd v w < 4 * ρ)
    (huv : pd (rescaledDir e ρ u) z ≤ s) (hvv : pd (rescaledDir e ρ v) z ≤ s) :
    pd u v ≤ 100 * ρ * s := by
  have htri := pd_triangle (rescaledDir e ρ u) z (rescaledDir e ρ v)
  rw [pd_symm z] at htri
  have hp : pd (rescaledDir e ρ u) (rescaledDir e ρ v) ≤ 2 * s := by linarith
  calc
    pd u v ≤ 50 * ρ * pd (rescaledDir e ρ u) (rescaledDir e ρ v) :=
      pd_le_rescaledDir e hew hρ hρ1 hu hv huw hvw
    _ ≤ 50 * ρ * (2 * s) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- Relative angular broadness at the coarse scale becomes absolute
broadness for the normalized directions. The factor `100^beta` is constant. -/
theorem rescaled_relative_cap_bound {n : ℕ}
    (x v : Fin n → Space) (Y : Fin n → Set Space) (y w : Space)
    (e : Space ≃ₗᵢ[ℝ] Space) (hew : e w = axis)
    {δ ρ C β : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hC : 1 ≤ C) (hβ : 0 ≤ β) (hw : ‖w‖ = 1)
    (hv : ∀ i, (Y i).Nonempty → ‖v i‖ = 1)
    (hcover : ∀ i, (Y i).Nonempty → Tube δ (x i) (v i) ⊆ Tube ρ y w)
    (hbroad : ∀ p u b, ‖u‖ = 1 → δ ≤ b → b ≤ ρ →
      ({i | p ∈ Y i ∧ pd (v i) u ≤ b}.ncard : ℝ) ≤
        (C * (b / ρ) ^ β) * incidence Y p) :
    ∀ p u s, 0 < s → δ ≤ 100 * ρ * s →
      ({i | p ∈ Y i ∧ pd (rescaledDir e ρ (v i)) u ≤ s}.ncard : ℝ) ≤
        (C * (100 : ℝ) ^ β * s ^ β) * incidence Y p := by
  intro p u s hs hδs
  have hinc : 0 ≤ incidence Y p := incidence_nonneg Y p
  have hcoef : C * (100 : ℝ) ^ β * s ^ β = C * (100 * s) ^ β := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 100) hs.le]
    ring
  rw [hcoef]
  by_cases hsmall : 100 * s ≤ 1
  · let A : Set (Fin n) := {i | p ∈ Y i ∧ pd (rescaledDir e ρ (v i)) u ≤ s}
    by_cases hA : A.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hA
      have hsub : A ⊆ {i | p ∈ Y i ∧ pd (v i) (v i₀) ≤ 100 * ρ * s} := by
        intro i hi
        refine ⟨hi.1, ?_⟩
        exact rescaled_cap_pair_bound e hew hρ hρ1 (hv i ⟨p, hi.1⟩)
          (hv i₀ ⟨p, hi₀.1⟩)
          (pd_lt_of_tube_subset hδ (hv i ⟨p, hi.1⟩) hw (hcover i ⟨p, hi.1⟩))
          (pd_lt_of_tube_subset hδ (hv i₀ ⟨p, hi₀.1⟩) hw (hcover i₀ ⟨p, hi₀.1⟩))
          hi.2 hi₀.2
      have hb := hbroad p (v i₀) (100 * ρ * s) (hv i₀ ⟨p, hi₀.1⟩) hδs
        (by nlinarith)
      have hratio : 100 * ρ * s / ρ = 100 * s := by field_simp
      rw [hratio] at hb
      exact (show (A.ncard : ℝ) ≤ _ from by exact_mod_cast Set.ncard_mono hsub).trans hb
    · have hzero : A = ∅ := not_nonempty_iff_eq_empty.mp hA
      change (A.ncard : ℝ) ≤ _
      rw [hzero, ncard_empty, Nat.cast_zero]
      positivity
  · have hmono : ({i | p ∈ Y i ∧ pd (rescaledDir e ρ (v i)) u ≤ s}.ncard : ℝ) ≤
        incidence Y p := by
      rw [incidence_eq_ncard]
      exact_mod_cast Set.ncard_mono (show {i | p ∈ Y i ∧
        pd (rescaledDir e ρ (v i)) u ≤ s} ⊆ {i | p ∈ Y i} from fun _ hi => hi.1)
    have hp : 1 ≤ (100 * s) ^ β := Real.one_le_rpow (le_of_not_ge hsmall) hβ
    have hc : 1 ≤ C * (100 * s) ^ β := by nlinarith
    exact hmono.trans (by nlinarith)

/-- Incidence is unchanged by an injective change of spatial coordinates. -/
theorem incidence_equiv_image {n : ℕ} (F : Space ≃ Space)
    (Y : Fin n → Set Space) (p : Space) :
    incidence (fun i => F '' Y i) p = incidence Y (F.symm p) := by
  rw [incidence_eq_ncard, incidence_eq_ncard]
  congr 2
  ext i
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro hp
    exact ⟨F.symm p, hp, F.apply_symm_apply p⟩

/-- The exact angular cap count also commutes with a bijective change of
the spatial coordinates; the directions need not change. -/
theorem cap_count_equiv_image {n : ℕ} (F : Space ≃ Space)
    (Y : Fin n → Set Space) (v : Fin n → Space) (p u : Space) (s : ℝ) :
    {i | p ∈ F '' Y i ∧ pd (v i) u ≤ s}.ncard =
      {i | F.symm p ∈ Y i ∧ pd (v i) u ≤ s}.ncard := by
  congr 1
  ext i
  have hmem : p ∈ F '' Y i ↔ F.symm p ∈ Y i := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro hp
      exact ⟨F.symm p, hp, F.apply_symm_apply p⟩
  exact and_congr_left fun _ => hmem

/-- The relative cap estimate holds for the affine-image shading at all
scales above `delta / (100 rho)`. -/
theorem rescaled_image_relative_cap_bound {n : ℕ}
    (x v : Fin n → Space) (Y : Fin n → Set Space) (y w : Space)
    (e : Space ≃ₗᵢ[ℝ] Space) (hew : e w = axis) (F : Space ≃ Space)
    {δ ρ C β : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hC : 1 ≤ C) (hβ : 0 ≤ β) (hw : ‖w‖ = 1)
    (hv : ∀ i, (Y i).Nonempty → ‖v i‖ = 1)
    (hcover : ∀ i, (Y i).Nonempty → Tube δ (x i) (v i) ⊆ Tube ρ y w)
    (hbroad : ∀ p u b, ‖u‖ = 1 → δ ≤ b → b ≤ ρ →
      ({i | p ∈ Y i ∧ pd (v i) u ≤ b}.ncard : ℝ) ≤
        (C * (b / ρ) ^ β) * incidence Y p) :
    ∀ p u s, δ / (100 * ρ) ≤ s →
      ({i | p ∈ F '' Y i ∧ pd (rescaledDir e ρ (v i)) u ≤ s}.ncard : ℝ) ≤
        (C * (100 : ℝ) ^ β * s ^ β) * incidence (fun i => F '' Y i) p := by
  intro p u s hs
  rw [cap_count_equiv_image, incidence_equiv_image]
  have hspos : 0 < s := (by positivity : 0 < δ / (100 * ρ)).trans_le hs
  exact rescaled_relative_cap_bound x v Y y w e hew hδ hρ hρ1 hC hβ hw hv hcover
    hbroad (F.symm p) u s hspos (by
      have hh := (div_le_iff₀ (by positivity : 0 < 100 * ρ)).mp hs
      nlinarith)

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
