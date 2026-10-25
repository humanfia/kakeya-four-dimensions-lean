-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.FineMap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineGeometry

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate
  (affine affine_apply volume_affine affine_dist_le stretch norm_sq_coords)

noncomputable section

abbrev fineContraction : ℝ := 1 / 100000000

def swapLong : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) 2)

theorem swapLong_apply (p : Space) (i : Fin 3) :
    swapLong p i = p (Equiv.swap (0 : Fin 3) 2 i) := by
  rfl

def fineAffine (e : AffineIsometryEquiv ℝ Space Space) (b : ℝ) (hb : 0 < b) :
    AffineEquiv ℝ Space Space :=
  e.symm.toAffineEquiv.trans
    (affine swapLong 0 fineContraction b⁻¹ (by norm_num) (inv_ne_zero hb.ne')).toAffineEquiv

theorem fineAffine_apply (e : AffineIsometryEquiv ℝ Space Space) {b : ℝ} (hb : 0 < b)
    (p : Space) : fineAffine e b hb p = fineContraction • stretch b⁻¹ (swapLong (e.symm p)) := by
  simp [fineAffine, affine_apply]

theorem fineAffine_volume (e : AffineIsometryEquiv ℝ Space Space) {b : ℝ} (hb : 0 < b)
    (U : Set Space) : volume (fineAffine e b hb '' U) =
      ENNReal.ofReal (fineContraction ^ 3 * b⁻¹ ^ 2) * volume U := by
  change volume ((fun p => affine swapLong 0 fineContraction b⁻¹ _ _ (e.symm p)) '' U) = _
  rw [← Set.image_image, volume_affine swapLong 0 (by norm_num) (inv_pos.mpr hb),
    WangZahlLot.Obl.wz_frostman_rigid_copies_volume.affine_volume_image]

theorem fineAffine_dist (e : AffineIsometryEquiv ℝ Space Space) {b : ℝ} (hb : 0 < b)
    (hb1 : b ≤ 1) (p q : Space) :
    dist (fineAffine e b hb p) (fineAffine e b hb q) ≤
      (fineContraction * b⁻¹) * dist p q := by
  have h := affine_dist_le swapLong 0 (by norm_num : 0 < fineContraction)
    ((one_le_inv₀ hb).mpr hb1) (e.symm p) (e.symm q)
  simpa [fineAffine] using h

theorem fineAffine_prism_norm {a b : ℝ} (hb : 0 < b) (hab : a ≤ b)
    (e : AffineIsometryEquiv ℝ Space Space) {p : Space}
    (hp : p ∈ e '' standardPrism a b) : ‖fineAffine e b hb p‖ ≤ 4 * fineContraction := by
  obtain ⟨p, hp, rfl⟩ := hp
  rw [fineAffine_apply, e.symm_apply_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : 0 < fineContraction)]
  have h0 : |b⁻¹ * p 0| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hb)]
    calc
      _ ≤ b⁻¹ * b := mul_le_mul_of_nonneg_left (hp.1.trans hab) (inv_nonneg.mpr hb.le)
      _ = 1 := inv_mul_cancel₀ hb.ne'
  have h1 : |b⁻¹ * p 1| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hb)]
    calc
      _ ≤ b⁻¹ * b := mul_le_mul_of_nonneg_left hp.2.1 (inv_nonneg.mpr hb.le)
      _ = 1 := inv_mul_cancel₀ hb.ne'
  have hsq : ‖stretch b⁻¹ (swapLong p)‖ ^ 2 =
      (p 2) ^ 2 + (b⁻¹ * p 1) ^ 2 + (b⁻¹ * p 0) ^ 2 := by
    rw [norm_sq_coords]
    simp [stretch, swapLong_apply, Equiv.swap_apply_def]
  have hs0 := sq_le_sq' (abs_le.mp h0).1 (abs_le.mp h0).2
  have hs1 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  have hs2 := sq_le_sq' (abs_le.mp hp.2.2).1 (abs_le.mp hp.2.2).2
  have hn : ‖stretch b⁻¹ (swapLong p)‖ ≤ 4 := by
    nlinarith [norm_nonneg (stretch b⁻¹ (swapLong p))]
  nlinarith only [hn]

/-- Fine tubes inside one prism have short, centrally located affine images. -/
theorem fineAffine_tube_data {a b δ : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hab : a ≤ b)
    (hδ : 0 < δ) (hδb : δ ≤ b) (e : AffineIsometryEquiv ℝ Space Space)
    (x v : Space) (hv : ‖v‖ = 1) (hT : tube δ x v ⊆ e '' standardPrism a b) :
    ‖fineAffine e b hb (x + (1 / 2 : ℝ) • v)‖ < 1 / 100 ∧
    ∃ u : Fin 3 → Space, Orthonormal ℝ u ∧
      fineAffine e b hb '' tube δ x v ⊆
        WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          (fineContraction * b⁻¹ * δ) (fineContraction * b⁻¹ * δ)
          (fineAffine e b hb (x + (1 / 2 : ℝ) • v)) u := by
  have hseg : segment ℝ x (x + v) ⊆ e '' standardPrism a b :=
    (self_subset_thickening hδ _).trans hT
  have hmid : x + (1 / 2 : ℝ) • v ∈ segment ℝ x (x + v) := by
    rw [segment_eq_image']
    exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by simp⟩
  have hnorm := fineAffine_prism_norm hb hab e (hseg hmid)
  refine ⟨by dsimp [fineContraction] at hnorm; linarith, ?_⟩
  apply affine_tube_prism (fineAffine e b hb) (by positivity)
    (by
      have hh := mul_le_mul_of_nonneg_left hδb (by positivity : 0 ≤ fineContraction * b⁻¹)
      have he : fineContraction * b⁻¹ * b = fineContraction := by field_simp
      rw [he] at hh
      dsimp [fineContraction] at hh
      linarith)
    (fineAffine_dist e hb hb1) x v hv
  have h0 := fineAffine_prism_norm hb hab e (hseg (left_mem_segment ℝ x (x + v)))
  have h1 := fineAffine_prism_norm hb hab e (hseg (right_mem_segment ℝ x (x + v)))
  have he : (fineAffine e b hb).linear v = fineAffine e b hb (x + v) - fineAffine e b hb x := by
    have he := (fineAffine e b hb).map_vadd x v
    simpa only [vadd_eq_add, add_comm] using (eq_sub_iff_add_eq.mpr he.symm)
  rw [he]
  have hn := norm_sub_le (fineAffine e b hb (x + v)) (fineAffine e b hb x)
  dsimp [fineContraction] at h0 h1
  linarith

abbrev fineRadius (δ b : ℝ) : ℝ := 4 * (fineContraction * b⁻¹ * δ)
abbrev fineFiberVolume : ℝ := 896 / fineContraction
abbrev fineFiberBound : ℝ := 1000000 * fineFiberVolume ^ 2

theorem fineAffine_preimage_tube_volume {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (hδb : δ ≤ b) (e : AffineIsometryEquiv ℝ Space Space) (z w : Space) (hw : ‖w‖ = 1) :
    volume (fineAffine e b hb ⁻¹' tube (fineRadius δ b) z w) ≤
      ENNReal.ofReal (fineFiberVolume * δ ^ 2) := by
  have hκ : 0 < fineContraction := by norm_num
  have hr : 0 ≤ fineRadius δ b := by dsimp [fineRadius]; positivity
  have hr1 : fineRadius δ b ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hδb (by positivity : 0 ≤ 4 * fineContraction * b⁻¹)
    have he : 4 * fineContraction * b⁻¹ * b = 4 * fineContraction := by field_simp
    rw [he] at h
    dsimp [fineRadius, fineContraction] at *
    linarith
  rw [affine_volume_preimage _ (by positivity : 0 < fineContraction ^ 3 * b⁻¹ ^ 2)
    (fineAffine_volume e hb)]
  calc
    _ ≤ ENNReal.ofReal (fineContraction ^ 3 * b⁻¹ ^ 2)⁻¹ *
        ENNReal.ofReal (56 * (fineRadius δ b) ^ 2) := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity)]
      exact mul_le_mul' le_rfl (tube_volume_upper hr hr1 z w hw)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [fineRadius, fineFiberVolume]
      field_simp
      ring

/-- The affine-normalized fine family admits a separated cover with a universal loss. -/
theorem fine_prism_net {a b δ : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hab : a ≤ b)
    (hδ : 0 < δ) (hδb : δ ≤ b) (e : AffineIsometryEquiv ℝ Space Space)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, tube δ (x i) (v i) ⊆ e '' standardPrism a b)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) :
    ∃ (M : ℕ) (j : Fin M → Fin n) (z w : Fin M → Space),
      0 < M ∧ Function.Injective j ∧ (∀ i, ‖w i‖ = 1) ∧
      (∀ i, tube (fineRadius δ b) (z i) (w i) ⊆ unitBall) ∧
      (∀ i i', i ≠ i' → volume (tube (fineRadius δ b) (z i) (w i) ∩
        tube (fineRadius δ b) (z i') (w i')) ≤
          (1 / 2 : ENNReal) * volume (tube (fineRadius δ b) (z i) (w i))) ∧
      (∀ i, fineAffine e b hb '' tube δ (x (j i)) (v (j i)) ⊆
        tube (fineRadius δ b) (z i) (w i)) ∧
      WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst * n ≤ (M : ℝ) * fineFiberBound := by
  have hκ : 0 < fineContraction := by norm_num
  have hρ : 0 < fineContraction * b⁻¹ * δ := by positivity
  have hρ1 : fineContraction * b⁻¹ * δ ≤ 1 / 1000000 := by
    have h := mul_le_mul_of_nonneg_left hδb (by positivity : 0 ≤ fineContraction * b⁻¹)
    have he : fineContraction * b⁻¹ * b = fineContraction := by field_simp
    rw [he] at h
    dsimp [fineContraction] at h
    linarith
  have hdata := fun i => fineAffine_tube_data hb hb1 hab hδ hδb e (x i) (v i) (hv i) (hT i)
  choose u hu hprism using fun i => (hdata i).2
  exact affine_tube_net hδ hρ hρ1 (by norm_num : 0 ≤ fineFiberVolume) hn x v
    (fineAffine e b hb) (fun i => fineAffine e b hb (x i + (1 / 2 : ℝ) • v i)) u hu
    (fun i => (hdata i).1) hv hover hprism (fineAffine_preimage_tube_volume hb hδ hδb e)

end

end WangZahlLot.Obl.wz_nonflat_factored_improvement
