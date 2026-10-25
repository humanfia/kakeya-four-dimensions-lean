-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.AffineSlabs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Basic

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

/-- The preimage of a positive-width slab under an invertible affine map is a slab. -/
lemma affine_preimage_slab (f : Space ≃ᵃ[ℝ] Space) {u : Space} (hu : ‖u‖ = 1)
    (t : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ (v : Space) (t' r' : ℝ), ‖v‖ = 1 ∧ 0 < r' ∧
      f ⁻¹' slab u t r = slab v t' r' := by
  let z := LinearMap.adjoint (f.linear : Space →ₗ[ℝ] Space) u
  have hz : z ≠ 0 := by
    intro h
    have he := LinearMap.adjoint_inner_left (f.linear : Space →ₗ[ℝ] Space)
      (f.linear.symm u) u
    change inner ℝ z (f.linear.symm u) = _ at he
    rw [h, inner_zero_left] at he
    change 0 = inner ℝ u (f.linear (f.linear.symm u)) at he
    rw [f.linear.apply_symm_apply, real_inner_self_eq_norm_sq, hu] at he
    norm_num at he
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let v : Space := ‖z‖⁻¹ • z
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hz]
  have hf (p : Space) : f p = f.linear p + f 0 := by
    simpa using f.map_vadd 0 p
  have hi (p : Space) :
      inner ℝ u (f p) - t = ‖z‖ * (inner ℝ v p - (t - inner ℝ u (f 0)) / ‖z‖) := by
    rw [hf, inner_add_right]
    simp only [v, inner_smul_left, RCLike.conj_to_real]
    rw [show inner ℝ z p = inner ℝ u (f.linear p) from
      LinearMap.adjoint_inner_left _ _ _]
    field_simp
    ring
  refine ⟨v, (t - inner ℝ u (f 0)) / ‖z‖, r / ‖z‖, hv, div_pos hr hn, ?_⟩
  ext p
  change |inner ℝ u (f p) - t| ≤ r ↔ _
  rw [hi, abs_mul, abs_of_pos hn]
  change ‖z‖ * _ ≤ r ↔ |inner ℝ v p - (t - inner ℝ u (f 0)) / ‖z‖| ≤ r / ‖z‖
  rw [le_div_iff₀ hn]
  rw [mul_comm ‖z‖]

lemma image_inter_preimage (f : Space ≃ᵃ[ℝ] Space) (D W : Set Space) :
    f '' (D ∩ f ⁻¹' W) = f '' D ∩ W := by
  ext p
  constructor
  · rintro ⟨q, ⟨hq, hqW⟩, rfl⟩
    exact ⟨⟨q, hq, rfl⟩, hqW⟩
  · rintro ⟨⟨q, hq, rfl⟩, hp⟩
    exact ⟨q, ⟨hq, hp⟩, rfl⟩

/-- Both volumes in a local slab bound acquire the same Jacobian. -/
lemma slabBound_affine_image (f : Space ≃ᵃ[ℝ] Space) (J : ℝ)
    (hvol : ∀ W : Set Space, volume (f '' W) = ENNReal.ofReal J * volume W)
    {D : Set Space} {L : ℝ} {n : ℕ} {P : Fin n → Prop} {U : Fin n → Set Space}
    (h : SlabBound D L P U) :
    SlabBound (f '' D) L P (fun i => f '' U i) := by
  intro u t r hu hr
  obtain ⟨v, t', r', hv, hr', heq⟩ := affine_preimage_slab f hu t hr
  have hc : {i | P i ∧ f '' U i ⊆ f '' D ∩ slab u t r} =
      {i | P i ∧ U i ⊆ D ∩ slab v t' r'} := by
    ext i
    simp only [mem_ofPred_eq]
    refine and_congr_right fun _ => ?_
    rw [← heq, ← image_inter_preimage f D (slab u t r)]
    exact Set.image_subset_image_iff f.injective
  have hs := h v t' r' hv hr'
  have hV : volume (f '' D ∩ slab u t r) =
      ENNReal.ofReal J * volume (D ∩ slab v t' r') := by
    rw [← image_inter_preimage, hvol, heq]
  rw [hc, hvol, hV]
  simpa only [mul_left_comm] using mul_le_mul_right hs (ENNReal.ofReal J)

/-- Enlarging image tubes and the containing body gives an unnormalized slab count. -/
lemma slab_count_of_bound {D B : Set Space} {L d : ℝ} {n m : ℕ}
    (hd : 0 < d) (hD : ENNReal.ofReal d ≤ volume D) (hDB : D ⊆ B)
    {U : Fin n → Set Space} {V : Fin m → Set Space}
    (j : Fin m → Fin n) (hj : Function.Injective j)
    (hU : ∀ i, U i ⊆ D) (hUV : ∀ i, U (j i) ⊆ V i)
    (h : SlabBound D L (fun _ => True) U) :
    ∀ u t r, ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal ({i | V i ⊆ B ∩ slab u t r}.ncard : ℝ) ≤
        ENNReal.ofReal (L * n / d) * volume (B ∩ slab u t r) := by
  intro u t r hu hr
  have hc : {i | V i ⊆ B ∩ slab u t r}.ncard ≤
      {i | U i ⊆ D ∩ slab u t r}.ncard := by
    refine (Set.ncard_mono (b := {i | U (j i) ⊆ D ∩ slab u t r}) ?_).trans
      (count_subfamily j hj (fun i => U i ⊆ D ∩ slab u t r))
    intro i hi p hp
    exact ⟨hU (j i) hp, (hi (hUV i hp)).2⟩
  have hs := h u t r hu hr
  simp only [true_and, ofPred_true, ncard_univ, Nat.card_fin] at hs
  have hmain : ENNReal.ofReal ({i | V i ⊆ B ∩ slab u t r}.ncard : ℝ) *
      ENNReal.ofReal d ≤ ENNReal.ofReal (L * n) * volume (B ∩ slab u t r) := by
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hc)) hD).trans
      (hs.trans (mul_le_mul_right (measure_mono (Set.inter_subset_inter_left _ hDB)) _))
  have hd0 : ENNReal.ofReal d ≠ 0 := (ENNReal.ofReal_pos.mpr hd).ne'
  calc
    _ = (ENNReal.ofReal ({i | V i ⊆ B ∩ slab u t r}.ncard : ℝ) *
        ENNReal.ofReal d) * (ENNReal.ofReal d)⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hd0 ENNReal.ofReal_ne_top, mul_one]
    _ ≤ (ENNReal.ofReal (L * n) * volume (B ∩ slab u t r)) *
        (ENNReal.ofReal d)⁻¹ := mul_le_mul_left hmain _
    _ = _ := by
      rw [mul_right_comm, ← ENNReal.ofReal_inv_of_pos hd,
        ← ENNReal.ofReal_mul' (inv_nonneg.mpr hd.le), div_eq_mul_inv]

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
