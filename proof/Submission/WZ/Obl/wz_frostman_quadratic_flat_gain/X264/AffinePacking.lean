-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.AffinePacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Basic
import Submission.WZ.Obl.wz_convex_container_tube_packing.Packing
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file AffinePacking.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set

/-- The accepted packing bound also applies to a containment subfamily. -/
lemma tube_count_packing {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space)
    {U : Set Space} (hU : volume U ≠ ⊤) (hv : ∀ i, ‖v i‖ = 1)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) :
    ENNReal.ofReal ((Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) * δ ^ 4) ≤
      ENNReal.ofReal 1000000 * (volume U) ^ 2 := by
  classical
  let S := {i | tube δ (x i) (v i) ⊆ U}
  let g : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have h := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hδ
    (fun i => x (g i)) (fun i => v (g i)) hU
    (fun i => hv (g i)) (fun i => (g i).property)
    (fun i j hij => hover (g i) (g j) (by
      intro he
      exact hij (g.injective (Subtype.ext he))))
  simpa only [Set.fintypeCard_eq_ncard, S] using h

/-- Packing survives an affine normalization, with the exact volume factor. -/
lemma affine_tube_count {δ J V : ℝ} (hδ : 0 < δ) (hJ : 0 < J) (hV : 0 ≤ V)
    (f : Space ≃ᵃ[ℝ] Space)
    (hf : ∀ U : Set Space, volume (f '' U) = ENNReal.ofReal J * volume U)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i)))
    {U : Set Space} (hU : volume U ≤ ENNReal.ofReal V) :
    (Set.ncard {i | f '' tube δ (x i) (v i) ⊆ U} : ℝ) ≤
      1000000 * (V / (J * δ ^ 2)) ^ 2 := by
  have hpre : volume (f ⁻¹' U) ≤ ENNReal.ofReal (V / J) := by
    apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hJ).ne'
      ENNReal.ofReal_ne_top).mp
    have he := hf (f ⁻¹' U)
    rw [Set.image_preimage_eq _ f.surjective] at he
    rw [← he, ← ENNReal.ofReal_mul hJ.le]
    simpa only [mul_div_cancel₀ V hJ.ne'] using hU
  have heq : {i | f '' tube δ (x i) (v i) ⊆ U} =
      {i | tube δ (x i) (v i) ⊆ f ⁻¹' U} := by
    ext i
    exact Set.image_subset_iff
  rw [heq]
  have hc := tube_count_packing hδ x v (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpre) hv hover
  have hbound : ENNReal.ofReal
      ((Set.ncard {i | tube δ (x i) (v i) ⊆ f ⁻¹' U} : ℝ) * δ ^ 4) ≤
      ENNReal.ofReal (1000000 * (V / J) ^ 2) := by
    calc
      _ ≤ _ := hc
      _ ≤ ENNReal.ofReal 1000000 * (ENNReal.ofReal (V / J)) ^ 2 := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 1000000 * (V / J) ^ 2)).mp hbound
  apply (mul_le_mul_iff_left₀ (pow_pos hδ 4)).mp
  calc
    _ ≤ 1000000 * (V / J) ^ 2 := hreal
    _ = (1000000 * (V / (J * δ ^ 2)) ^ 2) * δ ^ 4 := by field_simp <;> ring

/-- The global quadratic convex-count input survives affine maps, including containers
of infinite volume. No convexity of the test container is needed. -/
lemma affine_quadratic_count {δ J : ℝ} (hδ : 0 < δ) (hJ : 0 < J)
    (f : Space ≃ᵃ[ℝ] Space)
    (hf : ∀ U : Set Space, volume (f '' U) = ENNReal.ofReal J * volume U)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) (U : Set Space) :
    ENNReal.ofReal (Set.ncard {i | f '' tube δ (x i) (v i) ⊆ U} : ℝ) *
      ENNReal.ofReal ((J * δ ^ 2) ^ 2) ≤ ENNReal.ofReal 1000000 * (volume U) ^ 2 := by
  by_cases hU : volume U = ⊤
  · simp [hU]
  have h := affine_tube_count hδ hJ ENNReal.toReal_nonneg f hf x v hv hover
    (U := U) (le_of_eq (ENNReal.ofReal_toReal hU).symm)
  have hc := mul_le_mul_of_nonneg_right h (sq_nonneg (J * δ ^ 2))
  have hr : (Set.ncard {i | f '' tube δ (x i) (v i) ⊆ U} : ℝ) * (J * δ ^ 2) ^ 2 ≤
      1000000 * (volume U).toReal ^ 2 := by
    convert hc using 1
    field_simp
  calc
    _ = ENNReal.ofReal ((Set.ncard {i | f '' tube δ (x i) (v i) ⊆ U} : ℝ) *
        (J * δ ^ 2) ^ 2) := (ENNReal.ofReal_mul (Nat.cast_nonneg _)).symm
    _ ≤ ENNReal.ofReal (1000000 * (volume U).toReal ^ 2) := ENNReal.ofReal_le_ofReal hr
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hU]

/-- A volume bound of order `r t`, and the correct Jacobian normalization, give
quadratic growth of the number of affine tubes in an intermediate container. -/
lemma affine_tube_concentration {δ J C r s t : ℝ} (hδ : 0 < δ) (hJ : 0 < J)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hs : 0 < s) (ht : 0 < t)
    (hscale : s * t ≤ J * δ ^ 2) (f : Space ≃ᵃ[ℝ] Space)
    (hf : ∀ U : Set Space, volume (f '' U) = ENNReal.ofReal J * volume U)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i)))
    {U : Set Space} (hU : volume U ≤ ENNReal.ofReal (C * r * t)) :
    (Set.ncard {i | f '' tube δ (x i) (v i) ⊆ U} : ℝ) ≤
      (1000000 * C ^ 2) * (r / s) ^ 2 := by
  have hratio : C * r * t / (J * δ ^ 2) ≤ C * (r / s) := by
    calc
      _ ≤ C * r * t / (s * t) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hscale
      _ = _ := by field_simp
  calc
    _ ≤ 1000000 * (C * r * t / (J * δ ^ 2)) ^ 2 :=
      affine_tube_count hδ hJ (by positivity) f hf x v hv hover hU
    _ ≤ 1000000 * (C * (r / s)) ^ 2 := by gcongr
    _ = _ := by ring

/-- Affine maps with a fixed volume factor preserve relative overlap bounds. -/
lemma affine_overlap (f : Space ≃ᵃ[ℝ] Space) (J q : ENNReal)
    (hf : ∀ U : Set Space, volume (f '' U) = J * volume U)
    {S T : Set Space} (h : volume (S ∩ T) ≤ q * volume S) :
    volume (f '' S ∩ f '' T) ≤ q * volume (f '' S) := by
  rw [← Set.image_inter f.injective, hf, hf]
  simpa only [mul_left_comm] using mul_le_mul' (le_refl J) h

/-- Normalized Frostman counts are affine invariant. -/
lemma affine_frostman_count {n : ℕ} (T : Fin n → Set Space) (P : Set Space)
    (f : Space ≃ᵃ[ℝ] Space) (J D : ENNReal)
    (hf : ∀ U : Set Space, volume (f '' U) = J * volume U)
    (hcount : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {i | T i ⊆ U} : ℝ) * volume P ≤ D * volume U)
    (U : Set Space) (hU : Convex ℝ U) :
    ENNReal.ofReal (Set.ncard {i | f '' T i ⊆ U} : ℝ) * volume (f '' P) ≤ D * volume U := by
  have hc := hcount (f ⁻¹' U) (hU.affine_preimage f.toAffineMap)
  have heq : {i | f '' T i ⊆ U} = {i | T i ⊆ f ⁻¹' U} := by
    ext i
    exact Set.image_subset_iff
  rw [heq, hf]
  have hv := hf (f ⁻¹' U)
  rw [Set.image_preimage_eq _ f.surjective] at hv
  rw [hv]
  simpa only [mul_assoc, mul_left_comm] using mul_le_mul' (le_refl J) hc

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
