-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyTransport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyCounts
import Submission.WZ.Obl.wz_nonflat_factored_improvement.AffineCounts
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Packets

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (closedTube tube_subset_closedTube)
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (affine_volume_preimage packetIndex packetIndex_injective packetIndex_contained packetSize_eq)

theorem BodyConvexCount.mono_m {n : ℕ} {U : Fin n → Set Space} {w m M : ℝ}
    (h : BodyConvexCount U w m) (hm : m ≤ M) : BodyConvexCount U w M := by
  intro Q hQ
  exact (h Q hQ).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hm) le_rfl)

theorem BodyConvexCount.affine_image {n : ℕ} {U : Fin n → Set Space} {w m J : ℝ}
    (hw : 0 ≤ w) (hJ : 0 < J) (f : Space ≃ᵃ[ℝ] Space)
    (hvol : ∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q)
    (h : BodyConvexCount U w m) : BodyConvexCount (fun i => f '' U i) (J * w) m := by
  intro Q hQ
  have he : {i | f '' U i ⊆ Q} = {i | U i ⊆ f ⁻¹' Q} := by
    ext i; exact image_subset_iff
  rw [he]
  calc
    _ = ENNReal.ofReal J * ENNReal.ofReal ((Set.ncard {i | U i ⊆ f ⁻¹' Q} : ℝ) * w) := by
      rw [← ENNReal.ofReal_mul hJ.le]; congr 1; ring
    _ ≤ ENNReal.ofReal J * (ENNReal.ofReal m * volume (f ⁻¹' Q)) :=
      mul_le_mul' le_rfl (h _ (hQ.affine_preimage f.toAffineMap))
    _ = _ := by
      rw [affine_volume_preimage f hJ hvol]
      calc
        _ = ENNReal.ofReal m * ((ENNReal.ofReal J * ENNReal.ofReal J⁻¹) * volume Q) := by ring
        _ = _ := by rw [← ENNReal.ofReal_mul hJ.le, mul_inv_cancel₀ hJ.ne', ENNReal.ofReal_one, one_mul]

theorem BodyPacking.affine_image {n : ℕ} {U : Fin n → Set Space} {w P J : ℝ}
    (hw : 0 ≤ w) (hJ : 0 < J) (f : Space ≃ᵃ[ℝ] Space)
    (hvol : ∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q)
    (h : BodyPacking U w P) : BodyPacking (fun i => f '' U i) (J * w) P := by
  intro Q hQ
  have he : {i | f '' U i ⊆ Q} = {i | U i ⊆ f ⁻¹' Q} := by
    ext i; exact image_subset_iff
  rw [he]
  calc
    _ = ENNReal.ofReal J * ENNReal.ofReal (Real.sqrt (Set.ncard {i | U i ⊆ f ⁻¹' Q} : ℝ) * w) := by
      rw [← ENNReal.ofReal_mul hJ.le]; congr 1; ring
    _ ≤ ENNReal.ofReal J * (ENNReal.ofReal P * volume (f ⁻¹' Q)) :=
      mul_le_mul' le_rfl (h _ (hQ.affine_preimage f.toAffineMap))
    _ = _ := by
      rw [affine_volume_preimage f hJ hvol]
      calc
        _ = ENNReal.ofReal P * ((ENNReal.ofReal J * ENNReal.ofReal J⁻¹) * volume Q) := by ring
        _ = _ := by rw [← ENNReal.ofReal_mul hJ.le, mul_inv_cancel₀ hJ.ne', ENNReal.ofReal_one, one_mul]

theorem body_slab_of_convex_count {n : ℕ} (hn : 0 < n) {U : Fin n → Set Space}
    {w m : ℝ} (hw : 0 < w) (hm : 0 ≤ m) (hball : ∀ i, U i ⊆ ball (0 : Space) 1)
    (hc : BodyConvexCount U w m) : BodySlabCount U (8 * m / (w * n)) := by
  intro ν s r hν hr
  have he : {i | U i ⊆ {p | |inner ℝ ν p - s| ≤ r}} =
      {i | U i ⊆ ball (0 : Space) 1 ∩ {p | |inner ℝ ν p - s| ≤ r}} := by
    ext i; exact ⟨fun h p hp => ⟨hball i hp, h hp⟩, fun h => h.trans inter_subset_right⟩
  rw [he]
  have hh := hc _ (WangZahlLot.Obl.wz_nonflat_factored_improvement.slab_convex ν s r)
  have hv := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.slab_volume_le hν s r hr.le
  have h := hh.trans (mul_le_mul' le_rfl hv)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ = ENNReal.ofReal w⁻¹ * ENNReal.ofReal
        ((Set.ncard {i | U i ⊆ ball (0 : Space) 1 ∩ {p | |inner ℝ ν p - s| ≤ r}} : ℝ) * w) := by
      rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
    _ ≤ ENNReal.ofReal w⁻¹ * (ENNReal.ofReal m * ENNReal.ofReal (8 * r)) := mul_le_mul' le_rfl h
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

theorem closedTube_convex_count {δ K : ℝ} (hK : 0 ≤ K) {n : ℕ} (x v : Fin n → Space)
    (hc : ∀ Q : Set Space, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) ≤ ENNReal.ofReal K * volume Q) :
    BodyConvexCount (fun i => closedTube δ (x i) (v i)) (δ ^ 2) (K * δ ^ 2) := by
  intro Q hQ
  have hn : Set.ncard {i | closedTube δ (x i) (v i) ⊆ Q} ≤
      Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} :=
    ncard_mono (fun i hi => (tube_subset_closedTube _ _ _).trans hi)
  calc
    _ = ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal (Set.ncard {i | closedTube δ (x i) (v i) ⊆ Q} : ℝ) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg δ)]; congr 1; ring
    _ ≤ ENNReal.ofReal (δ ^ 2) * (ENNReal.ofReal K * volume Q) := by
      apply mul_le_mul' le_rfl
      exact (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hn)).trans (hc Q hQ)
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg δ)]; congr 2; ring

theorem closedTube_packing {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1)
    (hover : ∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) :
    BodyPacking (fun i => closedTube δ (x i) (v i)) (δ ^ 2) 1000 := by
  intro Q _
  by_cases hQ : volume Q = ⊤
  · simp [hQ]
  let g := packetIndex δ x v Q
  have hg := packetIndex_injective δ x v Q
  have hp := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hδ
    (fun i => x (g i)) (fun i => v (g i)) hQ (fun i => hv (g i))
    (packetIndex_contained δ x v Q) (fun i j hij => hover (g i) (g j) (hg.ne hij))
  rw [packetSize_eq] at hp
  have hpr := ENNReal.toReal_mono (by finiteness) hp
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤
    (Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) * δ ^ 4), ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1000000)] at hpr
  have hn : (Set.ncard {i | closedTube δ (x i) (v i) ⊆ Q} : ℝ) ≤
      Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} := by
    exact_mod_cast ncard_mono (fun i hi => (tube_subset_closedTube δ (x i) (v i)).trans hi)
  have hsqrt := Real.sq_sqrt (show 0 ≤ (Set.ncard {i | closedTube δ (x i) (v i) ⊆ Q} : ℝ) by positivity)
  have hh : Real.sqrt (Set.ncard {i | closedTube δ (x i) (v i) ⊆ Q} : ℝ) * δ ^ 2 ≤
      1000 * (volume Q).toReal := by
    have hsq : (Real.sqrt (Set.ncard {i | closedTube δ (x i) (v i) ⊆ Q} : ℝ) * δ ^ 2) ^ 2 ≤
        (1000 * (volume Q).toReal) ^ 2 := by
      rw [mul_pow, hsqrt]
      nlinarith only [hpr, mul_le_mul_of_nonneg_right hn (show 0 ≤ δ ^ 4 by positivity)]
    nlinarith [ENNReal.toReal_nonneg (a := volume Q)]
  rw [← ENNReal.ofReal_toReal hQ, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hh

end WangZahlLot.Obl.wz_flat_factored_improvement
