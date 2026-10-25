-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaledSeparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.SeparatedRelativePower
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaledBroadness

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open wz_extremal_lipschitz_grains wz_affine_robust_cluster_estimate
open scoped Classical

set_option maxHeartbeats 1400000 in
/-- Select separated dense cells in normalized coordinates and transport
all mass and relative-incidence guarantees to the physical shading. -/
theorem rescaled_separated_dense_input_power {η : ℝ} (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ ρ r L : ℝ, 0 < δ → ∀ hρ : 0 < ρ,
      ρ ≤ 1 → δ ≤ ρ * r → 0 ≤ L →
      let ξ := δ / (100 * ρ)
      ξ ≤ 1 → ξ ≤ d →
      ∀ (n N : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space)
        (C : Fin N → Set Space) (q : Fin N → Space) (y w : Space)
        (e : Space ≃ₗᵢ[ℝ] Space), e w = axis →
      let F := rescaleMap e y w (by norm_num : (0 : ℝ) < 1 / 100) hρ
      ‖w‖ = 1 → (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) →
      (∀ i, volume (Y i) ≠ ⊤) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
      (∀ i, (Y i).Nonempty → Tube δ (x i) (v i) ⊆ Tube ρ y w) →
      (∀ j, MeasurableSet (C j)) →
      (∀ j, C j ⊆ F ⁻¹' Metric.ball (F (q j)) (r / 100)) →
      (Pairwise fun j k => Disjoint (C j) (C k)) →
      (⋃ i, Y i) ⊆ ⋃ j, C j →
      (∀ i, ({j | (Y i ∩ C j).Nonempty}.ncard : ℝ) ≤ L) →
      2 * (ξ ^ η * δ ^ 2 * r) * n * L ≤ shadingMass Y →
      ∃ W : Fin n → Set Space,
        (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i) ∧
        ENNReal.ofReal (ξ ^ (3 * η)) * (∑ i, volume (Y i)) ≤ ∑ i, volume (W i) ∧
        (∀ i j k, j ≠ k → (W i ∩ C j).Nonempty → (W i ∩ C k).Nonempty →
          10 * (r / 100) < dist (F (q j)) (F (q k))) ∧
        (∀ i, (⋃ j, W i ∩ C j) = W i) ∧
        (∀ i, ({j | (W i ∩ C j).Nonempty}.ncard : ℝ) ≤ L) ∧
        (∀ j, ENNReal.ofReal (ξ ^ (4 * η) *
          ({i | (W i ∩ C j).Nonempty}.ncard : ℝ) * δ ^ 2 * r) ≤ ∑ i, volume (W i ∩ C j)) ∧
        ∀ p ∈ ⋃ i, W i, ξ ^ (3 * η) * incidence Y p ≤ incidence W p := by
  obtain ⟨d, hd, hseparate⟩ := separated_dense_relative_input_power hη
  refine ⟨d, hd, ?_⟩
  intro δ ρ r L hδ hρ hρ1 hδρr hL ξ hξ1 hξd n N x v Y C q y w e hew F
    hw hv hY hfin hYT hcarrier hC hball hdisj hcover hcross hbudget
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hr : 0 < r := by nlinarith
  have hξr : ξ ≤ r / 100 := by
    dsimp [ξ]
    apply (div_le_iff₀ (by positivity : 0 < 100 * ρ)).mpr
    nlinarith
  let J : ℝ := (1 / 100 : ℝ) ^ 3 * (ρ⁻¹) ^ 2
  have hJ : 0 < J := by dsimp [J]; positivity
  have hJ0 : ENNReal.ofReal J ≠ 0 := (ENNReal.ofReal_pos.mpr hJ).ne'
  have hFvol (A : Set Space) : volume (F '' A) = ENNReal.ofReal J * volume A :=
    rescaleMap_volume e y w (by norm_num : (0 : ℝ) < 1 / 100) hρ A
  have hFsum (U : Fin n → Set Space) :
      (∑ i, volume (F '' U i)) = ENNReal.ofReal J * ∑ i, volume (U i) := by
    simp only [hFvol, Finset.mul_sum]
  have hFmass (U : Fin n → Set Space) : shadingMass (fun i => F '' U i) = J * shadingMass U := by
    simp only [shadingMass, hFvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal hJ.le, Finset.mul_sum]
  have himage_ne (A B : Set Space) : (F '' A ∩ F '' B).Nonempty ↔ (A ∩ B).Nonempty := by
    rw [← image_inter F.injective]
    exact image_nonempty
  let Y' := fun i => F '' Y i
  let C' := fun j => F '' C j
  let x' := fun i => rescaledBase e y w (by norm_num : (0 : ℝ) < 1 / 100) hρ (x i) (v i)
  let v' := fun i => rescaledDir e ρ (v i)
  have hradius : (1 / 100 : ℝ) * ρ⁻¹ * δ = ξ := by dsimp [ξ]; ring
  have hY'T (i : Fin n) : Y' i ⊆ Tube ξ (x' i) (v' i) := by
    rintro p ⟨z, hz, rfl⟩
    have hvw := pd_lt_of_tube_subset hδ (hv i) hw (hcarrier i ⟨z, hz⟩)
    have hh := rescale_image_tube_subset e hew (by norm_num : (0 : ℝ) < 1 / 100)
      (by norm_num : (1 / 100 : ℝ) * 5 ≤ 1) hρ hρ1 (hv i) hvw
      (mem_image_of_mem F (hYT i hz))
    simpa only [hradius] using hh
  have hdisj' : Pairwise fun j k => Disjoint (C' j) (C' k) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    rintro p ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
    have hab : b = a := F.injective he
    exact Set.disjoint_left.mp (hdisj hjk) ha (hab ▸ hb)
  have hcover' : (⋃ i, Y' i) ⊆ ⋃ j, C' j := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    obtain ⟨z, hz, rfl⟩ := hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover (mem_iUnion.mpr ⟨i, hz⟩))
    exact mem_iUnion.mpr ⟨j, mem_image_of_mem F hj⟩
  have hgeom : J * (δ ^ 2 * r) = ξ ^ 2 * (r / 100) := by
    dsimp [J, ξ]
    field_simp
  have hbudget' : 2 * (ξ ^ η * ξ ^ 2 * (r / 100)) * n * L ≤ shadingMass Y' := by
    rw [hFmass]
    calc
      _ = J * (2 * (ξ ^ η * δ ^ 2 * r) * n * L) := by
        calc
          _ = (2 * ξ ^ η * n * L) * (ξ ^ 2 * (r / 100)) := by ring
          _ = _ := by rw [← hgeom]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbudget hJ.le
  obtain ⟨V, hV, hkeep, hsep, hunion, hcrossV, hdense, hrelative⟩ :=
    hseparate ξ (r / 100) L hξ hξ1 hξd hξr hL n N x' v' Y' C' (fun j => F (q j))
      (fun i => norm_rescaledDir e hρ hρ1 (hv i))
      (fun i => F.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hY i))
      (fun i => by rw [hFvol]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin i))
      hY'T (fun j => F.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hC j))
      (fun j p hp => by obtain ⟨z, hz, rfl⟩ := hp; exact hball j hz)
      hdisj' hcover' (fun i => by simpa only [Y', C', himage_ne] using hcross i) hbudget'
  let W := fun i => F ⁻¹' V i
  have hW (i : Fin n) : MeasurableSet (W i) ∧ W i ⊆ Y i := by
    refine ⟨(hV i).1.preimage F.continuous.measurable, ?_⟩
    intro p hp
    obtain ⟨z, hz, he⟩ := (hV i).2 hp
    exact F.injective he ▸ hz
  have hVW (i : Fin n) : V i = F '' W i := (image_preimage_eq _ F.surjective).symm
  have hcell (i : Fin n) (j : Fin N) : V i ∩ C' j = F '' (W i ∩ C j) := by
    rw [hVW, image_inter F.injective]
  have hcellne (i : Fin n) (j : Fin N) : (V i ∩ C' j).Nonempty ↔ (W i ∩ C j).Nonempty := by
    rw [hcell]
    exact image_nonempty
  have hWsum : (∑ i, volume (V i)) = ENNReal.ofReal J * ∑ i, volume (W i) := by
    simp only [hVW, hFsum]
  refine ⟨W, hW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFsum, hWsum] at hkeep
    apply (ENNReal.mul_le_mul_iff_right hJ0 ENNReal.ofReal_ne_top).mp
    simpa only [mul_left_comm] using hkeep
  · intro i j k hjk hj hk
    exact hsep i j k hjk ((hcellne i j).mpr hj) ((hcellne i k).mpr hk)
  · intro i
    rw [← inter_iUnion]
    exact inter_eq_left.mpr (((hW i).2.trans (subset_iUnion Y i)).trans hcover)
  · intro i
    simpa only [hcellne] using hcrossV i
  · intro j
    have hh := hdense j
    simp only [hcell, Set.image_nonempty, hFvol, ← Finset.mul_sum] at hh
    apply (ENNReal.mul_le_mul_iff_right hJ0 ENNReal.ofReal_ne_top).mp
    rw [← ENNReal.ofReal_mul hJ.le]
    have he : J * (ξ ^ (4 * η) * ({i | (W i ∩ C j).Nonempty}.ncard : ℝ) * δ ^ 2 * r) =
        ξ ^ (4 * η) * ({i | (W i ∩ C j).Nonempty}.ncard : ℝ) * ξ ^ 2 * (r / 100) := by
      calc
        _ = (ξ ^ (4 * η) * ({i | (W i ∩ C j).Nonempty}.ncard : ℝ)) * (J * (δ ^ 2 * r)) := by ring
        _ = _ := by rw [hgeom]; ring
    rw [he]
    exact hh
  · intro p hp
    have hpV : F p ∈ ⋃ i, V i := by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨i, hi⟩
    have hincV : incidence V (F p) = incidence W p := by
      rw [incidence_eq_ncard, incidence_eq_ncard]
      rfl
    have hincY : incidence Y' (F p) = incidence Y p := by
      rw [incidence_eq_ncard, incidence_eq_ncard]
      congr 2
      ext i
      simp only [Y', mem_setOf_eq, mem_image, F.injective.eq_iff, exists_eq_right]
    simpa only [hincV, hincY] using hrelative (F p) hpV

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
