-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaledLocalPlanar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaledBroadness
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleEllipsoid
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalPlanar
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorRetention

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open wz_extremal_lipschitz_grains wz_affine_robust_cluster_estimate

set_option maxHeartbeats 1200000 in
/-- Local planar refinement in a coarse tube, with relative angular
broadness and ellipsoidal localization. All power errors are measured at
the normalized fine scale delta/(100 rho). -/
theorem rescaled_local_planar {ε β D : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hD : 0 < D) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ ρ r : ℝ, 0 < δ → ∀ hρ : 0 < ρ, ρ ≤ 1 → δ ≤ ρ * r → r ≤ 1 →
      let δ' := δ / (100 * ρ)
      δ' ≤ 1 / 100 → δ' ≤ d →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (y w p₀ : Space)
        (e : Space ≃ₗᵢ[ℝ] Space), e w = axis →
      let F := rescaleMap e y w (by norm_num : (0 : ℝ) < 1 / 100) hρ
      0 < n → (n : ℝ) ≤ δ' ^ (-D) → ‖w‖ = 1 → (∀ i, ‖v i‖ = 1) →
      (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ Tube δ (x i) (v i) ∩ F ⁻¹' Metric.ball (F p₀) (r / 100)) →
      (∀ i, Tube δ (x i) (v i) ⊆ Tube ρ y w) →
      ENNReal.ofReal (δ' ^ η * (n : ℝ) * δ ^ 2 * r) ≤ ∑ i, volume (Y i) →
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ' ^ (-η) * δ * ρ * r ^ 2) →
      (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
        ({i | p ∈ Y i ∧ pd (v i) u ≤ s}.ncard : ℝ) ≤
          (δ' ^ (-η) * (s / ρ) ^ β) * incidence Y p) →
      ∃ (u : Space) (t M : ℝ) (Z : Fin n → Set Space), ‖u‖ = 1 ∧ 0 < M ∧
        (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
        (∀ i, (Z i).Nonempty → Tube δ (x i) (v i) ∩
          F ⁻¹' Metric.ball (F p₀) (r / 100) ⊆ {p | |inner ℝ u p - t| ≤ 20 * δ}) ∧
        (∀ i, (Z i).Nonempty → |inner ℝ u (v i)| ≤ 2 * δ / r) ∧
        ENNReal.ofReal (δ' ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
        ENNReal.ofReal (δ' ^ ε * δ * ρ * r ^ 2) ≤ volume (⋃ i, Z i) ∧
        (∀ p ∈ ⋃ i, Z i, M ≤ incidence Z p ∧ incidence Z p ≤ 2 * M) := by
  obtain ⟨η₀, hη₀, hη₀1, d₀, hd₀, hlocal⟩ := local_planar_uniform hε hβ hD
  let η := η₀ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηη₀ : η ≤ η₀ := by dsimp [η]; linarith
  obtain ⟨d₁, hd₁, hconstant⟩ := fixed_constant_power_bound
    (by positivity : (0 : ℝ) < (100 : ℝ) ^ β) hη
  refine ⟨η, hη, hηη₀.trans hη₀1, min d₀ d₁, lt_min hd₀ hd₁, ?_⟩
  intro δ ρ r hδ hρ hρ1 hδρr hr1 δ' hδ'100 hδ'd n x v Y y w p₀ e hew F
    hn hnD hw hv hY hYT hcover hdense hvol hbroad
  have hr : 0 < r := by nlinarith
  have hδ' : 0 < δ' := by dsimp [δ']; positivity
  have hδ'1 : δ' ≤ 1 := by linarith
  have hδ'r : δ' ≤ r / 100 := by
    dsimp [δ']
    apply (div_le_iff₀ (by positivity : 0 < 100 * ρ)).mpr
    nlinarith
  let J : ℝ := (1 / 100 : ℝ) ^ 3 * (ρ⁻¹) ^ 2
  have hJ : 0 < J := by dsimp [J]; positivity
  let V := fun i => F '' Y i
  let x' := fun i => rescaledBase e y w (by norm_num : (0 : ℝ) < 1 / 100) hρ (x i) (v i)
  let v' := fun i => rescaledDir e ρ (v i)
  have hradius : (1 / 100 : ℝ) * ρ⁻¹ * δ = δ' := by dsimp [δ']; ring
  have hvw (i : Fin n) : pd (v i) w < 4 * ρ :=
    pd_lt_of_tube_subset hδ (hv i) hw (hcover i)
  have hV (i : Fin n) : MeasurableSet (V i) :=
    F.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hY i)
  have hVT (i : Fin n) : V i ⊆ Tube δ' (x' i) (v' i) ∩ Metric.ball (F p₀) (r / 100) := by
    rintro p ⟨q, hq, rfl⟩
    refine ⟨?_, (hYT i hq).2⟩
    have hh := rescale_image_tube_subset e hew (by norm_num : (0 : ℝ) < 1 / 100)
      (by norm_num : (1 / 100 : ℝ) * 5 ≤ 1) hρ hρ1 (hv i) (hvw i)
      (mem_image_of_mem F (hYT i hq).1)
    simpa only [hradius] using hh
  have hVsum : (∑ i, volume (V i)) = ENNReal.ofReal J * ∑ i, volume (Y i) := by
    simp only [V, F, rescaleMap_volume, Finset.mul_sum, J]
  have hVunion : volume (⋃ i, V i) = ENNReal.ofReal J * volume (⋃ i, Y i) := by
    dsimp only [V, F]
    rw [← image_iUnion, rescaleMap_volume]
  have hpospow : δ' ^ η₀ ≤ δ' ^ η := Real.rpow_le_rpow_of_exponent_ge hδ' hδ'1 hηη₀
  have hnegpow : δ' ^ (-η) ≤ δ' ^ (-η₀) :=
    Real.rpow_le_rpow_of_exponent_ge hδ' hδ'1 (neg_le_neg hηη₀)
  have hgeom : J * (δ ^ 2 * r) = δ' ^ 2 * (r / 100) := by
    dsimp [J, δ']
    field_simp
  have hgeomvol : J * (δ * ρ * r ^ 2) = δ' * (r / 100) ^ 2 := by
    dsimp [J, δ']
    field_simp
  have hdenseV : ENNReal.ofReal (δ' ^ η₀ * (n : ℝ) * δ' ^ 2 * (r / 100)) ≤
      ∑ i, volume (V i) := by
    rw [hVsum]
    calc
      _ ≤ ENNReal.ofReal (J * (δ' ^ η * (n : ℝ) * δ ^ 2 * r)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ δ' ^ η * (n : ℝ) * δ' ^ 2 * (r / 100) := by gcongr
          _ = (δ' ^ η * (n : ℝ)) * (δ' ^ 2 * (r / 100)) := by ring
          _ = (δ' ^ η * (n : ℝ)) * (J * (δ ^ 2 * r)) := by rw [hgeom]
          _ = _ := by ring
      _ = ENNReal.ofReal J * ENNReal.ofReal (δ' ^ η * (n : ℝ) * δ ^ 2 * r) :=
        ENNReal.ofReal_mul hJ.le
      _ ≤ _ := mul_le_mul_right hdense _
  have hvolV : volume (⋃ i, V i) ≤ ENNReal.ofReal (δ' ^ (1 - η₀) * (r / 100) ^ 2) := by
    rw [hVunion]
    calc
      _ ≤ ENNReal.ofReal J * ENNReal.ofReal (δ' ^ (-η) * δ * ρ * r ^ 2) :=
        mul_le_mul_right hvol _
      _ = ENNReal.ofReal (δ' ^ (-η) * δ' * (r / 100) ^ 2) := by
        rw [← ENNReal.ofReal_mul hJ.le]
        congr 1
        calc
          _ = δ' ^ (-η) * (J * (δ * ρ * r ^ 2)) := by ring
          _ = _ := by rw [hgeomvol]; ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [sub_eq_add_neg, Real.rpow_add hδ', Real.rpow_one]
        nlinarith [mul_le_mul_of_nonneg_right hnegpow (by positivity : 0 ≤ δ' * (r / 100) ^ 2)]
  have hcapcoef : δ' ^ (-η) * (100 : ℝ) ^ β ≤ δ' ^ (-η₀) := by
    calc
      _ ≤ δ' ^ (-η) * δ' ^ (-η) := mul_le_mul_of_nonneg_left
        (hconstant δ' hδ' (hδ'd.trans (min_le_right _ _))) (Real.rpow_nonneg hδ'.le _)
      _ = _ := by rw [← Real.rpow_add hδ']; congr 1; dsimp [η]; ring
  have hbroadV : ∀ p u s, ‖u‖ = 1 → δ' ≤ s → s ≤ 1 →
      ({i | p ∈ V i ∧ min ‖v' i - u‖ ‖v' i + u‖ ≤ s}.ncard : ℝ) ≤
        (δ' ^ (-η₀) * s ^ β) * incidence V p := by
    intro p u s hu hs hs1
    have hC : 1 ≤ δ' ^ (-η) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ' hδ'1 (by linarith)
    have hh := rescaled_image_relative_cap_bound x v Y y w e hew F.toEquiv hδ hρ hρ1
      hC hβ.le hw (fun i _ => hv i) (fun i _ => hcover i) hbroad p u s hs
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcapcoef (Real.rpow_nonneg (hδ'.le.trans hs) _))
      (incidence_nonneg V p))
  obtain ⟨u', t', M, W, hu', hM, hW, hslab, hnormal, hkeep, hlarge, huniform⟩ :=
    hlocal δ' (r / 100) hδ' hδ'100 (hδ'd.trans (min_le_left _ _)) hδ'r (by linarith)
      n x' v' V (F p₀) hn hnD (fun i => norm_rescaledDir e hρ hρ1 (hv i)) hV hVT
      hdenseV hvolV hbroadV
  let Z := fun i => F ⁻¹' W i
  have hmem (i : Fin n) (p : Space) : F p ∈ V i ↔ p ∈ Y i := by
    constructor
    · rintro ⟨q, hq, heq⟩
      exact F.injective heq ▸ hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  have hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i := by
    intro i
    exact ⟨(hW i).1.preimage F.continuous.measurable,
      fun p hp => (hmem i p).mp ((hW i).2 hp)⟩
  have hZW (i : Fin n) : F '' Z i = W i := image_preimage_eq _ F.surjective
  have hZsum : (∑ i, volume (W i)) = ENNReal.ofReal J * ∑ i, volume (Z i) := by
    simp_rw [← hZW, show F = rescaleMap e y w (by norm_num : (0 : ℝ) < 1 / 100) hρ from rfl,
      rescaleMap_volume, ← Finset.mul_sum]
    rfl
  have hZunion : volume (⋃ i, W i) = ENNReal.ofReal J * volume (⋃ i, Z i) := by
    simp_rw [← hZW]
    rw [← image_iUnion]
    exact rescaleMap_volume e y w (by norm_num : (0 : ℝ) < 1 / 100) hρ _
  have hWne (i : Fin n) (hi : (Z i).Nonempty) : (W i).Nonempty := by
    obtain ⟨p, hp⟩ := hi
    exact ⟨F p, hp⟩
  let u := unit (pullbackNormal e ρ u')
  let t := (t' - inner ℝ u' (F p₀)) / ((1 / 100 : ℝ) * ‖pullbackNormal e ρ u'‖) +
    inner ℝ u p₀
  have hτ : δ' / (25 * (r / 100)) ≤ 1 / 10 := by
    apply (div_le_iff₀ (by positivity : 0 < 25 * (r / 100))).mpr
    linarith
  refine ⟨u, t, M, Z, norm_unit (pullbackNormal_ne_zero e hρ hρ1 hu'), hM, hZ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi p hp
    have hpT : F p ∈ Tube δ' (x' i) (v' i) := by
      have hh := rescale_image_tube_subset e hew (by norm_num : (0 : ℝ) < 1 / 100)
        (by norm_num : (1 / 100 : ℝ) * 5 ≤ 1) hρ hρ1 (hv i) (hvw i)
        (mem_image_of_mem F hp.1)
      simpa only [hradius] using hh
    have hh := rescaled_fine_slab_pullback e hew (by norm_num : (0 : ℝ) < 1 / 100)
      hρ hρ1 hδ.le (hv i) hu' (hvw i) hτ (hnormal i (hWne i hi)) p p₀ t'
      (by simpa only [hradius, F, mem_setOf_eq] using hslab i (hWne i hi) ⟨hpT, hp.2⟩)
    change |inner ℝ u p - t| ≤ 20 * δ
    have he : inner ℝ u p - t = inner ℝ u (p - p₀) -
        (t' - inner ℝ u' (F p₀)) / ((1 / 100 : ℝ) * ‖pullbackNormal e ρ u'‖) := by
      dsimp only [t]
      rw [inner_sub_right]
      ring
    rw [he]
    exact hh
  · intro i hi
    have hh := normalized_pullback_direction e hew hρ hρ1 (hv i) hu' (hvw i) hτ
      (hnormal i (hWne i hi))
    have he : 50 * ρ * (δ' / (25 * (r / 100))) = 2 * δ / r := by
      dsimp [δ']; field_simp; ring
    exact he ▸ hh
  · rw [hVsum, hZsum] at hkeep
    apply (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr hJ)) ENNReal.ofReal_ne_top).mp
    simpa only [mul_left_comm] using hkeep
  · apply (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr hJ)) ENNReal.ofReal_ne_top).mp
    rw [← hZunion, ← ENNReal.ofReal_mul hJ.le]
    have he : J * (δ' ^ ε * δ * ρ * r ^ 2) = δ' ^ (1 + ε) * (r / 100) ^ 2 := by
      calc
        _ = δ' ^ ε * (J * (δ * ρ * r ^ 2)) := by ring
        _ = _ := by rw [hgeomvol, Real.rpow_add hδ', Real.rpow_one]; ring
    rw [he]
    exact hlarge
  · intro p hp
    have hpW : F p ∈ ⋃ i, W i := by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨i, hi⟩
    have hi : incidence W (F p) = incidence Z p := by
      rw [incidence_eq_ncard, incidence_eq_ncard]
      rfl
    simpa only [hi] using huniform (F p) hpW

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
