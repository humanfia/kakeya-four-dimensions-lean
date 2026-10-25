-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LocalPlanar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalNormalize
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PlanarUniform

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

set_option maxHeartbeats 800000 in
/-- Planar refinement inside a ball, with all losses measured at the original
fine scale. The containing slab has thickness comparable to the fine tubes. -/
theorem local_planar_uniform {ε β D : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hD : 0 < D) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ r : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d → δ ≤ r → r ≤ 1 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (c : Space),
        0 < n → (n : ℝ) ≤ δ ^ (-D) → (∀ i, ‖v i‖ = 1) →
        (∀ i, MeasurableSet (Y i)) →
        (∀ i, Y i ⊆ Tube δ (x i) (v i) ∩ Metric.ball c r) →
        ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2 * r) ≤ ∑ i, volume (Y i) →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (1 - η) * r ^ 2) →
        (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ 1 →
          ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s}.ncard : ℝ) ≤
            (δ ^ (-η) * s ^ β) * incidence Y p) →
        ∃ (e : Space) (t M : ℝ) (Z : Fin n → Set Space), ‖e‖ = 1 ∧ 0 < M ∧
          (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
          (∀ i, (Z i).Nonempty →
            Tube δ (x i) (v i) ∩ Metric.ball c r ⊆ {p | |inner ℝ e p - t| ≤ 2 * δ}) ∧
          (∀ i, (Z i).Nonempty → |inner ℝ e (v i)| ≤ δ / (25 * r)) ∧
          ENNReal.ofReal (δ ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
          ENNReal.ofReal (δ ^ (1 + ε) * r ^ 2) ≤ volume (⋃ i, Z i) ∧
          (∀ p ∈ ⋃ i, Z i, M ≤ incidence Z p ∧ incidence Z p ≤ 2 * M) := by
  obtain ⟨η₀, hη₀, hη₀1, d₀, hd₀, hplanar⟩ := planar_uniform_two_scales hε hβ hD
  let η := η₀ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηη₀ : η ≤ η₀ := by dsimp [η]; linarith
  obtain ⟨d₁, hd₁, hcut⟩ := exists_power_cutoff hη (c := 1 / 100) (by norm_num)
  refine ⟨η, hη, hηη₀.trans hη₀1, min d₀ d₁, lt_min hd₀ hd₁, ?_⟩
  intro δ r hδ hδ100 hδd hδr hr1 n x v Y c hn hnD hv hY hYT hdense hvol hbroad
  have hr : 0 < r := hδ.trans_le hδr
  have hδ1 : δ ≤ 1 := by linarith
  let a := (100 * r)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  let ρ := δ / (100 * r)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ100 : ρ ≤ 1 / 100 := by
    dsimp [ρ]
    exact (div_le_iff₀ (by positivity : 0 < 100 * r)).mpr (by linarith)
  have hδρ : δ / 100 ≤ ρ := by
    dsimp [ρ]
    apply (le_div_iff₀ (by positivity : 0 < 100 * r)).mpr
    nlinarith
  let F := localMap hr c
  let V := fun i => F '' Y i
  choose z hzball hzY hzlocal using
    fun i => local_shading_carrier hr hδr (x i) (v i) c (hv i) (Y i) (hYT i)
  have hV : ∀ i, MeasurableSet (V i) := fun i => localMap_measurableSet hr c (hY i)
  have hmem (i : Fin n) (p : Space) : F p ∈ V i ↔ p ∈ Y i := by
    constructor
    · rintro ⟨q, hq, hqp⟩
      exact F.injective hqp ▸ hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  have hVsum : (∑ i, volume (V i)) = ENNReal.ofReal (a ^ 3) * ∑ i, volume (Y i) := by
    simp only [V, F, localMap_volume, Finset.mul_sum, a]
  have hVunion : volume (⋃ i, V i) = ENNReal.ofReal (a ^ 3) * volume (⋃ i, Y i) := by
    dsimp only [V, F]
    rw [← image_iUnion, localMap_volume]
  have hpow : δ ^ η₀ ≤ δ ^ η / 100 := by
    have hc := hcut δ hδ (hδd.trans (min_le_right _ _))
    have he : δ ^ η₀ = δ ^ η * δ ^ η := by
      rw [← Real.rpow_add hδ]
      congr 1
      dsimp [η]
      ring
    rw [he]
    nlinarith [Real.rpow_pos_of_pos hδ η]
  have hnegative : δ ^ (-η) ≤ δ ^ (-η₀) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηη₀)
  have hdensity : ENNReal.ofReal (δ ^ η₀ * (n : ℝ) * ρ ^ 2) ≤ ∑ i, volume (V i) := by
    rw [hVsum]
    calc
      _ ≤ ENNReal.ofReal (a ^ 3 * (δ ^ η * (n : ℝ) * δ ^ 2 * r)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ (δ ^ η / 100) * (n : ℝ) * ρ ^ 2 := by gcongr
          _ = _ := by dsimp [a, ρ]; field_simp
      _ = ENNReal.ofReal (a ^ 3) * ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2 * r) :=
        ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := mul_le_mul_right hdense _
  have hvolume : volume (⋃ i, V i) ≤ ENNReal.ofReal (δ ^ (-η₀) * ρ) := by
    rw [hVunion]
    calc
      _ ≤ ENNReal.ofReal (a ^ 3) * ENNReal.ofReal (δ ^ (1 - η) * r ^ 2) :=
        mul_le_mul_right hvol _
      _ = ENNReal.ofReal (a ^ 3 * (δ ^ (1 - η) * r ^ 2)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have he : a ^ 3 * (δ ^ (1 - η) * r ^ 2) = δ ^ (-η) * ρ / 10000 := by
          rw [show (1 : ℝ) - η = 1 + (-η) by ring, Real.rpow_add hδ, Real.rpow_one]
          dsimp [a, ρ]
          field_simp
          ring
        rw [he]
        have hh := mul_le_mul_of_nonneg_right hnegative hρ.le
        have hh0 : 0 ≤ δ ^ (-η) * ρ := by positivity
        linarith
  have hbroadV : ∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ 1 →
      ({i | p ∈ V i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s}.ncard : ℝ) ≤
        (δ ^ (-η₀) * s ^ β) * incidence V p := by
    intro q u s hu hs hs1
    obtain ⟨p, rfl⟩ := F.surjective q
    have he : {i | F p ∈ V i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s} =
        {i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s} := by
      ext i
      rw [mem_setOf_eq, mem_setOf_eq, hmem]
    have hi : incidence V (F p) = incidence Y p := localMap_incidence hr c Y p
    rw [he, hi]
    exact (hbroad p u s hu hs hs1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hnegative (Real.rpow_nonneg (hδ.le.trans hs) β))
      (incidence_nonneg Y p))
  obtain ⟨e, t, M, W, he, hM, hW, hslab, hkeep, hlarge, huniform⟩ :=
    hplanar δ ρ hδ hδ100 (hδd.trans (min_le_left _ _)) hδρ hρ100 n z v V hn hnD hv
      hzball hV hzY hdensity hvolume hbroadV
  let Z := fun i => F ⁻¹' W i
  have hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i := by
    intro i
    refine ⟨(hW i).1.preimage F.continuous.measurable, ?_⟩
    intro p hp
    exact (hmem i p).mp ((hW i).2 hp)
  have hZW : ∀ i, F '' Z i = W i := fun i => image_preimage_eq _ F.surjective
  have hZsum : (∑ i, volume (W i)) = ENNReal.ofReal (a ^ 3) * ∑ i, volume (Z i) := by
    simp_rw [← hZW, show F = localMap hr c from rfl, localMap_volume, ← Finset.mul_sum]
    rfl
  have hZunion : volume (⋃ i, W i) = ENNReal.ofReal (a ^ 3) * volume (⋃ i, Z i) := by
    simp_rw [← hZW]
    rw [← image_iUnion]
    exact localMap_volume hr c _
  have hWne (i : Fin n) (hi : (Z i).Nonempty) : (W i).Nonempty := by
    obtain ⟨p, hp⟩ := hi
    exact ⟨F p, hp⟩
  refine ⟨e, inner ℝ e c + 100 * r * t, M, Z, he, hM, hZ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi p hp
    have hpV := hzlocal i (hi.mono (hZ i).2) (mem_image_of_mem F hp)
    have hh := hslab i (hWne i hi) hpV
    change |inner ℝ e (localMap hr c p) - t| ≤ 2 * ρ at hh
    have heq : inner ℝ e (localMap hr c p) - t =
        a * (inner ℝ e p - (inner ℝ e c + 100 * r * t)) := by
      rw [localMap_apply, inner_smul_right, inner_sub_right]
      dsimp [a]
      field_simp
      ring
    rw [heq, abs_mul, abs_of_pos ha] at hh
    have hb : a * (2 * δ) = 2 * ρ := by dsimp [a, ρ]; ring
    rw [← hb] at hh
    exact (mul_le_mul_iff_right₀ ha).mp hh
  · intro i hi
    have hx : z i ∈ Tube ρ (z i) (v i) :=
      Metric.self_subset_thickening hρ _ (left_mem_segment ℝ (z i) (z i + v i))
    have hxv : z i + v i ∈ Tube ρ (z i) (v i) :=
      Metric.self_subset_thickening hρ _ (right_mem_segment ℝ (z i) (z i + v i))
    have h₀ := hslab i (hWne i hi) hx
    have h₁ := hslab i (hWne i hi) hxv
    change |inner ℝ e (z i) - t| ≤ 2 * ρ at h₀
    change |inner ℝ e (z i + v i) - t| ≤ 2 * ρ at h₁
    have hh : |inner ℝ e (v i)| ≤ 4 * ρ := by
      calc
        _ = |(inner ℝ e (z i + v i) - t) - (inner ℝ e (z i) - t)| := by
          rw [inner_add_right]
          congr 1
          ring
        _ ≤ |inner ℝ e (z i + v i) - t| + |inner ℝ e (z i) - t| := abs_sub _ _
        _ ≤ _ := by linarith
    have hfour : 4 * ρ = δ / (25 * r) := by dsimp [ρ]; ring
    exact hfour ▸ hh
  · rw [hVsum, hZsum] at hkeep
    apply (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity : 0 < a ^ 3)))
      ENNReal.ofReal_ne_top).mp
    simpa only [mul_left_comm] using hkeep
  · apply (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity : 0 < a ^ 3)))
      ENNReal.ofReal_ne_top).mp
    rw [← hZunion, ← ENNReal.ofReal_mul (by positivity : 0 ≤ a ^ 3)]
    apply (ENNReal.ofReal_le_ofReal ?_).trans hlarge
    rw [Real.rpow_add hδ, Real.rpow_one]
    have heq : a ^ 3 * (δ * δ ^ ε * r ^ 2) = δ ^ ε * ρ / 10000 := by
      dsimp [a, ρ]
      field_simp
      ring
    rw [heq]
    have hh : 0 ≤ δ ^ ε * ρ := by positivity
    linarith
  · intro p hp
    have hpW : F p ∈ ⋃ i, W i := by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨i, hi⟩
    have hi : incidence W (F p) = incidence Z p := by
      rw [incidence_eq_ncard, incidence_eq_ncard]
      rfl
    simpa only [hi] using huniform (F p) hpW

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
