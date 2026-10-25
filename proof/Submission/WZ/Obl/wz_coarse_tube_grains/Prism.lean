-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.Prism.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaledBoundedPrisms
import Submission.WZ.Obl.wz_coarse_tube_grains.PolyMethod.Rescaled
import Submission.WZ.Obl.wz_coarse_tube_grains.Select

/-!
# Prisms in one thin carrier

The polynomial grains partition of the selected shading inside a thin carrier (x0325's
`grains_partition_tube`, o005, with the Guth lower bound on its scale added here) is fed to
x0310's `rescaled_prism_family_of_bounded_partition` (o019). The lower bound
`8 δ ρ ≤ s |E|` on the partition scale is what makes the prescribed grain length `c` fit
under the partition scale.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_tube_grains

open Set Metric MeasureTheory
open wz_affine_robust_cluster_estimate
open scoped Classical

local notation "V" => LeanEval.Analysis.WangZahlKakeya.Space

/-- The sum of the shading masses as an integral of the multiplicity. -/
theorem sum_volume_eq_lintegral {m : ℕ} {Y : Fin m → Set V} (hY : ∀ i, MeasurableSet (Y i)) :
    ∑ i, volume (Y i) =
      ∫⁻ p, ((Finset.univ.filter fun i => p ∈ Y i).card : ENNReal) := by
  have h : ∀ p, ((Finset.univ.filter fun i => p ∈ Y i).card : ENNReal) =
      ∑ i, (Y i).indicator 1 p := by
    intro p
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p ∈ Y i <;> simp [hp]
  simp_rw [h]
  rw [lintegral_finset_sum _ (fun i _ => measurable_one.indicator (hY i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_indicator_one (hY i)]

/-- Restricting a shading of uniform multiplicity to a set capturing a share of its union
keeps the same share of its mass, up to a factor `2`. -/
theorem capture_mass {m : ℕ} {Y : Fin m → Set V} (hY : ∀ i, MeasurableSet (Y i)) {k : ℕ}
    (hlev : ∀ p ∈ ⋃ i, Y i, 2 ^ k ≤ (Finset.univ.filter fun i => p ∈ Y i).card ∧
      (Finset.univ.filter fun i => p ∈ Y i).card < 2 ^ (k + 1))
    {S : Set V} (hS : MeasurableSet S) {a : ENNReal}
    (hcap : volume (⋃ i, Y i) ≤ a * volume (S ∩ ⋃ i, Y i)) :
    ∑ i, volume (Y i) ≤ 2 * a * ∑ i, volume (Y i ∩ S) := by
  have hU : MeasurableSet (⋃ i, Y i) := MeasurableSet.iUnion hY
  have hup : ∑ i, volume (Y i) ≤ (2 ^ (k + 1) : ENNReal) * volume (⋃ i, Y i) := by
    rw [sum_volume_eq_lintegral hY, ← lintegral_indicator_const hU]
    apply lintegral_mono
    intro p
    dsimp only
    by_cases hp : p ∈ ⋃ i, Y i
    · simp only [Set.indicator_of_mem hp]
      exact_mod_cast (hlev p hp).2.le
    · simp only [Set.indicator_of_notMem hp]
      have : (Finset.univ.filter fun i => p ∈ Y i) = ∅ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        exact fun h => hp (Set.mem_iUnion.mpr ⟨i, h⟩)
      simp [this]
  have hlow : (2 ^ k : ENNReal) * volume (S ∩ ⋃ i, Y i) ≤ ∑ i, volume (Y i ∩ S) := by
    rw [sum_volume_eq_lintegral (fun i => (hY i).inter hS), ← lintegral_indicator_const (hS.inter hU)]
    apply lintegral_mono
    intro p
    dsimp only
    by_cases hp : p ∈ S ∩ ⋃ i, Y i
    · simp only [Set.indicator_of_mem hp]
      have hsub : (Finset.univ.filter fun i => p ∈ Y i) ⊆
          (Finset.univ.filter fun i => p ∈ Y i ∩ S) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨hi, hp.1⟩
      calc (2 ^ k : ENNReal) ≤ ((Finset.univ.filter fun i => p ∈ Y i).card : ENNReal) := by
            exact_mod_cast (hlev p hp.2).1
        _ ≤ _ := by
          have h : ((Finset.univ.filter fun i => p ∈ Y i).card : ENNReal) ≤
              ((Finset.univ.filter fun i => p ∈ Y i ∩ S).card : ENNReal) := by
            exact_mod_cast Finset.card_le_card hsub
          convert h
    · simp only [Set.indicator_of_notMem hp]
      simp
  calc ∑ i, volume (Y i) ≤ (2 ^ (k + 1) : ENNReal) * volume (⋃ i, Y i) := hup
    _ ≤ (2 ^ (k + 1) : ENNReal) * (a * volume (S ∩ ⋃ i, Y i)) := by gcongr
    _ = 2 * a * ((2 ^ k : ENNReal) * volume (S ∩ ⋃ i, Y i)) := by ring
    _ ≤ 2 * a * ∑ i, volume (Y i ∩ S) := by gcongr

/-- Rescaled size of an anisotropic piece. -/
theorem rescale_piece_le {E : V ≃ₗᵢ[ℝ] V} {w : V}
    (hew : E w = axis) (hw : ‖w‖ = 1) {ρ s : ℝ}
    (hρ : 0 < ρ) (hs : 0 ≤ s) {u : V}
    (h1 : ‖u - (inner ℝ w u) • w‖ ≤ 4 * ρ * s) (h2 : |inner ℝ w u| ≤ 4 * s) :
    ‖(1 / 100 : ℝ) • stretch ρ⁻¹ (E u)‖ ≤ s / 16 := by
  have hi : inner ℝ axis (E u) = inner ℝ w u := by rw [← hew, E.inner_map_map]
  have h0 : (E u) 0 = inner ℝ w u := by
    rw [← hi]
    simp [axis, PiLp.inner_apply, Fin.sum_univ_three]
  have hn := norm_sq_coords (E u)
  rw [E.norm_map] at hn
  have e1 := norm_sub_sq_real u ((inner ℝ w u) • w)
  have e2 : inner ℝ u ((inner ℝ w u) • w) = (inner ℝ w u) ^ 2 := by
    rw [real_inner_smul_right, real_inner_comm]; ring
  have e3 : ‖(inner ℝ w u) • w‖ ^ 2 = (inner ℝ w u) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, hw, mul_one, sq_abs]
  rw [e2, e3] at e1
  have hst : ‖stretch ρ⁻¹ (E u)‖ ^ 2 =
      (inner ℝ w u) ^ 2 + ρ⁻¹ ^ 2 * ‖u - (inner ℝ w u) • w‖ ^ 2 := by
    rw [norm_sq_coords]
    simp only [stretch_zero, stretch_one, stretch_two]
    rw [h0]
    have : (E u) 1 ^ 2 + (E u) 2 ^ 2 = ‖u - (inner ℝ w u) • w‖ ^ 2 := by
      rw [e1, hn, h0]; ring
    rw [← this]; ring
  have hperp2 : ρ⁻¹ ^ 2 * ‖u - (inner ℝ w u) • w‖ ^ 2 ≤ 16 * s ^ 2 := by
    have hp0 : 0 ≤ ‖u - (inner ℝ w u) • w‖ := norm_nonneg _
    have : ‖u - (inner ℝ w u) • w‖ ^ 2 ≤ (4 * ρ * s) ^ 2 := pow_le_pow_left₀ hp0 h1 2
    calc ρ⁻¹ ^ 2 * ‖u - (inner ℝ w u) • w‖ ^ 2 ≤ ρ⁻¹ ^ 2 * (4 * ρ * s) ^ 2 := by gcongr
      _ = 16 * s ^ 2 := by field_simp; ring
  have hax2 : (inner ℝ w u) ^ 2 ≤ 16 * s ^ 2 := by
    have := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
    nlinarith
  have hsq : ‖stretch ρ⁻¹ (E u)‖ ^ 2 ≤ (6.25 * s) ^ 2 := by nlinarith
  have hS : ‖stretch ρ⁻¹ (E u)‖ ≤ 6.25 * s :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
  linarith

/-- Smallness of a fixed power, for all small bases. -/
theorem exists_small_rpow {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ d : ℝ, 0 < d ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ d → ξ ^ a ≤ c := by
  refine ⟨c ^ a⁻¹, Real.rpow_pos_of_pos hc _, ?_⟩
  intro ξ hξ hξd
  calc ξ ^ a ≤ (c ^ a⁻¹) ^ a := Real.rpow_le_rpow hξ.le hξd ha.le
    _ = c := Real.rpow_inv_rpow hc.le ha.ne'

set_option maxHeartbeats 3200000 in
/-- Prisms in one thin carrier, from the polynomial grains partition and x0310's prism
family. -/
theorem prism_in_carrier {ζ β D : ℝ} (hζ : 0 < ζ) (hβ : 0 < β) (hD : 0 < D) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η ≤ ζ / 48 ∧ ∃ d : ℝ, 0 < d ∧ ∃ K : ℝ, 1 ≤ K ∧
    ∀ (δ ρ c : ℝ), 0 < δ → ∀ hρ : 0 < ρ, ρ ≤ 1 / 256 → 0 < c → 16 * δ ≤ 128 * ρ * c →
      δ / (100 * ρ) ≤ d →
      2560 * c ≤ (δ / (100 * ρ)) ^ (ζ / 5) →
      ∀ (m : ℕ) (x v : Fin m → V) (Y : Fin m → Set V) (y w : V) (k : ℕ),
      (m : ℝ) ≤ (δ / (100 * ρ)) ^ (-D) →
      c * m * δ ≤ (δ / (100 * ρ)) ^ (ζ / 5) * ρ →
      ‖w‖ = 1 → (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ Tb δ (x i) (v i)) →
      (∀ i, (Y i).Nonempty → Tb δ (x i) (v i) ⊆ Tb ρ y w) →
      (∀ p ∈ ⋃ i, Y i, 2 ^ k ≤ (Finset.univ.filter fun i => p ∈ Y i).card ∧
          (Finset.univ.filter fun i => p ∈ Y i).card < 2 ^ (k + 1)) →
      ENNReal.ofReal ((δ / (100 * ρ)) ^ (η / 4) * m * δ ^ 2) ≤ ∑ i, volume (Y i) →
      (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
        (({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s} : Set (Fin m)).ncard : ℝ) ≤
          (δ / (100 * ρ)) ^ (-η) * (s / ρ) ^ β * (({i | p ∈ Y i} : Set (Fin m)).ncard : ℝ)) →
      ∃ (Y' : Fin m → Set V) (r : ℝ) (N : ℕ) (C : Fin N → Set V) (q : Fin N → V),
        (∀ i, MeasurableSet (Y' i) ∧ Y' i ⊆ Y i) ∧
        (∑ i, volume (Y i)) ≤ ENNReal.ofReal (K * (δ / (100 * ρ)) ^ (-(η / 8))) *
          ∑ i, volume (Y' i) ∧
        Nonempty (RIS.Interfaces.CellPrismFamily δ r ρ c ζ x v Y' C q y w) := by
  obtain ⟨η, hη, hη1, hηζ, d₁, hd₁, hprism⟩ :=
    RIS.Interfaces.rescaled_prism_family_of_bounded_partition hζ hβ hD
  obtain ⟨KP, hKP, dP, hdP, hpart⟩ :=
    PolyMethod.Grains.grains_partition_tube (η / 8) (by positivity)
  have hKP0 : 0 < KP := by linarith
  obtain ⟨da, hda, hsa⟩ := exists_small_rpow (by positivity : 0 < η / 2)
    (by positivity : (0 : ℝ) < 1 / (10 ^ 9 * KP ^ 2))
  obtain ⟨db, hdb, hsb⟩ := exists_small_rpow hη (by positivity : (0 : ℝ) < 1 / (16 * KP))
  obtain ⟨dc, hdc, hsc⟩ := exists_small_rpow (by positivity : 0 < ζ / 30)
    (by norm_num : (0 : ℝ) < 1 / 20000)
  refine ⟨η, hη, hη1, hηζ, min (min (min d₁ (1 / 100)) (dP / 100)) (min da (min db dc)),
    by positivity, 2 * KP, by linarith, ?_⟩
  intro δ ρ c hδ hρ hρ256 hc hsize hξd hc2560 m x v Y y w k hmD hcm hw hv hYm hYT hYcar hlev
    hdens hbroad
  set ξ : ℝ := δ / (100 * ρ) with hξ_def
  have hξ0 : 0 < ξ := by positivity
  simp only [le_min_iff] at hξd
  obtain ⟨⟨⟨hξd₁, hξ100⟩, hξP⟩, hξa, hξb, hξc⟩ := hξd
  have hξ1 : ξ ≤ 1 := hξ100.trans (by norm_num)
  have hδρ : δ / ρ = 100 * ξ := by rw [hξ_def]; field_simp
  have hδρP : δ ≤ dP * ρ := by
    have : δ / ρ ≤ dP := by rw [hδρ]; linarith
    rwa [div_le_iff₀ hρ] at this
  have hδ1 : δ ≤ 1 := by
    have : δ / ρ ≤ 1 := by rw [hδρ]; linarith
    rw [div_le_iff₀ hρ] at this
    linarith
  have hρ1 : ρ ≤ 1 := by linarith
  -- powers of `ξ`
  have hpa := hsa ξ hξ0 hξa
  have hpb := hsb ξ hξ0 hξb
  have hpc := hsc ξ hξ0 hξc
  have hz5 : ξ ^ (ζ / 5) = ξ ^ (ζ / 6) * ξ ^ (ζ / 30) := by
    rw [← Real.rpow_add hξ0]; congr 1; ring
  have hz6 : ξ ^ (ζ / 6) ≤ 1 := Real.rpow_le_one hξ0.le hξ1 (by positivity)
  have hz5' : ξ ^ (ζ / 5) ≤ ξ ^ (ζ / 30) := by
    rw [hz5]; exact mul_le_of_le_one_left (by positivity) hz6
  have hc1 : 2560 * c ≤ 1 := hc2560.trans (hz5'.trans (hpc.trans (by norm_num)))
  -- the partition
  set E : Set V := ⋃ i, Y i with hE_def
  have hEm : MeasurableSet E := MeasurableSet.iUnion hYm
  have hEsub : E ⊆ Tb ρ y w := by
    intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    exact hYcar i ⟨p, hi⟩ (hYT i hi)
  obtain ⟨s, mP, G, P, cP, hs1, hs4, -, hguth, hP, hPdisj, -, hPthin, hPtot, -, hPcross⟩ :=
    hpart δ ρ hδ hδρP hρ1 y w hw E hEm hEsub
  have hs0 : 0 < s := lt_of_lt_of_le (div_pos hδ hρ) hs1
  set S : Set V := ⋃ j, P j with hS_def
  have hSm : MeasurableSet S := MeasurableSet.iUnion fun j => (hP j).1
  set Y' : Fin m → Set V := fun i => Y i ∩ S with hY'_def
  have hY'm : ∀ i, MeasurableSet (Y' i) := fun i => (hYm i).inter hSm
  -- the tube volume bound and the union of the shading
  have htube : ∀ i, volume (Tb δ (x i) (v i)) ≤ ENNReal.ofReal (384 * δ ^ 2) :=
    fun i => RIS.tube_volume_upper hδ hδ1 (x i) (v i) (hv i)
  have hEvol : volume E ≤ ENNReal.ofReal (m * (384 * δ ^ 2)) := by
    calc volume E ≤ ∑ i, volume (Y i) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : Fin m, ENNReal.ofReal (384 * δ ^ 2) :=
          Finset.sum_le_sum fun i _ => (measure_mono (hYT i)).trans (htube i)
      _ = ENNReal.ofReal (m * (384 * δ ^ 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  -- mass captured by the partition
  set t : ℝ := (δ / ρ) ^ (η / 8) with ht_def
  have ht0 : 0 < t := Real.rpow_pos_of_pos (div_pos hδ hρ) _
  have htinv : (δ / ρ) ^ (-(η / 8)) = t⁻¹ := Real.rpow_neg (div_pos hδ hρ).le _
  have hPS : volume S = ∑ j, volume (P j) := by
    rw [hS_def, measure_iUnion (fun j k hjk => hPdisj hjk) (fun j => (hP j).1), tsum_fintype]
  have hSE : S ⊆ E := iUnion_subset fun j => (hP j).2.1
  have hcap : volume E ≤ ENNReal.ofReal (KP * t⁻¹) * volume (S ∩ E) := by
    rw [Set.inter_eq_left.mpr hSE, hPS]
    have h1 : ENNReal.ofReal (KP * t⁻¹) * ENNReal.ofReal (t / KP) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have : KP * t⁻¹ * (t / KP) = 1 := by field_simp
      rw [this, ENNReal.ofReal_one]
    have h2 := hPtot
    calc volume E = ENNReal.ofReal (KP * t⁻¹) * (ENNReal.ofReal (t / KP) * volume E) := by
          rw [← mul_assoc, h1, one_mul]
      _ ≤ _ := by gcongr
  have hmass := capture_mass hYm hlev hSm hcap
  have hmass' : (∑ i, volume (Y i)) ≤ ENNReal.ofReal (2 * KP * t⁻¹) * ∑ i, volume (Y' i) := by
    calc (∑ i, volume (Y i)) ≤ 2 * ENNReal.ofReal (KP * t⁻¹) * ∑ i, volume (Y i ∩ S) := hmass
      _ = ENNReal.ofReal (2 * KP * t⁻¹) * ∑ i, volume (Y' i) := by
          have h2 : ENNReal.ofReal (2 * KP * t⁻¹) = 2 * ENNReal.ofReal (KP * t⁻¹) := by
            rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
          rw [h2]
  -- the output mass relation, with `t⁻¹ ≤ ξ ^ (-(η/8))`
  have htξ : t⁻¹ ≤ ξ ^ (-(η / 8)) := by
    rw [← htinv, hδρ]
    exact Real.rpow_le_rpow_of_nonpos hξ0 (by linarith) (by linarith)
  refine ⟨Y', ?_⟩
  -- parameters for x0310
  set R : ℝ := s / 16 with hR_def
  set r : ℝ := min 1 (100 * R) with hr_def
  set L : ℝ := KP * (δ / ρ) ^ (-(η / 8)) / s with hL_def
  have hr0 : 0 < r := lt_min one_pos (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrR : r / 100 ≤ R := by
    have := min_le_right 1 (100 * R)
    rw [← hr_def] at this
    linarith
  have hL0 : 0 ≤ L := by positivity
  -- the Guth bound: either `r = 1` or `ρ ≤ 48 s m δ`
  have hcases : r = 1 ∨ (r = 100 * R ∧ ρ ≤ 48 * s * m * δ) := by
    by_cases hA : 1 ≤ 100 * R
    · left; exact min_eq_left hA
    · right
      push_neg at hA
      refine ⟨min_eq_right hA.le, ?_⟩
      rcases hguth with hg | hg
      · have h2 : ENNReal.ofReal (8 * δ * ρ) ≤ ENNReal.ofReal (s * (m * (384 * δ ^ 2))) := by
          rw [ENNReal.ofReal_mul hs0.le]
          exact hg.trans (by gcongr)
        have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
        nlinarith
      · exfalso
        rw [hR_def, hg] at hA
        norm_num at hA
  have h512 : 512 * c ≤ r := by
    rcases hcases with hr | ⟨hr, hρs⟩
    · rw [hr]; linarith
    · have hmδ : 0 < (m : ℝ) * δ := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · exfalso; rw [h0] at hρs; simp at hρs; linarith
        · positivity
      have hcs : c ≤ 48 * ξ ^ (ζ / 5) * s := by
        have : c * (m * δ) ≤ 48 * ξ ^ (ζ / 5) * s * (m * δ) := by
          calc c * (m * δ) = c * m * δ := by ring
            _ ≤ ξ ^ (ζ / 5) * ρ := hcm
            _ ≤ ξ ^ (ζ / 5) * (48 * s * m * δ) := by gcongr
            _ = 48 * ξ ^ (ζ / 5) * s * (m * δ) := by ring
        exact le_of_mul_le_mul_right this hmδ
      rw [hr, hR_def]
      have : ξ ^ (ζ / 5) ≤ 1 / 20000 := hz5'.trans hpc
      have h1 : ξ ^ (ζ / 5) * s ≤ 1 / 20000 * s := mul_le_mul_of_nonneg_right this hs0.le
      linarith [hcs, h1]
  have h2560 : 2560 * c ≤ ξ ^ (ζ / 6) * r := by
    rcases hcases with hr | ⟨hr, hρs⟩
    · rw [hr, mul_one]
      have h1 : ξ ^ (ζ / 5) ≤ ξ ^ (ζ / 6) := by
        rw [hz5]
        exact mul_le_of_le_one_right (by positivity) (hpc.trans (by norm_num))
      exact hc2560.trans h1
    · have hmδ : 0 < (m : ℝ) * δ := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · exfalso; rw [h0] at hρs; simp at hρs; linarith
        · positivity
      have hcs : c ≤ 48 * ξ ^ (ζ / 5) * s := by
        have : c * (m * δ) ≤ 48 * ξ ^ (ζ / 5) * s * (m * δ) := by
          calc c * (m * δ) = c * m * δ := by ring
            _ ≤ ξ ^ (ζ / 5) * ρ := hcm
            _ ≤ ξ ^ (ζ / 5) * (48 * s * m * δ) := by gcongr
            _ = 48 * ξ ^ (ζ / 5) * s * (m * δ) := by ring
        exact le_of_mul_le_mul_right this hmδ
      rw [hr, hR_def]
      rw [hz5] at hcs
      have hz6' : 0 ≤ ξ ^ (ζ / 6) := by positivity
      have h1 : ξ ^ (ζ / 6) * ξ ^ (ζ / 30) * s ≤ ξ ^ (ζ / 6) * (1 / 20000) * s := by gcongr
      linarith [hcs, h1]
  -- the rotation
  obtain ⟨Er, hEr⟩ := exists_rotation hw
  -- the hypotheses of x0310's theorem
  have hY'fin : ∀ i, volume (Y' i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (RIS.tube_volume_ne_top δ (x i) (v i))
      (measure_mono (Set.inter_subset_left.trans (hYT i)))
  have hY'T : ∀ i, Y' i ⊆ Tb δ (x i) (v i) := fun i => Set.inter_subset_left.trans (hYT i)
  have hY'car : ∀ i, (Y' i).Nonempty → Tb δ (x i) (v i) ⊆ Tb ρ y w :=
    fun i hi => hYcar i (hi.mono Set.inter_subset_left)
  have hPball : ∀ j, P j ⊆ (RIS.rescaleMap Er y w (by norm_num : (0 : ℝ) < 1 / 100) hρ) ⁻¹'
      closedBall (RIS.rescaleMap Er y w (by norm_num : (0 : ℝ) < 1 / 100) hρ (cP j)) R := by
    intro j p hp
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, RIS.rescaleMap_sub]
    obtain ⟨h1, h2⟩ := (hP j).2.2 p hp
    exact rescale_piece_le hEr hw hρ hs0.le h1 h2
  have hcover : (⋃ i, Y' i) ⊆ ⋃ j, P j := iUnion_subset fun i => Set.inter_subset_right
  have hcross : ∀ i, (({j | (Y' i ∩ P j).Nonempty} : Set (Fin G)).ncard : ℝ) ≤ L := by
    intro i
    by_cases hi : (Y' i).Nonempty
    · calc (({j | (Y' i ∩ P j).Nonempty} : Set (Fin G)).ncard : ℝ)
          ≤ (({j | (Tb δ (x i) (v i) ∩ P j).Nonempty} : Set (Fin G)).ncard : ℝ) := by
            exact_mod_cast Set.ncard_le_ncard
              (fun j hj => Set.Nonempty.mono (Set.inter_subset_inter_left _ (hY'T i)) hj)
              (Set.toFinite _)
        _ ≤ L := hPcross (x i) (v i) (hv i) (hY'car i hi)
    · have : ({j | (Y' i ∩ P j).Nonempty} : Set (Fin G)) = ∅ := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hi (h.mono Set.inter_subset_left)
      rw [this, Set.ncard_empty, Nat.cast_zero]
      exact hL0
  -- density
  have hshade : ξ ^ (η / 4) * m * δ ^ 2 * t / (2 * KP) ≤
      wz_extremal_lipschitz_grains.shadingMass Y' := by
    have h1 : ENNReal.ofReal (ξ ^ (η / 4) * m * δ ^ 2) ≤
        ENNReal.ofReal (2 * KP * t⁻¹) * ∑ i, volume (Y' i) := hdens.trans hmass'
    have hfin : (∑ i, volume (Y' i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hY'fin i
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity)] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    have h3 : (∑ i, volume (Y' i)).toReal = wz_extremal_lipschitz_grains.shadingMass Y' := by
      rw [wz_extremal_lipschitz_grains.shadingMass, ENNReal.toReal_sum fun i _ => hY'fin i]
    rw [h3] at h2
    rw [div_le_iff₀ (by positivity)]
    calc ξ ^ (η / 4) * m * δ ^ 2 * t ≤ 2 * KP * t⁻¹ * wz_extremal_lipschitz_grains.shadingMass Y' * t := by
          gcongr
      _ = wz_extremal_lipschitz_grains.shadingMass Y' * (2 * KP) := by field_simp
  have htξ' : ξ ^ (η / 8) ≤ t := by
    rw [ht_def, hδρ]
    exact Real.rpow_le_rpow hξ0.le (by linarith) (by positivity)
  have hdensx : 2 * (ξ ^ η * δ ^ 2 * r) * m * ((12 * R / (r / 100)) ^ 3 * L) ≤
      wz_extremal_lipschitz_grains.shadingMass Y' := by
    refine le_trans ?_ hshade
    -- `(12 R / (r/100))^3 * L * r ≤ 300^3 * 6.25 * KP * t⁻¹`
    have hLt : L = KP * t⁻¹ / s := by rw [hL_def, htinv]
    have hbox : (12 * R / (r / 100)) ^ 3 * L * r ≤ 300 ^ 3 * 7 * KP * t⁻¹ := by
      rw [hLt]
      have hratio : 12 * R / (r / 100) ≤ 300 := by
        rw [div_le_iff₀ (by positivity)]
        rcases hcases with hr | ⟨hr, -⟩
        · rw [hr, hR_def]; linarith
        · rw [hr, hR_def]; nlinarith
      have hrs : r / s ≤ 7 := by
        rw [div_le_iff₀ hs0]
        rcases hcases with hr | ⟨hr, -⟩
        · rw [hr]
          by_contra hcon
          push_neg at hcon
          have : 100 * R < 1 := by rw [hR_def]; linarith
          have := min_eq_right this.le
          rw [← hr_def] at this
          linarith
        · rw [hr, hR_def]; linarith
      have hq0 : 0 ≤ 12 * R / (r / 100) := by positivity
      calc (12 * R / (r / 100)) ^ 3 * (KP * t⁻¹ / s) * r
          = (12 * R / (r / 100)) ^ 3 * (KP * t⁻¹) * (r / s) := by ring
        _ ≤ 300 ^ 3 * (KP * t⁻¹) * 7 := by gcongr
        _ = 300 ^ 3 * 7 * KP * t⁻¹ := by ring
    have hkey : 2 * ξ ^ η * (300 ^ 3 * 7 * KP * t⁻¹) ≤ ξ ^ (η / 4) * t / (2 * KP) := by
      rw [le_div_iff₀ (by positivity)]
      have hxi : ξ ^ η = ξ ^ (η / 2) * ξ ^ (η / 4) * ξ ^ (η / 8) * ξ ^ (η / 8) := by
        rw [← Real.rpow_add hξ0, ← Real.rpow_add hξ0, ← Real.rpow_add hξ0]; congr 1; ring
      have ht2 : ξ ^ (η / 8) * ξ ^ (η / 8) ≤ t * t := by gcongr
      have hpa' : ξ ^ (η / 2) * (10 ^ 9 * KP ^ 2) ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at hpa; linarith
      have e1 : 2 * ξ ^ η * (300 ^ 3 * 7 * KP * t⁻¹) * (2 * KP) =
          (ξ ^ (η / 2) * (10 ^ 9 * KP ^ 2)) * (ξ ^ (η / 4) * (ξ ^ (η / 8) * ξ ^ (η / 8))) * t⁻¹ *
            (4 * 300 ^ 3 * 7 / 10 ^ 9) := by
        rw [hxi]; ring
      rw [e1]
      have hq : (4 * 300 ^ 3 * 7 / 10 ^ 9 : ℝ) ≤ 1 := by norm_num
      have hb : 0 ≤ ξ ^ (η / 4) * (ξ ^ (η / 8) * ξ ^ (η / 8)) * t⁻¹ := by positivity
      calc (ξ ^ (η / 2) * (10 ^ 9 * KP ^ 2)) * (ξ ^ (η / 4) * (ξ ^ (η / 8) * ξ ^ (η / 8))) * t⁻¹ *
            (4 * 300 ^ 3 * 7 / 10 ^ 9)
          ≤ 1 * (ξ ^ (η / 4) * (ξ ^ (η / 8) * ξ ^ (η / 8))) * t⁻¹ * 1 := by gcongr
        _ ≤ 1 * (ξ ^ (η / 4) * (t * t)) * t⁻¹ * 1 := by gcongr
        _ = ξ ^ (η / 4) * t := by field_simp
    have hδm : 0 ≤ δ ^ 2 * m := by positivity
    calc 2 * (ξ ^ η * δ ^ 2 * r) * m * ((12 * R / (r / 100)) ^ 3 * L)
        = 2 * ξ ^ η * ((12 * R / (r / 100)) ^ 3 * L * r) * (δ ^ 2 * m) := by ring
      _ ≤ 2 * ξ ^ η * (300 ^ 3 * 7 * KP * t⁻¹) * (δ ^ 2 * m) := by gcongr
      _ ≤ ξ ^ (η / 4) * t / (2 * KP) * (δ ^ 2 * m) := by gcongr
      _ = ξ ^ (η / 4) * m * δ ^ 2 * t / (2 * KP) := by ring
  -- local volume
  have hlocal : ∀ j p, volume (P j ∩ (RIS.rescaleMap Er y w (by norm_num : (0 : ℝ) < 1 / 100) hρ) ⁻¹'
      ball (RIS.rescaleMap Er y w (by norm_num : (0 : ℝ) < 1 / 100) hρ p) (r / 100)) ≤
      ENNReal.ofReal (ξ ^ (-η) * δ * ρ * r ^ 2) := by
    intro j p
    refine (measure_mono Set.inter_subset_left).trans ((hPthin j).trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have hb' : 16 * KP ≤ ξ ^ (-η) := by
      rw [Real.rpow_neg hξ0.le, le_inv_comm₀ (by positivity) (by positivity)]
      rw [le_div_iff₀ (by positivity)] at hpb
      rw [inv_eq_one_div, le_div_iff₀ (by positivity)]; linarith
    have hs2 : KP * s ^ 2 ≤ ξ ^ (-η) * r ^ 2 := by
      rcases hcases with hr | ⟨hr, -⟩
      · rw [hr]
        have : s ^ 2 ≤ 16 := by nlinarith
        nlinarith
      · rw [hr, hR_def]
        nlinarith
    have hδρ0 : 0 ≤ δ * ρ := by positivity
    nlinarith
  -- broadness for `Y'`
  have hbroadx : ∀ p u s', ‖u‖ = 1 → δ ≤ s' → s' ≤ ρ →
      (({i | p ∈ Y' i ∧ pd (v i) u ≤ s'} : Set (Fin m)).ncard : ℝ) ≤
        (ξ ^ (-η) * (s' / ρ) ^ β) * wz_extremal_lipschitz_grains.incidence Y' p := by
    intro p u s' hu hs' hs'ρ
    rw [wz_extremal_lipschitz_grains.incidence_eq_ncard]
    by_cases hpS : p ∈ S
    · have e1 : ({i | p ∈ Y' i ∧ pd (v i) u ≤ s'} : Set (Fin m)) =
          {i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s'} := by
        ext i; simp only [Set.mem_setOf_eq, Y', Set.mem_inter_iff, pd]; tauto
      have e2 : ({i | p ∈ Y' i} : Set (Fin m)) = {i | p ∈ Y i} := by
        ext i; simp only [Set.mem_setOf_eq, Y', Set.mem_inter_iff]; tauto
      rw [e1, e2]
      exact hbroad p u s' hu hs' hs'ρ
    · have e1 : ({i | p ∈ Y' i ∧ pd (v i) u ≤ s'} : Set (Fin m)) = ∅ := by
        ext i; simp only [Set.mem_setOf_eq, Y', Set.mem_inter_iff, Set.mem_empty_iff_false,
          iff_false]; tauto
      rw [e1, Set.ncard_empty, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hξ0.le _)
        (Real.rpow_nonneg (div_nonneg (hδ.le.trans hs') hρ.le) _)) (Nat.cast_nonneg _)
  have key := hprism δ r R ρ c L hδ hρ hρ256 hc (by linarith) h512 hr1 hrR hL0 hsize hξ100 hξd₁
    h2560 m G x v Y' P cP y w Er hEr hmD hw hv hY'm hY'fin hY'T hY'car (fun j => (hP j).1)
    hPball hPdisj hcover hcross hdensx hlocal hbroadx
  obtain ⟨N, C, q, -, -, -, -, -, -, hfam⟩ := key
  refine ⟨r, N, C, q, fun i => ⟨hY'm i, Set.inter_subset_left⟩, ?_, hfam⟩
  calc (∑ i, volume (Y i)) ≤ ENNReal.ofReal (2 * KP * t⁻¹) * ∑ i, volume (Y' i) := hmass'
    _ ≤ ENNReal.ofReal (2 * KP * ξ ^ (-(η / 8))) * ∑ i, volume (Y' i) := by
        gcongr

end WangZahlLot.Obl.wz_coarse_tube_grains
