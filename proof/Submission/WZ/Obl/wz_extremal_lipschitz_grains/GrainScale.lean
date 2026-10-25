-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GrainScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GrainFan
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LipschitzRefine
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LipschitzTools

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- The mass measure is at least the minimal multiplicity times the volume of the shaded part. -/
theorem massMeasure_ge_mul {n : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i))
    {μlo : ℝ} (hlo : ∀ y ∈ ⋃ i, Y i, μlo ≤ (fineMult Y y : ℝ)) {S : Set Space}
    (hS : MeasurableSet S) :
    ENNReal.ofReal μlo * volume ((⋃ i, Y i) ∩ S) ≤ massMeasure Y S := by
  rw [massMeasure, withDensity_apply _ hS]
  have hU : MeasurableSet (⋃ i, Y i) := MeasurableSet.iUnion hY
  calc ENNReal.ofReal μlo * volume ((⋃ i, Y i) ∩ S)
      = ∫⁻ y in S, (⋃ i, Y i).indicator (fun _ => ENNReal.ofReal μlo) y := by
        rw [lintegral_indicator hU, setLIntegral_const, Measure.restrict_apply hU, inter_comm,
          mul_comm]
    _ ≤ ∫⁻ y in S, (fineMult Y y : ℝ≥0∞) := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ ⋃ i, Y i
        · rw [indicator_of_mem hy]
          show ENNReal.ofReal μlo ≤ (fineMult Y y : ℝ≥0∞)
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (hlo y hy)
        · rw [indicator_of_notMem hy]; exact zero_le

/-- **Cube bound from a two-scale decomposition**: the refined fine set has volume
`O((r / τc)⁴ τc^(3-σ-ε) δ^(σ-2ε))` in every closed ball of radius `r ∈ [τc, 1]`. -/
theorem volume_ball_le_of_twoScale {σ ε δ τc : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hδ : 0 < δ) (hτc : δ ≤ τc) (hτc4 : τc ≤ 1 / 4) (hn : 0 < n)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i))
    (hTS : TwoScaleAtP σ ε δ τc n x v Y) :
    ∃ Y' : Fin n → Set Space, (∀ i, Y' i ⊆ Y i) ∧ (∀ i, MeasurableSet (Y' i)) ∧
      ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y' i) ∧
      (∀ p ∈ ⋃ i, Y' i, δ ^ (2 - σ + ε) * (n : ℝ) ≤ (fineMult Y' p : ℝ)) ∧
      ∀ c : Space, ∀ r : ℝ, τc ≤ r →
        volume ((⋃ i, Y' i) ∩ closedBall c r) ≤
          ENNReal.ofReal (54880000 * (r / τc) ^ 4 * τc ^ (3 - σ - ε) * δ ^ (σ - 2 * ε)) := by
  classical
  obtain ⟨Y', K, z, w, Yt, a, s, M, hY'Y, hY'm, hY'mass, hFamc, hSepc, hvolc, hcontr, hdir, hs,
    hslo, hshi, hYt, hfine, hfib, hcoarse, hclo, hR1, hR2, hP2, hP3⟩ := hTS
  refine ⟨Y', hY'Y, hY'm, hY'mass, hfine, ?_⟩
  intro c r hr
  have hK : 0 < K := hFamc.1
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hτ0 : 0 < τc := hδ.trans_le hτc
  have hr0 : 0 < r := hτ0.trans_le hr
  set lam := 1 - 4 * τc with hlam
  set B := closedBall c r with hB
  -- labels of fine tubes meeting the ball
  set I : Finset (Fin n) := Finset.univ.filter fun i => (Y' i ∩ B).Nonempty with hI
  obtain ⟨S, hScard, hS⟩ := exists_cells_cover (lam • c) hr0.le hs
  set Cc := τc ^ (2 - σ - ε) * (K : ℝ) with hCc
  have hlab : ∀ m, ((Finset.univ.filter fun J => m ∈ M J).card : ℝ) ≤ Cc :=
    card_labels_le hs hYt hcoarse
  set 𝒥 : Finset (Fin K) := S.biUnion fun m => Finset.univ.filter fun J => m ∈ M J with h𝒥
  have hlam0 : 0 ≤ lam := by rw [hlam]; linarith
  have hlam1 : lam ≤ 1 := by linarith
  -- fine labels meeting the ball map into the coarse labels `𝒥`
  have hI𝒥 : ∀ i ∈ I, a i ∈ 𝒥 := by
    intro i hi
    obtain ⟨y, hyY, hyB⟩ := (Finset.mem_filter.1 hi).2
    have hly : lam • y ∈ Yt (a i) := hcontr i ⟨y, hyY, rfl⟩
    rw [hYt] at hly
    obtain ⟨m, hm, hym⟩ := mem_iUnion₂.1 hly
    have hidx : cubeIndex s (lam • y) = m := cubeIndex_eq_of_mem hs hym
    have hdist : dist (lam • y) (lam • c) ≤ r := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hlam0]
      calc lam * dist y c ≤ 1 * r :=
            mul_le_mul hlam1 (mem_closedBall.1 hyB) dist_nonneg zero_le_one
        _ = r := one_mul r
    have hmS := hS (lam • y) hdist
    rw [hidx] at hmS
    exact Finset.mem_biUnion.2 ⟨m, hmS, Finset.mem_filter.2 ⟨Finset.mem_univ _, hm⟩⟩
  -- counting fine labels
  have hIcard : (I.card : ℝ) ≤ (S.card : ℝ) * Cc * (δ ^ (-ε) * ((n : ℝ) / (K : ℝ))) := by
    have hsub : I ⊆ 𝒥.biUnion (fun J => Finset.univ.filter fun i => a i = J ∧ (Y' i).Nonempty) := by
      intro i hi
      refine Finset.mem_biUnion.2 ⟨a i, hI𝒥 i hi, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, ?_⟩⟩
      obtain ⟨y, hy⟩ := (Finset.mem_filter.1 hi).2
      exact ⟨y, hy.1⟩
    have h1 : (I.card : ℝ) ≤ ∑ J ∈ 𝒥,
        ((Finset.univ.filter fun i => a i = J ∧ (Y' i).Nonempty).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : ∀ J, ((Finset.univ.filter fun i => a i = J ∧ (Y' i).Nonempty).card : ℝ) ≤
        δ ^ (-ε) * ((n : ℝ) / (K : ℝ)) := by
      intro J
      have h := hP2 J
      have e : {i | a i = J ∧ (Y' i).Nonempty} =
          ↑(Finset.univ.filter fun i => a i = J ∧ (Y' i).Nonempty) := by ext; simp
      rwa [e, Set.ncard_coe_finset] at h
    have h3 : (𝒥.card : ℝ) ≤ (S.card : ℝ) * Cc := by
      calc (𝒥.card : ℝ) ≤ ∑ m ∈ S, ((Finset.univ.filter fun J => m ∈ M J).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _m ∈ S, Cc := Finset.sum_le_sum fun m _ => hlab m
        _ = S.card * Cc := by rw [Finset.sum_const, nsmul_eq_mul]
    have hpos : 0 ≤ δ ^ (-ε) * ((n : ℝ) / (K : ℝ)) := by positivity
    calc (I.card : ℝ) ≤ _ := h1
      _ ≤ ∑ _J ∈ 𝒥, δ ^ (-ε) * ((n : ℝ) / (K : ℝ)) := Finset.sum_le_sum fun J _ => h2 J
      _ = 𝒥.card * (δ ^ (-ε) * ((n : ℝ) / (K : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S.card : ℝ) * Cc * (δ ^ (-ε) * ((n : ℝ) / (K : ℝ))) := by gcongr
  -- the mass in the ball
  set b := 128 * (4 * (r + δ) + δ) * δ ^ 2 with hb
  have hmassB : massMeasure Y' B ≤ ENNReal.ofReal ((I.card : ℝ) * b) := by
    rw [massMeasure_apply hY'm measurableSet_closedBall]
    calc ∑ i, volume (Y' i ∩ B)
        ≤ ∑ i, (if (Y' i ∩ B).Nonempty then ENNReal.ofReal b else 0) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs with h
          · exact (measure_mono (inter_subset_inter_left _ ((hY'Y i).trans (hYT i)))).trans
              (volume_tube_inter_closedBall_le hδ hr0.le (hv i) c)
          · rw [Set.not_nonempty_iff_eq_empty.1 h, measure_empty]
      _ = ∑ _i ∈ I, ENNReal.ofReal b := by rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      _ = ENNReal.ofReal ((I.card : ℝ) * b) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  set μlo := δ ^ (2 - σ + ε) * (n : ℝ) with hμlo
  have hμlo0 : 0 < μlo := by positivity
  have hlow := massMeasure_ge_mul hY'm hfine (measurableSet_closedBall (x := c) (ε := r))
  have hvolB : volume ((⋃ i, Y' i) ∩ B) ≤ ENNReal.ofReal ((I.card : ℝ) * b / μlo) := by
    have h1 := hlow.trans hmassB
    have hfin : volume ((⋃ i, Y' i) ∩ B) ≠ ∞ :=
      ne_top_of_le_ne_top (measure_closedBall_lt_top (x := c) (r := r)).ne
        (measure_mono inter_subset_right)
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hμlo0.le] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    rw [← ENNReal.ofReal_toReal hfin]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ hμlo0]; linarith
  refine hvolB.trans (ENNReal.ofReal_le_ofReal ?_)
  -- arithmetic
  have hS' : (S.card : ℝ) ≤ (35 * (r / τc)) ^ 3 := by
    have h1 : (S.card : ℝ) ≤ ((⌊2 * r / s⌋₊ : ℝ) + 3) ^ 3 := by exact_mod_cast hScard
    have h2 : (⌊2 * r / s⌋₊ : ℝ) ≤ 2 * r / s := Nat.floor_le (by positivity)
    have h3 : 2 * r / s ≤ 32 * (r / τc) := by
      rw [div_le_iff₀ hs]
      calc 2 * r = 32 * (r / τc) * (τc / 16) := by field_simp; ring
        _ ≤ 32 * (r / τc) * s := by gcongr
    have h4 : 3 ≤ 3 * (r / τc) := by
      have : 1 ≤ r / τc := by rw [le_div_iff₀ hτ0]; linarith
      linarith
    calc (S.card : ℝ) ≤ _ := h1
      _ ≤ (35 * (r / τc)) ^ 3 := by
          apply pow_le_pow_left₀ (by positivity); linarith
  have hb' : b ≤ 1152 * r * δ ^ 2 := by
    rw [hb]; have : δ ≤ r := hτc.trans hr; nlinarith [sq_nonneg δ]
  have hCcn : Cc * (δ ^ (-ε) * ((n : ℝ) / (K : ℝ))) = τc ^ (2 - σ - ε) * δ ^ (-ε) * n := by
    rw [hCc]; field_simp
  have hτpow : τc * τc ^ (2 - σ - ε) = τc ^ (3 - σ - ε) := by
    rw [show τc * τc ^ (2 - σ - ε) = τc ^ (1 : ℝ) * τc ^ (2 - σ - ε) by rw [Real.rpow_one],
      ← Real.rpow_add hτ0]; ring_nf
  have hδpow : δ ^ (-ε) * δ ^ 2 / μlo * n = δ ^ (σ - 2 * ε) := by
    rw [hμlo]
    have e : δ ^ (-ε) * δ ^ 2 = δ ^ (2 - σ + ε) * δ ^ (σ - 2 * ε) := by
      rw [show δ ^ 2 = δ ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      ring_nf
    rw [e]; field_simp
  have hrτ : r = r / τc * τc := by field_simp
  calc (I.card : ℝ) * b / μlo
      ≤ (S.card : ℝ) * Cc * (δ ^ (-ε) * ((n : ℝ) / (K : ℝ))) * (1152 * r * δ ^ 2) / μlo := by
        apply div_le_div_of_nonneg_right _ hμlo0.le
        have hb0 : (0 : ℝ) ≤ 128 * (4 * (r + δ) + δ) * δ ^ 2 := by positivity
        have hCc0 : 0 ≤ Cc := mul_nonneg (Real.rpow_nonneg hτ0.le _) (Nat.cast_nonneg _)
        have hX0 : 0 ≤ (S.card : ℝ) * Cc * (δ ^ (-ε) * ((n : ℝ) / (K : ℝ))) :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCc0)
            (mul_nonneg (Real.rpow_nonneg hδ.le _) (div_nonneg hnR.le hKR.le))
        exact mul_le_mul hIcard hb' hb0 hX0
    _ = (S.card : ℝ) * 1152 * r * τc ^ (2 - σ - ε) * (δ ^ (-ε) * δ ^ 2 / μlo * n) := by
        rw [mul_assoc (S.card : ℝ) Cc, hCcn]; ring
    _ = (S.card : ℝ) * 1152 * (r / τc) * (τc * τc ^ (2 - σ - ε)) * δ ^ (σ - 2 * ε) := by
        rw [hδpow]; nth_rewrite 1 [hrτ]; ring
    _ ≤ (35 * (r / τc)) ^ 3 * 1152 * (r / τc) * τc ^ (3 - σ - ε) * δ ^ (σ - 2 * ε) := by
        rw [hτpow]; gcongr
    _ ≤ 54880000 * (r / τc) ^ 4 * τc ^ (3 - σ - ε) * δ ^ (σ - 2 * ε) := by
        have : 0 ≤ (r / τc) ^ 4 * τc ^ (3 - σ - ε) * δ ^ (σ - 2 * ε) := by positivity
        nlinarith

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
