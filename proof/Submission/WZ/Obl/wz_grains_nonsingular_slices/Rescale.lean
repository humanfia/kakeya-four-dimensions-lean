-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.Rescale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.RescaleMap
import Submission.WZ.Obl.wz_grains_nonsingular_slices.RescaleSelect
import Submission.WZ.Obl.wz_grains_nonsingular_slices.RescaleCount
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Slices

/-!
# Normalized examples from a nondegenerate thin slab

On a slab `|z - a| ≤ 2b` where `m ≤ |f'| ≤ 2m` and `200 b ≤ m`, the map `normMap a b m`
turns the transversal tubes with dense shading in the central slab `|z - a| ≤ b/2` into nearly
vertical tubes at scale `4δ/θ`; distinct representatives with balanced clusters carry the
global convex count, and `normSlope a b m f` is a nonsingular slope with halved slices.
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- A tube contains the ball around its base point. -/
private lemma resc_ball_sub_tube (r : ℝ) (x v : Space) : ball x r ⊆ Tube r x v :=
  ball_subset_thickening (left_mem_segment ℝ x (x + v)) r

/-- The midpoint of the axis lies in the tube. -/
private lemma resc_mid_mem_tube {r : ℝ} (hr : 0 < r) (x v : Space) :
    x + (1 / 2 : ℝ) • v ∈ Tube r x v := by
  apply self_subset_thickening hr
  rw [segment_eq_image']
  exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by simp⟩

/-- Undoing a homothety with the inverse ratio. -/
private lemma resc_hom_cancel {c p : Space} {k lam : ℝ} (h : lam * k = 1) :
    c + lam • ((c + k • (p - c)) - c) = p := by
  rw [add_sub_cancel_left, smul_smul, h, one_smul, add_sub_cancel]

/-- The centre of a homothety is recovered from a point and its image. -/
private lemma resc_center_eq {c p : Space} {k lam : ℝ} (h : lam * (1 - k) = 1) :
    p + lam • ((c + k • (p - c)) - p) = c := by
  have e : (c + k • (p - c)) - p = (1 - k) • (c - p) := by module
  rw [e, smul_smul, h, one_smul, add_sub_cancel]

/-- A ball around the image of `x` under a homothety of ratio `k` is the image of a ball. -/
private lemma resc_ball_hom {c x y : Space} {k ρ : ℝ} (hk : 0 < k)
    (hy : y ∈ ball (c + k • (x - c)) (k * ρ)) :
    ∃ p ∈ ball x ρ, y = c + k • (p - c) := by
  refine ⟨c + k⁻¹ • (y - c), ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm] at hy ⊢
    have e : k⁻¹ • (y - (c + k • (x - c))) = c + k⁻¹ • (y - c) - x := by
      rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
      module
    rw [← e, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hk.le)]
    calc k⁻¹ * ‖y - (c + k • (x - c))‖ < k⁻¹ * (k * ρ) :=
          mul_lt_mul_of_pos_left hy (inv_pos.mpr hk)
      _ = ρ := by field_simp
  · rw [resc_hom_cancel (mul_inv_cancel₀ hk.ne')]

/-- Contracting a point of the unit ball towards a point of norm `≤ 3/2` stays in `ball 0 2`. -/
private lemma resc_norm_contr {c p : Space} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hc : ‖c‖ ≤ 3 / 2) (hp : ‖p‖ < 1) : ‖c + k • (p - c)‖ < 2 := by
  have e : c + k • (p - c) = (1 - k) • c + k • p := by module
  rw [e]
  calc ‖(1 - k) • c + k • p‖ ≤ ‖(1 - k) • c‖ + ‖k • p‖ := norm_add_le _ _
    _ = (1 - k) * ‖c‖ + k * ‖p‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hk0]
    _ < 2 := by nlinarith [norm_nonneg c, norm_nonneg p]

/-- `normMap` is affine. -/
private lemma resc_normMap_combo (a b m : ℝ) (hb : b ≠ 0) (p q : Space) (s t : ℝ)
    (hst : s + t = 1) :
    normMap a b m (s • p + t • q) = s • normMap a b m p + t • normMap a b m q := by
  ext i
  fin_cases i
  · simp [normMap]
    ring
  · simp [normMap]
    ring
  · simp [normMap]
    field_simp
    linear_combination a * hst

/-- Preimages of convex sets under `normMap` are convex. -/
private lemma resc_convex_preimage {a b m : ℝ} (hb : b ≠ 0) {S : Set Space}
    (hS : Convex ℝ S) : Convex ℝ (normMap a b m ⁻¹' S) := by
  intro p hp q hq s t hs ht hst
  show normMap a b m (s • p + t • q) ∈ S
  rw [resc_normMap_combo a b m hb p q s t hst]
  exact hS hp hq hs ht hst

/-- `normMap` scales volume by `m / 4`, so preimages have at most `4 / m` times the volume. -/
private lemma resc_vol_preimage {a b m : ℝ} (hb : 0 < b) (hm : 0 < m) (S X : Set Space) :
    volume (normMap a b m ⁻¹' S ∩ X) ≤ ENNReal.ofReal (4 / m) * volume S := by
  have h1 : ENNReal.ofReal (m / 4) * volume (normMap a b m ⁻¹' S ∩ X) ≤ volume S := by
    rw [← volume_normMap_image hb hm]
    apply measure_mono
    rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  have h2 : ENNReal.ofReal (4 / m) * ENNReal.ofReal (m / 4) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [show 4 / m * (m / 4) = 1 by field_simp]
    simp
  calc volume (normMap a b m ⁻¹' S ∩ X)
      = ENNReal.ofReal (4 / m) * (ENNReal.ofReal (m / 4) * volume (normMap a b m ⁻¹' S ∩ X)) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ ENNReal.ofReal (4 / m) * volume S := by gcongr

/-- The convex container: if a new tube of a selected representative lies in a convex `W`,
the old tubes of its cluster lie in one convex set of volume `≲ K_H³ / (b³ m) · |W|`
(three homothetic hulls: by `10⁶` in normalized coordinates, by `2 / (2 - b)` to capture
the contraction centres, and by `2 / b` to undo the contraction). -/
private lemma resc_hull
    {KH : ℝ} (hKH1 : 1 ≤ KH)
    (hKH : ∀ (W : Set Space) (lam : ℝ), Convex ℝ W →
      W ⊆ ball 0 2 → (∃ (c : Space) (r : ℝ), 0 < r ∧ ball c r ⊆ W) → 1 ≤ lam →
      ∃ W' : Set Space, Convex ℝ W' ∧ (∀ c ∈ W, ∀ p ∈ W, c + lam • (p - c) ∈ W') ∧
        volume W' ≤ ENNReal.ofReal (KH * lam ^ 3) * volume W)
    {δ δ' a b m : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') (hb : 0 < b) (hb1 : b ≤ 1) (hm : 0 < m)
    {ι : Type*} (x v x' w c : ι → Space)
    (G R : Finset ι) (mem : ι → Finset ι)
    (hRG : R ⊆ G) (hmemG : ∀ r ∈ R, mem r ⊆ G)
    (hT : ∀ i ∈ G, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hc : ∀ i ∈ G, ‖c i‖ ≤ 3 / 2)
    (hτ : ∀ i ∈ G, Tube δ' (x' i) (w i) ⊆ ball 0 1)
    (hslab : ∀ i ∈ G, ∃ p₀ ∈ Tube δ (x i) (v i), normMap a b m p₀ ∈ Tube δ' (x' i) (w i))
    (hcontr : ∀ i ∈ G, ∀ p ∈ Tube δ (x i) (v i),
      normMap a b m (c i + (b / 2) • (p - c i)) ∈ Tube δ' (x' i) (w i))
    (hclust : ∀ r ∈ R, ∀ i ∈ mem r, ∀ p ∈ Tube δ' (x' i) (w i),
        (x' r + (1 / 2 : ℝ) • w r) + ((1 : ℝ) / 1000000) • (p - (x' r + (1 / 2 : ℝ) • w r)) ∈
          Tube δ' (x' r) (w r))
    (W : Set Space) (hW : Convex ℝ W) (r0 i0 : ι) (hr0 : r0 ∈ R) (hi0 : i0 ∈ mem r0)
    (hr0W : Tube δ' (x' r0) (w r0) ⊆ W) :
    ∃ W3 : Set Space, Convex ℝ W3 ∧
      (∀ r ∈ R, Tube δ' (x' r) (w r) ⊆ W → ∀ i ∈ mem r, Tube δ (x i) (v i) ⊆ W3) ∧
      volume W3 ≤ ENNReal.ofReal (KH ^ 3 * (256 * 10 ^ 18) / (b ^ 3 * m)) * volume W := by
  set W1 := W ∩ ball (0 : Space) 1 with hW1
  have hW1c : Convex ℝ W1 := hW.inter (convex_ball _ _)
  have hW1b : W1 ⊆ ball 0 2 := fun p hp => ball_subset_ball (by norm_num) hp.2
  have hr0G : r0 ∈ G := hRG hr0
  have hW1ball : ∃ (c : Space) (r : ℝ), 0 < r ∧ ball c r ⊆ W1 :=
    ⟨x' r0, δ', hδ', fun p hp =>
      ⟨hr0W (resc_ball_sub_tube _ _ _ hp), hτ r0 hr0G (resc_ball_sub_tube _ _ _ hp)⟩⟩
  obtain ⟨W1', hW1'c, hW1'hull, hW1'vol⟩ :=
    hKH W1 1000000 hW1c hW1b hW1ball (by norm_num)
  -- every new tube of a relevant cluster lies in `W1'`
  have hτW1' : ∀ r ∈ R, Tube δ' (x' r) (w r) ⊆ W → ∀ i ∈ mem r,
      Tube δ' (x' i) (w i) ⊆ W1' := by
    intro r hr hrW i hi p hp
    have hrG := hRG hr
    have hcr : x' r + (1 / 2 : ℝ) • w r ∈ W1 :=
      ⟨hrW (resc_mid_mem_tube hδ' _ _), hτ r hrG (resc_mid_mem_tube hδ' _ _)⟩
    have hq := hclust r hr i hi p hp
    have hqW1 : (x' r + (1 / 2 : ℝ) • w r) + ((1 : ℝ) / 1000000) •
        (p - (x' r + (1 / 2 : ℝ) • w r)) ∈ W1 := ⟨hrW hq, hτ r hrG hq⟩
    have h := hW1'hull _ hcr _ hqW1
    rwa [resc_hom_cancel (by norm_num)] at h
  set K2 := normMap a b m ⁻¹' W1' ∩ ball (0 : Space) 2 with hK2
  have hK2c : Convex ℝ K2 := (resc_convex_preimage hb.ne' hW1'c).inter (convex_ball _ _)
  have hK2b : K2 ⊆ ball 0 2 := inter_subset_right
  -- contracted old tubes of relevant clusters lie in `K2`
  have hAK2 : ∀ r ∈ R, Tube δ' (x' r) (w r) ⊆ W → ∀ i ∈ mem r, ∀ p ∈ Tube δ (x i) (v i),
      c i + (b / 2) • (p - c i) ∈ K2 := by
    intro r hr hrW i hi p hp
    have hiG := hmemG r hr hi
    refine ⟨hτW1' r hr hrW i hi (hcontr i hiG p hp), ?_⟩
    rw [mem_ball_zero_iff]
    exact resc_norm_contr (by positivity) (by linarith) (hc i hiG)
      (mem_ball_zero_iff.mp (hT i hiG hp))
  have hK2ball : ∃ (c : Space) (r : ℝ), 0 < r ∧ ball c r ⊆ K2 := by
    refine ⟨c i0 + (b / 2) • (x i0 - c i0), b / 2 * δ, by positivity, ?_⟩
    intro y hy
    obtain ⟨p, hp, rfl⟩ := resc_ball_hom (by positivity) hy
    exact hAK2 r0 hr0 hr0W i0 hi0 p (resc_ball_sub_tube _ _ _ hp)
  have hlam1 : (1 : ℝ) ≤ 2 / (2 - b) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨K2', hK2'c, hK2'hull, hK2'vol⟩ := hKH K2 (2 / (2 - b)) hK2c hK2b hK2ball hlam1
  set K3 := K2' ∩ ball (0 : Space) 2 with hK3
  have hK3c : Convex ℝ K3 := hK2'c.inter (convex_ball _ _)
  have hK3b : K3 ⊆ ball 0 2 := inter_subset_right
  have hK2K3 : K2 ⊆ K3 := by
    intro p hp
    refine ⟨?_, hK2b hp⟩
    have h := hK2'hull p hp p hp
    simpa using h
  have hK3ball : ∃ (c : Space) (r : ℝ), 0 < r ∧ ball c r ⊆ K3 := by
    obtain ⟨c0, r, hr, hball⟩ := hK2ball
    exact ⟨c0, r, hr, hball.trans hK2K3⟩
  have hlam2 : (1 : ℝ) ≤ 2 / b := by
    rw [le_div_iff₀ hb]; linarith
  obtain ⟨W3, hW3c, hW3hull, hW3vol⟩ := hKH K3 (2 / b) hK3c hK3b hK3ball hlam2
  refine ⟨W3, hW3c, ?_, ?_⟩
  · intro r hr hrW i hi p hp
    have hiG := hmemG r hr hi
    obtain ⟨p₀, hp₀, hp₀τ⟩ := hslab i hiG
    have hp₀K2 : p₀ ∈ K2 :=
      ⟨hτW1' r hr hrW i hi hp₀τ, ball_subset_ball (by norm_num) (hT i hiG hp₀)⟩
    have hcK3 : c i ∈ K3 := by
      refine ⟨?_, mem_ball_zero_iff.mpr (by linarith [hc i hiG])⟩
      have h := hK2'hull p₀ hp₀K2 _ (hAK2 r hr hrW i hi p₀ hp₀)
      have h2b : (2 - b) ≠ 0 := by linarith
      rwa [resc_center_eq (k := b / 2) (lam := 2 / (2 - b))
        (by rw [div_mul_eq_mul_div, div_eq_one_iff_eq h2b]; ring)] at h
    have h := hW3hull (c i) hcK3 _ (hK2K3 (hAK2 r hr hrW i hi p hp))
    rwa [resc_hom_cancel (k := b / 2) (lam := 2 / b) (by field_simp)] at h
  · have h8 : (2 / (2 - b)) ^ 3 ≤ 8 := by
      have h0 : 0 ≤ 2 / (2 - b) := div_nonneg (by norm_num) (by linarith)
      have h2 : 2 / (2 - b) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      calc (2 / (2 - b)) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ h0 h2 3
        _ = 8 := by norm_num
    have hKH0 : 0 ≤ KH := by linarith
    calc volume W3 ≤ ENNReal.ofReal (KH * (2 / b) ^ 3) * volume K3 := hW3vol
      _ ≤ ENNReal.ofReal (KH * (2 / b) ^ 3) * volume K2' := by
          gcongr; exact inter_subset_left
      _ ≤ ENNReal.ofReal (KH * (2 / b) ^ 3) *
            (ENNReal.ofReal (KH * (2 / (2 - b)) ^ 3) * volume K2) := by gcongr
      _ ≤ ENNReal.ofReal (KH * (2 / b) ^ 3) *
            (ENNReal.ofReal (KH * (2 / (2 - b)) ^ 3) *
              (ENNReal.ofReal (4 / m) * volume W1')) := by
          gcongr; exact resc_vol_preimage hb hm _ _
      _ ≤ ENNReal.ofReal (KH * (2 / b) ^ 3) *
            (ENNReal.ofReal (KH * (2 / (2 - b)) ^ 3) *
              (ENNReal.ofReal (4 / m) * (ENNReal.ofReal (KH * 1000000 ^ 3) * volume W1))) := by
          gcongr
      _ ≤ ENNReal.ofReal (KH * (2 / b) ^ 3) *
            (ENNReal.ofReal (KH * (2 / (2 - b)) ^ 3) *
              (ENNReal.ofReal (4 / m) * (ENNReal.ofReal (KH * 1000000 ^ 3) * volume W))) := by
          gcongr; exact inter_subset_left
      _ = ENNReal.ofReal (KH * (2 / b) ^ 3 * (KH * (2 / (2 - b)) ^ 3 *
            (4 / m * (KH * 1000000 ^ 3)))) * volume W := by
          have h1 : (0:ℝ) ≤ KH * (2 / b) ^ 3 := by positivity
          have h2 : (0:ℝ) ≤ KH * (2 / (2 - b)) ^ 3 :=
            mul_nonneg hKH0 (pow_nonneg (div_nonneg (by norm_num) (by linarith)) 3)
          have h3 : (0:ℝ) ≤ 4 / m := by positivity
          rw [ENNReal.ofReal_mul h1, ENNReal.ofReal_mul h2, ENNReal.ofReal_mul h3]
          ring
      _ ≤ ENNReal.ofReal (KH ^ 3 * (256 * 10 ^ 18) / (b ^ 3 * m)) * volume W := by
          gcongr
          have e : KH * (2 / b) ^ 3 * (KH * (2 / (2 - b)) ^ 3 * (4 / m * (KH * 1000000 ^ 3))) =
              (KH ^ 3 * (32 * 10 ^ 18) / (b ^ 3 * m)) * (2 / (2 - b)) ^ 3 := by
            field_simp
            ring
          rw [e]
          calc (KH ^ 3 * (32 * 10 ^ 18) / (b ^ 3 * m)) * (2 / (2 - b)) ^ 3
              ≤ (KH ^ 3 * (32 * 10 ^ 18) / (b ^ 3 * m)) * 8 := by gcongr
            _ = KH ^ 3 * (256 * 10 ^ 18) / (b ^ 3 * m) := by ring

/-- Disjoint clusters of size `≥ N` inside a set give `N` times as many members. -/
private lemma resc_card_le {ι : Type*} [DecidableEq ι] [Fintype ι] (R : Finset ι) (N : ℕ)
    (mem : ι → Finset ι)
    (hdisj : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → Disjoint (mem r) (mem r'))
    (hN : ∀ r ∈ R, N ≤ (mem r).card)
    (P : ι → Prop) [DecidablePred P] (Q : ι → Prop) [DecidablePred Q]
    (hPQ : ∀ r ∈ R, P r → ∀ i ∈ mem r, Q i) :
    N * (R.filter P).card ≤ (Finset.univ.filter Q).card := by
  have hsub : (R.filter P).biUnion mem ⊆ Finset.univ.filter Q := by
    intro i hi
    obtain ⟨r, hr, hir⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨hrR, hrP⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ r hrR hrP i hir⟩
  have hcard : ((R.filter P).biUnion mem).card = ∑ r ∈ R.filter P, (mem r).card := by
    apply Finset.card_biUnion
    intro r hr r' hr' hne
    exact hdisj r (Finset.mem_filter.mp hr).1 r' (Finset.mem_filter.mp hr').1 hne
  calc N * (R.filter P).card = ∑ r ∈ R.filter P, N := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ r ∈ R.filter P, (mem r).card :=
        Finset.sum_le_sum (fun r hr => hN r (Finset.mem_filter.mp hr).1)
    _ = ((R.filter P).biUnion mem).card := hcard.symm
    _ ≤ (Finset.univ.filter Q).card := Finset.card_le_card hsub

/-- `log₂ |G| + 1 ≤ 8 (1 + log (1/δ))` when `|G| ≤ n ≤ δ⁻⁵`. -/
private lemma resc_log_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n g : ℕ} (hg : 0 < g)
    (hgn : g ≤ n) (hn : (n : ℝ) ≤ δ ^ (-5 : ℝ)) :
    ((Nat.log 2 g : ℕ) : ℝ) + 1 ≤ 8 * (1 + Real.log (1 / δ)) := by
  set L := Nat.log 2 g
  have h2L : (2 : ℝ) ^ L ≤ δ ^ (-5 : ℝ) := by
    have h := Nat.pow_log_le_self 2 hg.ne'
    calc (2 : ℝ) ^ L = ((2 ^ L : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (g : ℝ) := by exact_mod_cast h
      _ ≤ n := by exact_mod_cast hgn
      _ ≤ _ := hn
  have hlog : (L : ℝ) * Real.log 2 ≤ 5 * Real.log (1 / δ) := by
    have h := Real.log_le_log (by positivity) h2L
    rw [Real.log_pow, Real.log_rpow hδ] at h
    rw [one_div, Real.log_inv]
    linarith
  have hlog2 : (5 : ℝ) / 8 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hlog2 hL0]

/-- The final comparison of the counting constants. -/
private lemma resc_final_arith {A B C Λ kap N n n' g b m : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hkap : 0 < kap) (hb : 0 < b) (hm : 0 < m) (hC : 0 ≤ C) (hN : 0 ≤ N) (hn' : 0 ≤ n')
    (hkn : kap * n ≤ g) (hg : g ≤ 16 * Λ * N * n')
    (hpar : 16 * C * Λ * B ≤ kap * b ^ 3 * m * A) :
    A⁻¹ * n * (C / (b ^ 3 * m)) ≤ N * (B⁻¹ * n') := by
  have key : n * C * B ≤ N * n' * (A * (b ^ 3 * m)) := by
    have h1 : kap * (n * C * B) ≤ kap * (N * n' * (A * (b ^ 3 * m))) := by
      calc kap * (n * C * B) = (kap * n) * (C * B) := by ring
        _ ≤ (16 * Λ * N * n') * (C * B) := by
            apply mul_le_mul_of_nonneg_right (hkn.trans hg) (by positivity)
        _ = N * n' * (16 * C * Λ * B) := by ring
        _ ≤ N * n' * (kap * b ^ 3 * m * A) :=
            mul_le_mul_of_nonneg_left hpar (by positivity)
        _ = kap * (N * n' * (A * (b ^ 3 * m))) := by ring
    exact le_of_mul_le_mul_left h1 hkap
  have e1 : A⁻¹ * n * (C / (b ^ 3 * m)) = (n * C * B) / (A * (b ^ 3 * m) * B) := by
    field_simp
  have e2 : N * (B⁻¹ * n') = (N * n' * (A * (b ^ 3 * m))) / (A * (b ^ 3 * m) * B) := by
    field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right key (by positivity)

/-- The two consequences of the large hypothesis on the parameters. -/
private lemma resc_params {KH Λ A B mu kap b θ m : ℝ} (hKH1 : 1 ≤ KH) (hΛ : 1 ≤ Λ)
    (hA : 0 < A) (hA1 : A ≤ 1) (hB : 0 < B) (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hkap : 0 < kap)
    (hkap1 : kap ≤ 1) (hb : 0 < b) (hm : 0 < m) (hbm : b ≤ m) (hb1 : b ≤ 1) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hbig : 10 ^ 22 * KH ^ 3 * Λ * B ≤ (mu * kap * b * θ * A) ^ 4) :
    64 * B ≤ m * mu * b * θ ^ 2 ∧
      16 * (KH ^ 3 * (256 * 10 ^ 18)) * Λ * B ≤ kap * b ^ 3 * m * A := by
  have hX : (mu * kap * b * θ * A) ^ 4 = mu ^ 4 * kap ^ 4 * b ^ 4 * θ ^ 4 * A ^ 4 := by ring
  have hKH3 : 1 ≤ KH ^ 3 := one_le_pow₀ hKH1
  have hb3 : b ^ 3 ≤ m := by
    calc b ^ 3 ≤ b := pow_le_of_le_one hb.le hb1 (by norm_num)
      _ ≤ m := hbm
  have hbig' : (4096 * 10 ^ 18) * Λ * B ≤ 10 ^ 22 * KH ^ 3 * Λ * B := by
    have : (4096 * 10 ^ 18 : ℝ) ≤ 10 ^ 22 * KH ^ 3 := by nlinarith
    have hΛB : 0 ≤ Λ * B := by positivity
    nlinarith
  have hmu4 : mu ^ 4 ≤ mu := pow_le_of_le_one hmu.le hmu1 (by norm_num)
  have hmu4' : mu ^ 4 ≤ 1 := pow_le_one₀ hmu.le hmu1
  have hkap4 : kap ^ 4 ≤ kap := pow_le_of_le_one hkap.le hkap1 (by norm_num)
  have hkap4' : kap ^ 4 ≤ 1 := pow_le_one₀ hkap.le hkap1
  have hθ4 : θ ^ 4 ≤ θ ^ 2 := pow_le_pow_of_le_one hθ.le hθ1 (by norm_num)
  have hθ4' : θ ^ 4 ≤ 1 := pow_le_one₀ hθ.le hθ1
  have hA4 : A ^ 4 ≤ A := pow_le_of_le_one hA.le hA1 (by norm_num)
  have hA4' : A ^ 4 ≤ 1 := pow_le_one₀ hA.le hA1
  have hb4 : b ^ 4 ≤ b * m := by
    calc b ^ 4 = b * b ^ 3 := by ring
      _ ≤ b * m := mul_le_mul_of_nonneg_left hb3 hb.le
  have hb4' : b ^ 4 ≤ b ^ 3 * m := by
    calc b ^ 4 = b ^ 3 * b := by ring
      _ ≤ b ^ 3 * m := mul_le_mul_of_nonneg_left hbm (by positivity)
  constructor
  · have h1 : mu ^ 4 * kap ^ 4 * b ^ 4 * θ ^ 4 * A ^ 4 ≤ mu * 1 * (b * m) * θ ^ 2 * 1 := by
      refine mul_le_mul ?_ hA4' (by positivity) (by positivity)
      refine mul_le_mul ?_ hθ4 (by positivity) (by positivity)
      refine mul_le_mul ?_ hb4 (by positivity) (by positivity)
      exact mul_le_mul hmu4 hkap4' (by positivity) (by positivity)
    have h64 : 64 * B ≤ 4096 * 10 ^ 18 * Λ * B := by nlinarith
    nlinarith
  · have h1 : mu ^ 4 * kap ^ 4 * b ^ 4 * θ ^ 4 * A ^ 4 ≤ 1 * kap * (b ^ 3 * m) * 1 * A := by
      refine mul_le_mul ?_ hA4 (by positivity) (by positivity)
      refine mul_le_mul ?_ hθ4' (by positivity) (by positivity)
      refine mul_le_mul ?_ hb4' (by positivity) (by positivity)
      exact mul_le_mul hmu4' hkap4 (by positivity) (by positivity)
    nlinarith

theorem rescale : ∃ K : ℝ, 1 ≤ K ∧ ∀ (η ηs δ θ a b m mu kap s : ℝ), 0 < η → 0 < ηs →
    0 < δ → δ ≤ 1 / 100 → 0 < θ → θ ≤ 1 → 400 * δ ≤ θ → 0 < b → 4 * b ≤ θ → 100 * δ ≤ b →
    0 < m → m ≤ 1 → 200 * b ≤ m → |a| + 2 * b ≤ 1 → 0 < mu → mu ≤ 1 → 0 < kap → kap ≤ 1 →
    0 ≤ s →
    K * (1 + Real.log (1 / δ)) * (4 * δ / θ) ^ ηs ≤ (mu * kap * b * θ * δ ^ η) ^ 4 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n → (n : ℝ) ≤ δ ^ (-5 : ℝ) →
    Family δ n x v Y → (∀ i, IsCompact (Y i)) → GlobalCount η δ n x v →
    ∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
    (∀ t ∈ Icc (a - 2 * b) (a + 2 * b),
      m ≤ |deriv f t| ∧ |deriv f t| ≤ 2 * m ∧ |deriv (deriv f) t| ≤ 1) →
    (∀ z ∈ Icc (a - 2 * b) (a + 2 * b), volume (PS f (⋃ i, Y i) z) ≤ ENNReal.ofReal s) →
    ∀ G : Finset (Fin n), kap * n ≤ G.card → (∀ i ∈ G, θ ≤ |v i 2|) →
    (∀ i ∈ G, ENNReal.ofReal (mu * b * δ ^ 2) ≤ volume (Y i ∩ {q | |q 2 - a| ≤ b / 2})) →
    ∃ (n' : ℕ) (x' v' : Fin n' → Space) (Y' : Fin n' → Set Space),
      Dense ηs (4 * δ / θ) n' x' v' Y' ∧ (∀ i, IsCompact (Y' i)) ∧
      (∀ i, (1 / 2 : ℝ) ≤ |v' i 2|) ∧ GlobalCount ηs (4 * δ / θ) n' x' v' ∧
      ∃ g : ℝ → ℝ, (ContDiff ℝ 2 g ∧ ∀ z ∈ Icc (-1 : ℝ) 1,
          1 ≤ |deriv g z| ∧ |deriv g z| ≤ 2 ∧ |deriv (deriv g) z| ≤ (1 / 100 : ℝ)) ∧
        ∀ z ∈ Icc (-1 : ℝ) 1, volume (PS g (⋃ i, Y' i) z) ≤ ENNReal.ofReal (s / 2) := by
  classical
  obtain ⟨KH, hKH1, hKH⟩ := homothety_hull
  refine ⟨10 ^ 22 * KH ^ 3, ?_, ?_⟩
  · have : (1 : ℝ) ≤ KH ^ 3 := one_le_pow₀ hKH1
    nlinarith
  intro η ηs δ θ a b m mu kap s hη hηs hδ hδ1 hθ hθ1 hδθ hb hbθ hδb hm hm1 hbm ha hmu hmu1
    hkap hkap1 hs hbig n x v Y hn hnδ hfam hYc hGC f hf hderiv hslice G hGcard hGθ hGmass
  -- basic parameter facts
  have hb1 : b ≤ 1 := by linarith
  have ha1 : |a| ≤ 1 := by linarith
  have hδ'0 : 0 < 4 * δ / θ := by positivity
  have hδ'1 : 4 * δ / θ ≤ 1 / 100 := by rw [div_le_iff₀ hθ]; linarith
  have hδ'lt : 2 * δ / θ < 4 * δ / θ := by
    apply div_lt_div_of_pos_right _ hθ; linarith
  have hΛ : 1 ≤ 1 + Real.log (1 / δ) := by
    have : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    linarith
  have hA : 0 < δ ^ η := Real.rpow_pos_of_pos hδ η
  have hA1 : δ ^ η ≤ 1 := Real.rpow_le_one hδ.le (by linarith) hη.le
  have hB : 0 < (4 * δ / θ) ^ ηs := Real.rpow_pos_of_pos hδ'0 ηs
  have hpar := resc_params hKH1 hΛ hA hA1 hB hmu hmu1 hkap hkap1 hb hm (by linarith) hb1 hθ
    hθ1 hbig
  set slab : Set Space := {q : Space | |q 2 - a| ≤ b / 2} with hslab_def
  have hslabc : IsClosed slab := isClosed_le (by fun_prop) continuous_const
  -- each tube of `G` meets the central slab
  have hmeet : ∀ i ∈ G, (Tube δ (x i) (v i) ∩ slab).Nonempty := by
    intro i hi
    have hpos : (0 : ℝ≥0∞) < volume (Y i ∩ slab) :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) (hGmass i hi)
    obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact ⟨p, hfam.sub i hp.1, hp.2⟩
  -- the new tubes
  have hex : ∀ i : Fin n, ∃ x' w c : Space, i ∈ G → (‖w‖ = 1 ∧ (1 / 2 : ℝ) ≤ |w 2| ∧
      ‖c‖ ≤ 3 / 2 ∧ Tube (4 * δ / θ) x' w ⊆ ball 0 1 ∧
      normMap a b m '' (Tube δ (x i) (v i) ∩ slab) ⊆
        cthickening (2 * δ / θ) (segment ℝ x' (x' + w)) ∧
      ∀ p ∈ Tube δ (x i) (v i), c + (b / 2) • (p - c) ∈
        normMap a b m ⁻¹' Tube (4 * δ / θ) x' w) := by
    intro i
    by_cases hi : i ∈ G
    · obtain ⟨x', w, c, h⟩ := rescale_tube hδ hb hm hm1 hbθ hθ1 hδb hδθ ha1 (hfam.unit i)
        (hGθ i hi) (hfam.ball i) (hmeet i hi)
      exact ⟨x', w, c, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hi⟩
  choose x' w c hxwc using hex
  have hslab' : ∀ i ∈ G, ∃ p₀ ∈ Tube δ (x i) (v i),
      normMap a b m p₀ ∈ Tube (4 * δ / θ) (x' i) (w i) := by
    intro i hi
    obtain ⟨p₀, hp₀⟩ := hmeet i hi
    exact ⟨p₀, hp₀.1, cthickening_subset_thickening' hδ'0 hδ'lt _
      ((hxwc i hi).2.2.2.2.1 ⟨p₀, hp₀, rfl⟩)⟩
  have hcontr' : ∀ i ∈ G, ∀ p ∈ Tube δ (x i) (v i),
      normMap a b m (c i + (b / 2) • (p - c i)) ∈ Tube (4 * δ / θ) (x' i) (w i) :=
    fun i hi p hp => (hxwc i hi).2.2.2.2.2 p hp
  have hGne : G.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < G.card := lt_of_lt_of_le (by positivity) hGcard
    exact_mod_cast this
  obtain ⟨R, N, mem, hRG, hRne, hN, hmemG, hdisj, hNcard, hGR, hsep, hclust⟩ :=
    select_clusters hδ'0 hδ'1 G hGne x' w (fun i hi => (hxwc i hi).1)
  have hYcomp : ∀ k : Fin R.card, IsCompact (normMap a b m '' (Y (enumerate R k) ∩ slab)) :=
    fun k => ((hYc _).inter_right hslabc).image (continuous_normMap a b m)
  refine ⟨R.card, fun k => x' (enumerate R k), fun k => w (enumerate R k),
    fun k => normMap a b m '' (Y (enumerate R k) ∩ slab), ?_, hYcomp, ?_, ?_,
    normSlope a b m f, normSlope_bounds hb hm hbm hf hderiv, ?_⟩
  · -- the new family is dense
    refine ⟨Finset.card_pos.mpr hRne, fun k => (hxwc _ (hRG (enumerate_mem R k))).1,
      fun k => (hxwc _ (hRG (enumerate_mem R k))).2.2.2.1, ?_, ?_, ?_, ?_⟩
    · intro k k' hkk'
      exact hsep _ (enumerate_mem R k) _ (enumerate_mem R k') ((enumerate_injective R).ne hkk')
    · intro k
      exact (hYcomp k).measurableSet
    · intro k
      have hkG := hRG (enumerate_mem R k)
      calc normMap a b m '' (Y (enumerate R k) ∩ slab)
          ⊆ normMap a b m '' (Tube δ (x (enumerate R k)) (v (enumerate R k)) ∩ slab) :=
            image_mono (inter_subset_inter_left _ (hfam.sub _))
        _ ⊆ cthickening (2 * δ / θ) (segment ℝ (x' (enumerate R k))
              (x' (enumerate R k) + w (enumerate R k))) := (hxwc _ hkG).2.2.2.2.1
        _ ⊆ _ := cthickening_subset_thickening' hδ'0 hδ'lt _
    · have hvolk : ∀ k : Fin R.card, ENNReal.ofReal (m / 4 * (mu * b * δ ^ 2)) ≤
          volume (normMap a b m '' (Y (enumerate R k) ∩ slab)) := by
        intro k
        rw [volume_normMap_image hb hm, ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact hGmass _ (hRG (enumerate_mem R k))
      calc ENNReal.ofReal ((4 * δ / θ) ^ ηs * (R.card : ℝ) * (4 * δ / θ) ^ 2)
          ≤ ENNReal.ofReal ((R.card : ℝ) * (m / 4 * (mu * b * δ ^ 2))) := by
            apply ENNReal.ofReal_le_ofReal
            have e1 : (4 * δ / θ) ^ ηs * (R.card : ℝ) * (4 * δ / θ) ^ 2 =
                ((R.card : ℝ) * δ ^ 2 / θ ^ 2) * (16 * (4 * δ / θ) ^ ηs) := by
              field_simp
              ring
            have e2 : (R.card : ℝ) * (m / 4 * (mu * b * δ ^ 2)) =
                ((R.card : ℝ) * δ ^ 2 / θ ^ 2) * (m * mu * b * θ ^ 2 / 4) := by
              field_simp
            rw [e1, e2]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [hpar.1]
        _ = ∑ k : Fin R.card, ENNReal.ofReal (m / 4 * (mu * b * δ ^ 2)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
        _ ≤ ∑ k, volume (normMap a b m '' (Y (enumerate R k) ∩ slab)) :=
            Finset.sum_le_sum (fun k _ => hvolk k)
  · intro k
    exact (hxwc _ (hRG (enumerate_mem R k))).2.1
  · -- the global convex count
    intro W hW
    have hcount : ncard {k : Fin R.card |
        Tube (4 * δ / θ) (x' (enumerate R k)) (w (enumerate R k)) ⊆ W} =
        (R.filter (fun r => Tube (4 * δ / θ) (x' r) (w r) ⊆ W)).card :=
      enumerate_count R (fun r => Tube (4 * δ / θ) (x' r) (w r) ⊆ W)
    show ENNReal.ofReal (ncard {k : Fin R.card |
        Tube (4 * δ / θ) (x' (enumerate R k)) (w (enumerate R k)) ⊆ W} : ℝ) ≤
      ENNReal.ofReal ((4 * δ / θ) ^ (-ηs) * (R.card : ℝ)) * volume W
    rw [hcount]
    rcases (R.filter (fun r => Tube (4 * δ / θ) (x' r) (w r) ⊆ W)).eq_empty_or_nonempty
      with hrel | hrel
    · rw [hrel]
      simp
    obtain ⟨r0, hr0⟩ := hrel
    obtain ⟨hr0R, hr0W⟩ := Finset.mem_filter.mp hr0
    obtain ⟨i0, hi0⟩ : (mem r0).Nonempty :=
      Finset.card_pos.mp (lt_of_lt_of_le hN (hNcard r0 hr0R).1)
    obtain ⟨W3, hW3c, hW3T, hW3vol⟩ := resc_hull hKH1 hKH hδ hδ'0 hb hb1 hm x v x' w c G R mem
      hRG hmemG (fun i _ => hfam.ball i) (fun i hi => (hxwc i hi).2.2.1)
      (fun i hi => (hxwc i hi).2.2.2.1) hslab' hcontr' hclust W hW r0 i0 hr0R hi0 hr0W
    have hcard := resc_card_le R N mem hdisj (fun r hr => (hNcard r hr).1)
      (fun r => Tube (4 * δ / θ) (x' r) (w r) ⊆ W) (fun i => Tube δ (x i) (v i) ⊆ W3)
      (fun r hr hrW i hi => hW3T r hr hrW i hi)
    have hGC3 := hGC W3 hW3c
    rw [ncard_setOf] at hGC3
    -- the arithmetic of the parameters
    have hGn : G.card ≤ n := by
      simpa using Finset.card_le_univ G
    have hlog := resc_log_bound hδ (by linarith) (Finset.card_pos.mpr hGne) hGn hnδ
    have hGR' : (G.card : ℝ) ≤ 16 * (1 + Real.log (1 / δ)) * N * R.card := by
      have h1 : (G.card : ℝ) ≤ 2 * ((Nat.log 2 G.card : ℕ) + 1 : ℝ) * N * R.card := by
        exact_mod_cast hGR
      have hNR : (0 : ℝ) ≤ N * R.card := by positivity
      calc (G.card : ℝ) ≤ 2 * ((Nat.log 2 G.card : ℕ) + 1 : ℝ) * N * R.card := h1
        _ = 2 * ((Nat.log 2 G.card : ℕ) + 1 : ℝ) * (N * R.card) := by ring
        _ ≤ 2 * (8 * (1 + Real.log (1 / δ))) * (N * R.card) := by gcongr
        _ = 16 * (1 + Real.log (1 / δ)) * N * R.card := by ring
    have harith := resc_final_arith (A := δ ^ η) (B := (4 * δ / θ) ^ ηs)
      (C := KH ^ 3 * (256 * 10 ^ 18)) (N := (N : ℝ)) (n := (n : ℝ)) (n' := (R.card : ℝ))
      hA hB hkap hb hm (by positivity) (by positivity) (by positivity) hGcard hGR' hpar.2
    rw [← Real.rpow_neg hδ.le, ← Real.rpow_neg hδ'0.le] at harith
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hNne : ENNReal.ofReal (N : ℝ) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact hNpos
    rw [← ENNReal.mul_le_mul_iff_right hNne ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (N : ℝ) *
          ENNReal.ofReal ((R.filter (fun r => Tube (4 * δ / θ) (x' r) (w r) ⊆ W)).card : ℝ)
        = ENNReal.ofReal ((N * (R.filter (fun r => Tube (4 * δ / θ) (x' r) (w r) ⊆ W)).card :
            ℕ) : ℝ) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          push_cast
          ring_nf
      _ ≤ ENNReal.ofReal ((Finset.univ.filter (fun i => Tube δ (x i) (v i) ⊆ W3)).card : ℝ) :=
          ENNReal.ofReal_le_ofReal (by exact_mod_cast hcard)
      _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W3 := hGC3
      _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) *
            (ENNReal.ofReal (KH ^ 3 * (256 * 10 ^ 18) / (b ^ 3 * m)) * volume W) := by
          gcongr
      _ = ENNReal.ofReal (δ ^ (-η) * (n : ℝ) * (KH ^ 3 * (256 * 10 ^ 18) / (b ^ 3 * m))) *
            volume W := by
          rw [ENNReal.ofReal_mul (p := δ ^ (-η) * (n : ℝ)) (by positivity), mul_assoc]
      _ ≤ ENNReal.ofReal ((N : ℝ) * ((4 * δ / θ) ^ (-ηs) * (R.card : ℝ))) * volume W := by
          gcongr
      _ = ENNReal.ofReal (N : ℝ) *
            (ENNReal.ofReal ((4 * δ / θ) ^ (-ηs) * (R.card : ℝ)) * volume W) := by
          rw [ENNReal.ofReal_mul (p := (N : ℝ)) (by positivity), mul_assoc]
  · -- the slices of the normalized slope
    intro z hz
    have hsub : (⋃ k, normMap a b m '' (Y (enumerate R k) ∩ slab)) ⊆
        normMap a b m '' (⋃ i, Y i) := by
      refine iUnion_subset fun k => image_mono ?_
      exact inter_subset_left.trans (subset_iUnion Y _)
    have hz' : a + 2 * b * z ∈ Icc (a - 2 * b) (a + 2 * b) := by
      constructor <;> nlinarith [hz.1, hz.2]
    calc volume (PS (normSlope a b m f) (⋃ k, normMap a b m '' (Y (enumerate R k) ∩ slab)) z)
        ≤ volume (PS (normSlope a b m f) (normMap a b m '' (⋃ i, Y i)) z) :=
          measure_mono (ps_mono hsub z)
      _ ≤ ENNReal.ofReal (s / 2) := volume_PS_normMap_le hb hm f _ z s (hslice _ hz')

end WangZahlLot.Obl.wz_grains_nonsingular_slices
