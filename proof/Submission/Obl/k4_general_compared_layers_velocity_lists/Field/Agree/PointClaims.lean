-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.PointClaims; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Claims

/-!
# The pointwise claims of coefficient agreement (paper Prop. 8.4)

See `Claims.lean` for the setting. Numeric hypotheses at one index:
`hfz : 8·10⁶ K¹¹ N^(m/1000) (δb + χ) ≤ a₁` (all freezing errors are below `a₁ / 8`) and
`hδbχ : 2 (K + 1) δb ≤ χ`, with `χ = N^(-m)` and `a₁ = N^(-(r+u))`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- The representative point of the native state of an incidence of block `Q` is close to it. -/
theorem agree_rep_close {k : ℕ} {r R : ℝ} (hat : p.AtDepth k r R) {Q : Fin (p.n k r)} {δb δs : ℝ}
    (hδb : 0 < δb) {ω : α × ℝ} (ht : ω.2 ∈ block (p.T k r) (p.j k r Q)) :
    0 ≤ ω.2 - p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω) ∧
      ω.2 - p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω) ≤ δb ∧
      0 ≤ p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω) ∧
      p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω) ≤ 1 ∧
      |p.x k ω.1 ω.2 1 - p.agRepZ k r Q δb (p.nativeState k r Q δb δs ω)| ≤ (p.K k + 1) * δb := by
  obtain ⟨hτ0, hτ1⟩ := agree_tauN_mem_unit (p := p) ht
  have hq := agree_blockLen_pos (p := p) k r
  have hq1 := agree_blockLen_le_one (p := p) k r
  set c := ⌊p.tauN k r Q ω / δb⌋ with hc
  have hlo := (le_div_iff₀ hδb).mp (Int.floor_le (p.tauN k r Q ω / δb))
  have hhi := (div_lt_iff₀ hδb).mp (Int.lt_floor_add_one (p.tauN k r Q ω / δb))
  have hc0 : (0 : ℝ) ≤ c := by
    have : (0 : ℤ) ≤ c := Int.floor_nonneg.mpr (div_nonneg hτ0 hδb.le)
    exact_mod_cast this
  have hrep : p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω) =
      p.blockStart k r Q + p.blockLen k r * ((c : ℝ) * δb) := rfl
  have hdiff : ω.2 - p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω) =
      p.blockLen k r * (p.tauN k r Q ω - (c : ℝ) * δb) := by
    rw [hrep]
    have h := agree_tauN_mul_add Q ω
    linear_combination h
  have hst := agree_blockStart_nonneg (p := p) k r Q
  have hst1 := agree_blockStart_add_le_one (p := p) k r Q
  have hd0 : 0 ≤ ω.2 - p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω) := by
    rw [hdiff]
    exact mul_nonneg hq.le (by linarith)
  have hd1 : ω.2 - p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω) ≤ δb := by
    rw [hdiff]
    have h1 : p.tauN k r Q ω - (c : ℝ) * δb ≤ δb := by linarith
    calc _ ≤ 1 * δb := mul_le_mul hq1 h1 (by linarith) zero_le_one
      _ = δb := one_mul δb
  refine ⟨hd0, hd1, ?_, ?_, ?_⟩
  · rw [hrep]
    have : 0 ≤ p.blockLen k r * ((c : ℝ) * δb) := mul_nonneg hq.le (mul_nonneg hc0 hδb.le)
    linarith
  · rw [hrep]
    have h1 : (c : ℝ) * δb ≤ 1 := by linarith
    have : p.blockLen k r * ((c : ℝ) * δb) ≤ p.blockLen k r * 1 :=
      mul_le_mul_of_nonneg_left h1 hq.le
    linarith
  · -- the major coordinate
    have hz := agree_abs_sub_bin_le hδb (rfl : ⌊p.zetaN k r Q ω / δb⌋ = ⌊p.zetaN k r Q ω / δb⌋)
    have hrepZ : p.agRepZ k r Q δb (p.nativeState k r Q δb δs ω) =
        p.c k r Q 0 + p.c k r Q 1 * p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω) +
          p.blockLen k r * ((⌊p.zetaN k r Q ω / δb⌋ : ℝ) * δb) := rfl
    rw [agree_zetaN_mul_add Q ω, hrepZ]
    have hc1 := hat.agree_coeff_le Q 1
    have hK0 : 0 ≤ p.K k := (abs_nonneg _).trans hc1
    have : p.c k r Q 0 + p.c k r Q 1 * ω.2 + p.blockLen k r * p.zetaN k r Q ω -
        (p.c k r Q 0 + p.c k r Q 1 * p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω) +
          p.blockLen k r * ((⌊p.zetaN k r Q ω / δb⌋ : ℝ) * δb)) =
        p.c k r Q 1 * (ω.2 - p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω)) +
          p.blockLen k r * (p.zetaN k r Q ω - (⌊p.zetaN k r Q ω / δb⌋ : ℝ) * δb) := by ring
    rw [this]
    calc _ ≤ |p.c k r Q 1 * (ω.2 - p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω))| +
          |p.blockLen k r * (p.zetaN k r Q ω - (⌊p.zetaN k r Q ω / δb⌋ : ℝ) * δb)| :=
          abs_add_le _ _
      _ = |p.c k r Q 1| * |ω.2 - p.agRepTime k r Q δb (p.nativeState k r Q δb δs ω)| +
          p.blockLen k r * |p.zetaN k r Q ω - (⌊p.zetaN k r Q ω / δb⌋ : ℝ) * δb| := by
          rw [abs_mul, abs_mul, abs_of_pos hq]
      _ ≤ p.K k * δb + 1 * δb := by
          gcongr
          rw [abs_of_nonneg hd0]
          exact hd1
      _ = _ := by ring

/-- A distance numeric: `δb (1 + 2K + K²) + 2 K χ ≤ 8 K² (δb + χ)`. -/
theorem agree_dist_numeric {K δb χ : ℝ} (hK1 : 1 ≤ K) (hδb : 0 ≤ δb) (hχ : 0 ≤ χ) {x : ℝ}
    (hx : x ≤ 2 * δb * (1 + 2 * K + K ^ 2) + 2 * K * χ) : x ≤ 8 * K ^ 2 * (δb + χ) := by
  nlinarith [mul_nonneg hδb (sq_nonneg (K - 1)), mul_nonneg hχ (sub_nonneg.mpr hK1),
    mul_nonneg hδb (sub_nonneg.mpr hK1), mul_nonneg hχ (mul_nonneg (sub_nonneg.mpr hK1)
      (sub_nonneg.mpr hK1))]

/-- The distance numeric for a point and a freezing point. -/
theorem agree_dist_src {K δb χ dt dY dZ : ℝ} (hK1 : 1 ≤ K) (hδb : 0 ≤ δb) (hχ : 0 ≤ χ)
    (hdt0 : 0 ≤ dt) (hdt : dt ≤ 2 * δb) (hdZ0 : 0 ≤ dZ)
    (hdZ : dZ ≤ 2 * χ + 2 * (K + 1) * δb) (hdY : dY ≤ K * dt + K * dZ) :
    dt + dY ≤ 8 * K ^ 2 * (δb + χ) := by
  have hK0 : 0 ≤ K := by linarith
  have h1 := mul_le_mul_of_nonneg_left hdt hK0
  have h2 := mul_le_mul_of_nonneg_left hdZ hK0
  nlinarith [mul_nonneg hδb (sq_nonneg (K - 1)), mul_nonneg hχ (sub_nonneg.mpr hK1),
    mul_nonneg hδb (sub_nonneg.mpr hK1), mul_nonneg hχ hK0, mul_nonneg hδb hK0]

/-- `8 K² ≤ 8·10⁶ K¹¹ B` for `K, B ≥ 1`. -/
theorem agree_small_numeric {K B : ℝ} (hK1 : 1 ≤ K) (hB1 : 1 ≤ B) :
    8 * K ^ 2 ≤ 8000000 * K ^ 11 * B := by
  have hK2 : K ^ 2 ≤ K ^ 11 := pow_le_pow_right₀ hK1 (by norm_num)
  have hK11 : 1 ≤ K ^ 11 := one_le_pow₀ hK1
  have h3 : K ^ 11 ≤ K ^ 11 * B := le_mul_of_one_le_right (by linarith) hB1
  nlinarith

namespace ComparedSample

variable {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)

theorem agree_coeff_coarse (i : Fin (s.layers 0).count) :
    ∀ b, |((s.layers 0).G i).coeff b| ≤ p.N k ^ (m / 1000) :=
  fun b => s.coefficient_bound 0 i b

/-- Same parent and same label for two incidences of one combined state. -/
theorem agree_state_parent {δb δs : ℝ} {M : ℕ} {e : Fin (s.count 0)} {ω : α × ℝ}
    (hωe : ω ∈ s.event 0 e) {Q : Fin (p.n k r)} {σ : {σ : Fin 4 → ℤ // σ ∈ agStateBox M}}
    (hq : s.agStF δb δs M ω = some (Q, σ)) :
    s.parent 0 e = Q ∧ p.nativeState k r Q δb δs ω = σ.1 := by
  obtain ⟨hωQ, hσ⟩ := s.agree_stF_eq_some_iff.mp hq
  exact ⟨s.agree_evQ_eq_of_mem (s.agree_mem_evQ_of_mem_event hωe) hωQ, hσ⟩

theorem agree_label_eq {e : Fin (s.count 0)} {ω : α × ℝ} (hωe : ω ∈ s.event 0 e)
    {i' : Fin (s.layers 0).count} (hi' : ω.1 ∈ (s.layers 0).C i') : s.coarse 0 e = i' := by
  have h1 := s.agree_entF_eq_some_iff.mpr (s.agree_event_data0 hωe).2.2.2.1
  have h2 := s.agree_entF_eq_some_iff.mpr hi'
  rw [h1] at h2
  exact Option.some_inj.mp h2

/-- **Claim 1: matching.** -/
theorem agree_claim_match {R : ℝ} (hat : p.AtDepth k r R) (hN1 : 1 ≤ p.N k) (hK1 : 1 ≤ p.K k)
    (hKH : p.K k ≤ H) (hℓr : 0 ≤ p.ℓ * r) (hm : 0 ≤ m) (hru : 0 ≤ r + u) {δb : ℝ}
    (hδb : 0 < δb) (hχ1 : p.N k ^ (-m) ≤ 1)
    (hfz : 8000000 * p.K k ^ 11 * p.N k ^ (m / 1000) * (δb + p.N k ^ (-m)) ≤
      p.N k ^ (-(r + u)))
    {M : ℕ} {e : Fin (s.count 0)} {c : ℤ} {ω ω' : α × ℝ} (hω : ω ∈ s.agSrc δb e c)
    (hω' : ω' ∈ s.agGood) {i' : Fin (s.layers 0).count} (hi' : ω'.1 ∈ (s.layers 0).C i')
    {q : Fin (p.n k r) × {σ : Fin 4 → ℤ // σ ∈ agStateBox M}}
    (hq : s.agStF δb (p.N k ^ (-(r + u))) M ω = some q)
    (hq' : s.agStF δb (p.N k ^ (-(r + u))) M ω' = some q) :
    p.uN k r (s.parent 0 e) ω ∈ Kernels.matchSet (s.agSrcPoly δb e c) (s.agTgtPoly δb e c i')
      (s.agTgtOffsets e i') (6 * H * p.N k ^ (-(r + u))) (p.K k) := by
  have hN : 0 < p.N k := by linarith
  have hH1 : 1 ≤ H := by linarith [s.loss_one]
  have ha : 0 < p.N k ^ (-(r + u)) := Real.rpow_pos_of_pos hN _
  have ha1 : p.N k ^ (-(r + u)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hχ : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  have hB1 : 1 ≤ p.N k ^ (m / 1000) := Real.one_le_rpow hN1 (by positivity)
  have hB0 : 0 ≤ p.N k ^ (m / 1000) := by linarith
  set a := p.N k ^ (-(r + u)) with ha_def
  set χ := p.N k ^ (-m) with hχ_def
  set B := p.N k ^ (m / 1000) with hB_def
  set K := p.K k with hK_def
  set D := δb + χ with hD_def
  have hD0 : 0 ≤ D := by positivity
  have hD1 : 8 * K ^ 2 * D ≤ 1 := by
    have h1 : 8 * K ^ 2 * D ≤ 8000000 * K ^ 11 * B * D :=
      mul_le_mul_of_nonneg_right (agree_small_numeric hK1 hB1) hD0
    linarith
  obtain ⟨Q, σ⟩ := q
  have hωe : ω ∈ s.event 0 e := hω.1
  obtain ⟨hQ, hσ⟩ := s.agree_state_parent hωe hq
  obtain ⟨e', hω'e'⟩ := s.agree_good_event hω'
  obtain ⟨hQ', hσ'⟩ := s.agree_state_parent hω'e' hq'
  have hi'e := s.agree_label_eq hω'e' hi'
  obtain ⟨hct, hcZ, hcU, hcX⟩ := s.agree_same_state_close hat hδb ha hq hq'
  dsimp only at hcU
  subst hQ
  subst hi'e
  obtain ⟨hgood, hB, ht, hC, hF⟩ := s.agree_event_data0 hωe
  obtain ⟨hgood', hB', ht', hC', hF'⟩ := s.agree_event_data0 hω'e'
  rw [hQ'] at hB' ht'
  have hunit := agree_block_subset_unit k r _ ht
  have hunit' := agree_block_subset_unit k r _ ht'
  have htabs : |ω.2| ≤ 1 := abs_le.mpr ⟨by linarith [hunit.1], hunit.2⟩
  have htabs' : |ω'.2| ≤ 1 := abs_le.mpr ⟨by linarith [hunit'.1], hunit'.2⟩
  obtain ⟨-, hU⟩ := hat.agree_normalized_le hN _ hB ht
  obtain ⟨-, hU'⟩ := hat.agree_normalized_le hN _ hB' ht'
  have hfit := s.agree_event_fit hat hN hKH hωe
  have hfit' := s.agree_event_fit hat hN hKH hω'e'
  rw [hQ'] at hfit'
  have hZ : |p.x k ω.1 ω.2 1| ≤ K := by
    simpa using baseGood_base_bound p hK1 hgood 1
  have hZ' : |p.x k ω'.1 ω'.2 1| ≤ K := by
    simpa using baseGood_base_bound p hK1 hgood' 1
  obtain ⟨hts0, hts1, hts2, hts3⟩ := s.agree_src_time hδb hω
  have htsabs : |s.agSrcTime δb e c| ≤ 1 := abs_le.mpr ⟨by linarith, hts3⟩
  have hZs := s.agree_src_Z hN hχ1 hδb hω
  set Qb := s.parent 0 e with hQb
  set ts := s.agSrcTime δb e c with hts_def
  set Zs := s.agSrcZ δb e c with hZs_def
  set Y := p.tiltY k r Qb with hY_def
  set w := p.blockWidth k r with hw_def
  have hw0 : 0 ≤ w := (agree_blockWidth_pos (p := p) r hN).le
  have hw1 : |w| ≤ 1 := by rw [abs_of_nonneg hw0]; exact agree_blockWidth_le_one hN1 hℓr
  have hYt : |Y ω.2 (p.x k ω.1 ω.2 1)| ≤ 3 * K ^ 2 := hat.agree_tiltY_abs_le hK1 Qb htabs hZ
  have hYt' : |Y ω'.2 (p.x k ω'.1 ω'.2 1)| ≤ 3 * K ^ 2 := hat.agree_tiltY_abs_le hK1 Qb htabs' hZ'
  -- distances to the freezing point
  have hK0 : 0 ≤ K := by linarith
  have hρ1 : |ω.2 - ts| + |Y ω.2 (p.x k ω.1 ω.2 1) - Y ts Zs| ≤ 8 * K ^ 2 * D := by
    have h1 := hat.agree_tiltY_sub_le Qb ω.2 (p.x k ω.1 ω.2 1) ts Zs
    have h2 : |ω.2 - ts| ≤ δb := by rw [abs_of_nonneg hts0]; exact hts1
    have hKδ : 0 ≤ (K + 1) * δb := by positivity
    exact agree_dist_src hK1 hδb.le hχ.le (abs_nonneg _) (by linarith) (abs_nonneg _)
      (by linarith) h1
  have hρ2 : |ω'.2 - ts| + |Y ω'.2 (p.x k ω'.1 ω'.2 1) - Y ts Zs| ≤ 8 * K ^ 2 * D := by
    have h1 := hat.agree_tiltY_sub_le Qb ω'.2 (p.x k ω'.1 ω'.2 1) ts Zs
    have h2 : |ω'.2 - ts| ≤ 2 * δb := by
      have : |ω.2 - ts| ≤ δb := by rw [abs_of_nonneg hts0]; exact hts1
      calc |ω'.2 - ts| ≤ |ω'.2 - ω.2| + |ω.2 - ts| := abs_sub_le _ _ _
        _ ≤ δb + δb := by rw [abs_sub_comm]; gcongr
        _ = 2 * δb := by ring
    have h2' : |p.x k ω'.1 ω'.2 1 - Zs| ≤ 2 * χ + 2 * (K + 1) * δb := by
      calc _ ≤ |p.x k ω'.1 ω'.2 1 - p.x k ω.1 ω.2 1| + |p.x k ω.1 ω.2 1 - Zs| :=
            abs_sub_le _ _ _
        _ ≤ (K + 1) * δb + (2 * χ + (K + 1) * δb) := by rw [abs_sub_comm]; gcongr
        _ = _ := by ring
    exact agree_dist_src hK1 hδb.le hχ.le (abs_nonneg _) h2 (abs_nonneg _) h2' h1
  have hYs : |Y ts Zs| ≤ 4 * K ^ 2 := by
    have h1 : |Y ts Zs| ≤ |Y ω.2 (p.x k ω.1 ω.2 1)| + |Y ω.2 (p.x k ω.1 ω.2 1) - Y ts Zs| := by
      have := abs_sub_abs_le_abs_sub (Y ts Zs) (Y ω.2 (p.x k ω.1 ω.2 1))
      rw [abs_sub_comm (Y ts Zs)] at this
      linarith
    have h2 := abs_nonneg (ω.2 - ts)
    have hKsq : 1 ≤ K ^ 2 := one_le_pow₀ hK1
    linarith
  -- freezing
  have hG := s.agree_totalDegree_coarse (s.coarse 0 e)
  have hG' := s.agree_totalDegree_coarse (s.coarse 0 e')
  obtain ⟨hA1, hB1'⟩ := agree_freeze_bounds _ hG hB0 (s.agree_coeff_coarse _) hK1 Y hw1 htabs htsabs
    (hYt.trans (by linarith [sq_nonneg K])) hYs hD0 hρ1
  obtain ⟨hA2, hB2⟩ := agree_freeze_bounds _ hG' hB0 (s.agree_coeff_coarse _) hK1 Y hw1 htabs' htsabs
    (hYt'.trans (by linarith [sq_nonneg K])) hYs hD0 hρ2
  have hBs := agree_transB_abs_le_K _ hG' hB0 (s.agree_coeff_coarse _) hK1 Y hw1 htsabs hYs
  have hDs := agree_transD_abs_le_one _ hG' hB0 (s.agree_coeff_coarse _) hw1
  have htot := agree_freeze_total hK1 hB0 hD0 hδb.le (by linarith : δb ≤ D) hA1 hB1' hA2 hB2 hBs hDs
    (abs_nonneg _) (abs_nonneg _)
  have hmatch := agree_tilted_match ((s.layers 0).G (s.coarse 0 e)) ((s.layers 0).G (s.coarse 0 e'))
    hG hG' Y w hfit hfit' hcX hcU hU hU' htot
  -- conclude
  refine ⟨⟨by linarith [(abs_le.mp hU).1], (abs_le.mp hU).2⟩,
    s.offset 0 Qb (s.coarse 0 e') (s.fine 0 e') - s.offset 0 Qb (s.coarse 0 e) (s.fine 0 e),
    ?_, ?_⟩
  · unfold agTgtOffsets
    apply Finset.mem_image.mpr
    refine ⟨s.fine 0 e', ?_, rfl⟩
    have := s.fine_mem 0 e'
    rwa [hQ'] at this
  · have hfin : 1000000 * K ^ 11 * B * D ≤ a / 8 := by linarith
    have hsrc : s.agSrcPoly δb e c = ![transA ((s.layers 0).G (s.coarse 0 e)) Y ts Zs,
        transB ((s.layers 0).G (s.coarse 0 e)) Y w ts Zs,
        transD ((s.layers 0).G (s.coarse 0 e)) w] := rfl
    have htgt : s.agTgtPoly δb e c (s.coarse 0 e') =
        ![transA ((s.layers 0).G (s.coarse 0 e')) Y ts Zs,
        transB ((s.layers 0).G (s.coarse 0 e')) Y w ts Zs,
        transD ((s.layers 0).G (s.coarse 0 e')) w] := rfl
    rw [hsrc, htgt]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    have hHa : a ≤ H * a := le_mul_of_one_le_left ha.le hH1
    have h6 : 2 * (2 * H * a) + a + 1000000 * K ^ 11 * B * D ≤ 6 * H * a := by linarith
    linarith

/-- **Claim 3: the target label belongs to the source's target list.** -/
theorem agree_claim_target {R : ℝ} (hat : p.AtDepth k r R) (hN1 : 1 ≤ p.N k)
    {δb : ℝ} (hδb : 0 < δb) (hχ1 : p.N k ^ (-m) ≤ 1)
    (hδbχ : 2 * (p.K k + 1) * δb ≤ p.N k ^ (-m)) {δs : ℝ} (hδs : 0 < δs)
    {M : ℕ} {e : Fin (s.count 0)} {c : ℤ} {ω ω' : α × ℝ} (hω : ω ∈ s.agSrc δb e c)
    (hω' : ω' ∈ s.agGood) {i' : Fin (s.layers 0).count} (hi' : ω'.1 ∈ (s.layers 0).C i')
    {q : Fin (p.n k r) × {σ : Fin 4 → ℤ // σ ∈ agStateBox M}}
    (hq : s.agStF δb δs M ω = some q) (hq' : s.agStF δb δs M ω' = some q) :
    i' ∈ s.agTgtList δb e c := by
  classical
  have hN : 0 < p.N k := by linarith
  have hχ : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  obtain ⟨Q, σ⟩ := q
  have hωe : ω ∈ s.event 0 e := hω.1
  obtain ⟨hQ, -⟩ := s.agree_state_parent hωe hq
  obtain ⟨e', hω'e'⟩ := s.agree_good_event hω'
  obtain ⟨hQ', -⟩ := s.agree_state_parent hω'e' hq'
  have hi'e := s.agree_label_eq hω'e' hi'
  obtain ⟨hct, hcZ, -, -⟩ := s.agree_same_state_close hat hδb hδs hq hq'
  subst hQ
  subst hi'e
  obtain ⟨hgood', -, ht', hC', -⟩ := s.agree_event_data0 hω'e'
  rw [hQ'] at ht'
  have hunit' := agree_block_subset_unit k r _ ht'
  obtain ⟨hts0, hts1, -, -⟩ := s.agree_src_time hδb hω
  have hZs := s.agree_src_Z hN hχ1 hδb hω
  obtain ⟨htag0, htag1⟩ := s.agree_coarse_tags hC'
  have hmem : s.coarse 0 e' ∈ s.coarseChoices (s.parent 0 e)
      ((s.layers 0).tag (s.coarse 0 e')) := by
    have := s.coarse_mem 0 e'
    rwa [hQ'] at this
  unfold agTgtList
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hmem, ?_⟩
  set χ := p.N k ^ (-m) with hχ_def
  set K := p.K k with hK_def
  set a := (s.layers 0).tag (s.coarse 0 e') 0 with ha_def
  set b := (s.layers 0).tag (s.coarse 0 e') 1 with hb_def
  set ts := s.agSrcTime δb e c with hts_def
  set Zs := s.agSrcZ δb e c with hZs_def
  have hb3 : |p.b k ω'.1 3| ≤ K := by
    have := hgood'.2
    have h0 := abs_nonneg (p.b k ω'.1 0)
    have h1 := abs_nonneg (p.b k ω'.1 1)
    have h4 := abs_nonneg (p.b k ω'.1 4)
    linarith
  have hv := agree_abs_sub_bin_le hχ htag0
  have hz := agree_abs_sub_bin_le hχ htag1
  have hav : |(a : ℝ) * χ| ≤ K + 1 := by
    have := abs_sub_abs_le_abs_sub ((a : ℝ) * χ) (p.b k ω'.1 3)
    rw [abs_sub_comm] at this
    linarith
  have hZ'Zs : |p.x k ω'.1 ω'.2 1 - Zs| ≤ 3 * χ := by
    calc _ ≤ |p.x k ω'.1 ω'.2 1 - p.x k ω.1 ω.2 1| + |p.x k ω.1 ω.2 1 - Zs| :=
          abs_sub_le _ _ _
      _ ≤ (K + 1) * δb + (2 * χ + (K + 1) * δb) := by rw [abs_sub_comm]; gcongr
      _ ≤ 3 * χ := by linarith
  have ht'ts : |ω'.2 - ts| ≤ 2 * δb := by
    have : |ω.2 - ts| ≤ δb := by rw [abs_of_nonneg hts0]; exact hts1
    calc |ω'.2 - ts| ≤ |ω'.2 - ω.2| + |ω.2 - ts| := abs_sub_le _ _ _
      _ ≤ δb + δb := by rw [abs_sub_comm]; gcongr
      _ = 2 * δb := by ring
  have ht'abs : |ω'.2| ≤ 1 := abs_le.mpr ⟨by linarith [hunit'.1], hunit'.2⟩
  have hprod : |ω'.2 * p.b k ω'.1 3 - ts * ((a : ℝ) * χ)| ≤ 2 * χ := by
    have heq : ω'.2 * p.b k ω'.1 3 - ts * ((a : ℝ) * χ) =
        ω'.2 * (p.b k ω'.1 3 - (a : ℝ) * χ) + (ω'.2 - ts) * ((a : ℝ) * χ) := by ring
    rw [heq]
    have hKδ : (K + 1) * (2 * δb) ≤ χ := by linarith
    calc _ ≤ |ω'.2 * (p.b k ω'.1 3 - (a : ℝ) * χ)| + |(ω'.2 - ts) * ((a : ℝ) * χ)| :=
          abs_add_le _ _
      _ = |ω'.2| * |p.b k ω'.1 3 - (a : ℝ) * χ| + |ω'.2 - ts| * |(a : ℝ) * χ| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * χ + (2 * δb) * (K + 1) := by gcongr
      _ ≤ 2 * χ := by linarith
  have hb0 : |p.b k ω'.1 0 - (Zs - ts * ((a : ℝ) * χ))| ≤ 5 * χ := by
    have hx1 : p.x k ω'.1 ω'.2 1 = p.b k ω'.1 0 + ω'.2 * p.b k ω'.1 3 := rfl
    have heq : p.b k ω'.1 0 - (Zs - ts * ((a : ℝ) * χ)) =
        (p.x k ω'.1 ω'.2 1 - Zs) - (ω'.2 * p.b k ω'.1 3 - ts * ((a : ℝ) * χ)) := by
      rw [hx1]; ring
    rw [heq]
    calc _ ≤ |p.x k ω'.1 ω'.2 1 - Zs| + |ω'.2 * p.b k ω'.1 3 - ts * ((a : ℝ) * χ)| :=
          abs_sub _ _
      _ ≤ 3 * χ + 2 * χ := add_le_add hZ'Zs hprod
      _ = 5 * χ := by ring
  have hy := agree_abs_sub_bin_le hχ
    (rfl : ⌊(Zs - ts * ((a : ℝ) * χ)) / χ⌋ = ⌊(Zs - ts * ((a : ℝ) * χ)) / χ⌋)
  have hcenter : s.agTagCenter δb e c a = ⌊(Zs - ts * ((a : ℝ) * χ)) / χ⌋ := rfl
  rw [hcenter]
  set y := ⌊(Zs - ts * ((a : ℝ) * χ)) / χ⌋ with hy_def
  have hreal : |((b : ℝ) - (y : ℝ))| * χ ≤ 7 * χ := by
    have heq : ((b : ℝ) - (y : ℝ)) * χ = ((b : ℝ) * χ - p.b k ω'.1 0) +
        (p.b k ω'.1 0 - (Zs - ts * ((a : ℝ) * χ))) +
        ((Zs - ts * ((a : ℝ) * χ)) - (y : ℝ) * χ) := by ring
    rw [← abs_of_pos hχ, ← abs_mul, heq, abs_of_pos hχ]
    calc _ ≤ |(b : ℝ) * χ - p.b k ω'.1 0| + |p.b k ω'.1 0 - (Zs - ts * ((a : ℝ) * χ))| +
          |(Zs - ts * ((a : ℝ) * χ)) - (y : ℝ) * χ| := abs_add_three _ _ _
      _ ≤ χ + 5 * χ + χ := by
          rw [abs_sub_comm ((b : ℝ) * χ)]
          gcongr
      _ = 7 * χ := by ring
  have hreal' : |((b : ℝ) - (y : ℝ))| ≤ 7 := le_of_mul_le_mul_right hreal hχ
  have : ((|b - y| : ℤ) : ℝ) ≤ 7 := by
    rw [Int.cast_abs, Int.cast_sub]
    exact hreal'
  exact_mod_cast this

/-- **Claim 2: a disagreement at the representative point is a coefficient gap.** -/
theorem agree_claim_gap {R : ℝ} (hat : p.AtDepth k r R) (hN1 : 1 ≤ p.N k) (hK1 : 1 ≤ p.K k)
    (hℓr : 0 ≤ p.ℓ * r) (hm : 0 ≤ m) (hru : 0 ≤ r + u) {δb : ℝ} (hδb : 0 < δb)
    (hχ1 : p.N k ^ (-m) ≤ 1)
    (hfz : 8000000 * p.K k ^ 11 * p.N k ^ (m / 1000) * (δb + p.N k ^ (-m)) ≤
      p.N k ^ (-(r + u)))
    {E : ℝ} (haE : p.N k ^ (-(r + u)) ≤ E) {δs : ℝ} {M : ℕ} {e : Fin (s.count 0)} {c : ℤ}
    {ω : α × ℝ} (hω : ω ∈ s.agSrc δb e c) {Q : Fin (p.n k r)}
    {σ : {σ : Fin 4 → ℤ // σ ∈ agStateBox M}}
    (hq : s.agStF δb δs M ω = some (Q, σ)) {i' : Fin (s.layers 0).count}
    (hbad : ¬ s.agreeRel δb E M (some (Q, σ)) (some (s.coarse 0 e)) (some i')) :
    E / 4 ≤ Kernels.coeffGap (s.agSrcPoly δb e c) (s.agTgtPoly δb e c i') := by
  have hN : 0 < p.N k := by linarith
  have hχ : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  have hB1 : 1 ≤ p.N k ^ (m / 1000) := Real.one_le_rpow hN1 (by positivity)
  have hB0 : 0 ≤ p.N k ^ (m / 1000) := by linarith
  have hωe : ω ∈ s.event 0 e := hω.1
  obtain ⟨hQ, hσ⟩ := s.agree_state_parent hωe hq
  subst hQ
  obtain ⟨hgood, hB, ht, hC, hF⟩ := s.agree_event_data0 hωe
  have hunit := agree_block_subset_unit k r _ ht
  have htabs : |ω.2| ≤ 1 := abs_le.mpr ⟨by linarith [hunit.1], hunit.2⟩
  have hZ : |p.x k ω.1 ω.2 1| ≤ p.K k := by
    simpa using baseGood_base_bound p hK1 hgood 1
  obtain ⟨hts0, hts1, hts2, hts3⟩ := s.agree_src_time hδb hω
  have htsabs : |s.agSrcTime δb e c| ≤ 1 := abs_le.mpr ⟨by linarith, hts3⟩
  have hZs := s.agree_src_Z hN hχ1 hδb hω
  obtain ⟨-, -, -, -, hrepZ⟩ := agree_rep_close (δs := δs) hat hδb ht
  rw [hσ] at hrepZ
  have hrepT : p.agRepTime k r (s.parent 0 e) δb σ.1 = s.agSrcTime δb e c := by
    have h0 : σ.1 0 = c := by
      rw [← hσ, agree_nativeState_apply_zero]
      exact hω.2
    unfold agRepTime agSrcTime
    rw [h0]
  set χ := p.N k ^ (-m) with hχ_def
  set B := p.N k ^ (m / 1000) with hB_def
  set K := p.K k with hK_def
  set D := δb + χ with hD_def
  set Qb := s.parent 0 e with hQb
  set ts := s.agSrcTime δb e c with hts_def
  set Zs := s.agSrcZ δb e c with hZs_def
  set Zr := p.agRepZ k r Qb δb σ.1 with hZr_def
  set Y := p.tiltY k r Qb with hY_def
  set w := p.blockWidth k r with hw_def
  have hK0 : 0 ≤ K := by linarith
  have hD0 : 0 ≤ D := by positivity
  have hw0 : 0 ≤ w := (agree_blockWidth_pos (p := p) r hN).le
  have hw1 : |w| ≤ 1 := by rw [abs_of_nonneg hw0]; exact agree_blockWidth_le_one hN1 hℓr
  have hD1 : 8 * K ^ 2 * D ≤ 1 := by
    have h1 : 8 * K ^ 2 * D ≤ 8000000 * K ^ 11 * B * D :=
      mul_le_mul_of_nonneg_right (agree_small_numeric hK1 hB1) hD0
    have ha1 : p.N k ^ (-(r + u)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    linarith
  have hYt : |Y ω.2 (p.x k ω.1 ω.2 1)| ≤ 3 * K ^ 2 := hat.agree_tiltY_abs_le hK1 Qb htabs hZ
  have hKsq : 1 ≤ K ^ 2 := one_le_pow₀ hK1
  -- the representative and freezing points are near the incidence
  have hρs : |ω.2 - ts| + |Y ω.2 (p.x k ω.1 ω.2 1) - Y ts Zs| ≤ 8 * K ^ 2 * D := by
    have h1 := hat.agree_tiltY_sub_le Qb ω.2 (p.x k ω.1 ω.2 1) ts Zs
    have h2 : |ω.2 - ts| ≤ δb := by rw [abs_of_nonneg hts0]; exact hts1
    have hKδ : 0 ≤ (K + 1) * δb := by positivity
    exact agree_dist_src hK1 hδb.le hχ.le (abs_nonneg _) (by linarith) (abs_nonneg _)
      (by linarith) h1
  have hρr : |ω.2 - ts| + |Y ω.2 (p.x k ω.1 ω.2 1) - Y ts Zr| ≤ 8 * K ^ 2 * D := by
    have h1 := hat.agree_tiltY_sub_le Qb ω.2 (p.x k ω.1 ω.2 1) ts Zr
    have h2 : |ω.2 - ts| ≤ δb := by rw [abs_of_nonneg hts0]; exact hts1
    have hKδ : 0 ≤ (K + 1) * δb := by positivity
    exact agree_dist_src hK1 hδb.le hχ.le (abs_nonneg _) (by linarith) (abs_nonneg _)
      (by linarith) h1
  have hYs : |Y ts Zs| ≤ 4 * K ^ 2 := by
    have := abs_sub_abs_le_abs_sub (Y ts Zs) (Y ω.2 (p.x k ω.1 ω.2 1))
    rw [abs_sub_comm (Y ts Zs)] at this
    have h2 := abs_nonneg (ω.2 - ts)
    linarith
  have hYr : |Y ts Zr| ≤ 4 * K ^ 2 := by
    have := abs_sub_abs_le_abs_sub (Y ts Zr) (Y ω.2 (p.x k ω.1 ω.2 1))
    rw [abs_sub_comm (Y ts Zr)] at this
    have h2 := abs_nonneg (ω.2 - ts)
    linarith
  have hρ : |ts - ts| + |Y ts Zr - Y ts Zs| ≤ 8 * K ^ 2 * D := by
    have h1 := hat.agree_tiltY_sub_le Qb ts Zr ts Zs
    have h2 : |Zr - Zs| ≤ 2 * χ + 2 * (K + 1) * δb := by
      calc _ ≤ |Zr - p.x k ω.1 ω.2 1| + |p.x k ω.1 ω.2 1 - Zs| := abs_sub_le _ _ _
        _ ≤ (K + 1) * δb + (2 * χ + (K + 1) * δb) := by rw [abs_sub_comm]; gcongr
        _ = _ := by ring
    exact agree_dist_src hK1 hδb.le hχ.le (abs_nonneg _) (by simp; positivity) (abs_nonneg _) h2 h1
  have hG := s.agree_totalDegree_coarse (s.coarse 0 e)
  have hG' := s.agree_totalDegree_coarse i'
  obtain ⟨-, hB1'⟩ := agree_freeze_bounds _ hG hB0 (s.agree_coeff_coarse _) hK1 Y hw1 htsabs htsabs
    hYr hYs hD0 hρ
  obtain ⟨-, hB2⟩ := agree_freeze_bounds _ hG' hB0 (s.agree_coeff_coarse _) hK1 Y hw1 htsabs htsabs
    hYr hYs hD0 hρ
  have hεB : 331776 * K ^ 10 * B * D ≤ E / 8 := by
    have hK10 : K ^ 10 ≤ K ^ 11 := pow_le_pow_right₀ hK1 (by norm_num)
    have h1 : 331776 * K ^ 10 * B * D ≤ 331776 * K ^ 11 * B * D := by gcongr
    have h2 : 0 ≤ K ^ 11 * B * D := by positivity
    linarith
  have hbad' : ¬ ∀ c' : Fin 2, |p.agPairAt k r Qb ((s.layers 0).G (s.coarse 0 e)) ts Zr c' -
      p.agPairAt k r Qb ((s.layers 0).G i') ts Zr c'| ≤ E / 2 := by
    rw [← hrepT]
    exact hbad
  apply agree_gap_of_pair_disagree hbad' _ _ rfl rfl hεB
  · exact hB1'
  · exact hB2

/-- **Freezing the final transverse pair** at the representative point of the native state. -/
theorem agree_pair_freeze {R : ℝ} (hat : p.AtDepth k r R) (hN1 : 1 ≤ p.N k) (hK1 : 1 ≤ p.K k)
    (hℓr : 0 ≤ p.ℓ * r) (hm : 0 ≤ m) (hru : 0 ≤ r + u) {δb : ℝ} (hδb : 0 < δb)
    (hχ1 : p.N k ^ (-m) ≤ 1)
    (hfz : 8000000 * p.K k ^ 11 * p.N k ^ (m / 1000) * (δb + p.N k ^ (-m)) ≤
      p.N k ^ (-(r + u)))
    (δs : ℝ) {e : Fin (s.count 0)} {ω : α × ℝ} (hωe : ω ∈ s.event 0 e)
    (i : Fin (s.layers 0).count) (c' : Fin 2) :
    |p.agPairAt k r (s.parent 0 e) ((s.layers 0).G i) ω.2 (p.x k ω.1 ω.2 1) c' -
      p.agPairAt k r (s.parent 0 e) ((s.layers 0).G i)
        (p.agRepTime k r (s.parent 0 e) δb (p.nativeState k r (s.parent 0 e) δb δs ω))
        (p.agRepZ k r (s.parent 0 e) δb (p.nativeState k r (s.parent 0 e) δb δs ω)) c'| ≤
      p.N k ^ (-(r + u)) / 8 := by
  have hN : 0 < p.N k := by linarith
  have hχ : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  have ha : 0 < p.N k ^ (-(r + u)) := Real.rpow_pos_of_pos hN _
  have hB1 : 1 ≤ p.N k ^ (m / 1000) := Real.one_le_rpow hN1 (by positivity)
  have hB0 : 0 ≤ p.N k ^ (m / 1000) := by linarith
  obtain ⟨hgood, hB, ht, hC, hF⟩ := s.agree_event_data0 hωe
  have hunit := agree_block_subset_unit k r _ ht
  have htabs : |ω.2| ≤ 1 := abs_le.mpr ⟨by linarith [hunit.1], hunit.2⟩
  have hZ : |p.x k ω.1 ω.2 1| ≤ p.K k := by
    simpa using baseGood_base_bound p hK1 hgood 1
  obtain ⟨hr0, hr1, hr2, hr3, hrepZ⟩ := agree_rep_close (δs := δs) hat hδb ht
  set χ := p.N k ^ (-m) with hχ_def
  set B := p.N k ^ (m / 1000) with hB_def
  set K := p.K k with hK_def
  set D := δb + χ with hD_def
  set Qb := s.parent 0 e with hQb
  set tr := p.agRepTime k r Qb δb (p.nativeState k r Qb δb δs ω) with htr
  set Zr := p.agRepZ k r Qb δb (p.nativeState k r Qb δb δs ω) with hZr
  set Y := p.tiltY k r Qb with hY_def
  set w := p.blockWidth k r with hw_def
  have hK0 : 0 ≤ K := by linarith
  have hD0 : 0 ≤ D := by positivity
  have hw0 : 0 ≤ w := (agree_blockWidth_pos (p := p) r hN).le
  have hw1 : |w| ≤ 1 := by rw [abs_of_nonneg hw0]; exact agree_blockWidth_le_one hN1 hℓr
  have hD1 : 8 * K ^ 2 * D ≤ 1 := by
    have h1 : 8 * K ^ 2 * D ≤ 8000000 * K ^ 11 * B * D :=
      mul_le_mul_of_nonneg_right (agree_small_numeric hK1 hB1) hD0
    have ha1 : p.N k ^ (-(r + u)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    linarith
  have hYt : |Y ω.2 (p.x k ω.1 ω.2 1)| ≤ 3 * K ^ 2 := hat.agree_tiltY_abs_le hK1 Qb htabs hZ
  have hKsq : 1 ≤ K ^ 2 := one_le_pow₀ hK1
  have htrabs : |tr| ≤ 1 := abs_le.mpr ⟨by linarith, hr3⟩
  have hρ : |ω.2 - tr| + |Y ω.2 (p.x k ω.1 ω.2 1) - Y tr Zr| ≤ 8 * K ^ 2 * D := by
    have h1 := hat.agree_tiltY_sub_le Qb ω.2 (p.x k ω.1 ω.2 1) tr Zr
    have h2 : |ω.2 - tr| ≤ δb := by rw [abs_of_nonneg hr0]; exact hr1
    have hKδ : 0 ≤ (K + 1) * δb := by positivity
    exact agree_dist_src hK1 hδb.le hχ.le (abs_nonneg _) (by linarith) (abs_nonneg _)
      (by linarith) h1
  have hYr : |Y tr Zr| ≤ 4 * K ^ 2 := by
    have := abs_sub_abs_le_abs_sub (Y tr Zr) (Y ω.2 (p.x k ω.1 ω.2 1))
    rw [abs_sub_comm (Y tr Zr)] at this
    have h2 := abs_nonneg (ω.2 - tr)
    linarith
  have hG := s.agree_totalDegree_coarse i
  obtain ⟨-, hBd⟩ := agree_freeze_bounds _ hG hB0 (s.agree_coeff_coarse _) hK1 Y hw1 htabs htrabs
    (hYt.trans (by linarith [sq_nonneg K])) hYr hD0 hρ
  have hfin : 331776 * K ^ 10 * B * D ≤ p.N k ^ (-(r + u)) / 8 := by
    have hK10 : K ^ 10 ≤ K ^ 11 := pow_le_pow_right₀ hK1 (by norm_num)
    have h1 : 331776 * K ^ 10 * B * D ≤ 331776 * K ^ 11 * B * D := by gcongr
    have h2 : 0 ≤ K ^ 11 * B * D := by positivity
    linarith
  fin_cases c'
  · simp only [Fin.zero_eta, agPairAt, Matrix.cons_val_zero]
    exact hBd.trans hfin
  · simp only [Fin.mk_one, agPairAt, Matrix.cons_val_one, Matrix.head_cons, sub_self, abs_zero]
    positivity

end ComparedSample

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
