-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.Claims; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Freeze
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.MatchCover

/-!
# The pointwise claims of coefficient agreement at a fine state

For a source incidence `ω` (a color-0 event `e` and a time cell `c` of its parent block) and a
agGood target incidence `ω'` of coarse label `i'` in the same combined state:

* `agree_claim_match`: the normalized transverse coordinate of `ω` lies in the matching set of the
  frozen source and target quadratics, with the target's offset differences, to width
  `6 H a₁` on `[-K, K]`;
* `agree_claim_target`: `i'` belongs to the target list of the source;
* `agree_claim_gap`: a disagreement of the transverse pairs at the state's representative point is a
  nonconstant coefficient gap `≥ E / 4` of the frozen quadratics;
* `agree_pair_freeze`: the transverse pair at an incidence and at the representative point of its
  native state differ by at most `a₁ / 8`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

theorem agree_nativeState_apply_zero (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (δb δs : ℝ) (ω : α × ℝ) :
    p.nativeState k r Q δb δs ω 0 = ⌊p.tauN k r Q ω / δb⌋ := rfl

theorem agree_nativeState_apply_one (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (δb δs : ℝ) (ω : α × ℝ) :
    p.nativeState k r Q δb δs ω 1 = ⌊p.zetaN k r Q ω / δb⌋ := rfl

theorem agree_nativeState_apply_two (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (δb δs : ℝ) (ω : α × ℝ) :
    p.nativeState k r Q δb δs ω 2 = ⌊p.uN k r Q ω / δb⌋ := rfl

theorem agree_nativeState_apply_three (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (δb δs : ℝ) (ω : α × ℝ) :
    p.nativeState k r Q δb δs ω 3 = ⌊p.signal k ω.1 ω.2 / δs⌋ := rfl

theorem AtDepth.agree_tiltY_sub_le {k : ℕ} {r R : ℝ} (hat : p.AtDepth k r R) (Q : Fin (p.n k r))
    (t Z t' Z' : ℝ) :
    |p.tiltY k r Q t Z - p.tiltY k r Q t' Z'| ≤ p.K k * |t - t'| + p.K k * |Z - Z'| := by
  unfold tiltY
  have h3 := hat.agree_coeff_le Q 3
  have h4 := hat.agree_coeff_le Q 4
  calc _ = |p.c k r Q 3 * (t - t') + p.c k r Q 4 * (Z - Z')| := by ring_nf
    _ ≤ |p.c k r Q 3 * (t - t')| + |p.c k r Q 4 * (Z - Z')| := abs_add_le _ _
    _ = |p.c k r Q 3| * |t - t'| + |p.c k r Q 4| * |Z - Z'| := by rw [abs_mul, abs_mul]
    _ ≤ _ := by gcongr

theorem AtDepth.agree_tiltY_abs_le {k : ℕ} {r R : ℝ} (hat : p.AtDepth k r R) (hK1 : 1 ≤ p.K k)
    (Q : Fin (p.n k r)) {t Z : ℝ} (ht : |t| ≤ 1) (hZ : |Z| ≤ p.K k) :
    |p.tiltY k r Q t Z| ≤ 3 * p.K k ^ 2 := by
  unfold tiltY
  have h2 := hat.agree_coeff_le Q 2
  have h3 := hat.agree_coeff_le Q 3
  have h4 := hat.agree_coeff_le Q 4
  calc _ ≤ |p.c k r Q 2 + p.c k r Q 3 * t| + |p.c k r Q 4 * Z| := abs_add_le _ _
    _ ≤ |p.c k r Q 2| + |p.c k r Q 3 * t| + |p.c k r Q 4 * Z| := by
        gcongr; exact abs_add_le _ _
    _ = |p.c k r Q 2| + |p.c k r Q 3| * |t| + |p.c k r Q 4| * |Z| := by
        rw [abs_mul, abs_mul]
    _ ≤ p.K k + p.K k * 1 + p.K k * p.K k := by gcongr
    _ ≤ 3 * p.K k ^ 2 := by nlinarith

namespace ComparedSample

variable {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)

theorem agree_good_event {ω : α × ℝ} (hω : ω ∈ s.agGood) : ∃ e, ω ∈ s.event 0 e :=
  mem_iUnion.mp hω.1

/-- The time of a source lies in its cell, after the freezing time. -/
theorem agree_src_time {δb : ℝ} (hδb : 0 < δb) {e : Fin (s.count 0)} {c : ℤ} {ω : α × ℝ}
    (hω : ω ∈ s.agSrc δb e c) :
    0 ≤ ω.2 - s.agSrcTime δb e c ∧ ω.2 - s.agSrcTime δb e c ≤ δb ∧
      0 ≤ s.agSrcTime δb e c ∧ s.agSrcTime δb e c ≤ 1 := by
  have hc : ⌊p.tauN k r (s.parent 0 e) ω / δb⌋ = c := hω.2
  have ht := (s.agree_event_data0 hω.1).2.2.1
  obtain ⟨hτ0, hτ1⟩ := agree_tauN_mem_unit (p := p) ht
  have hq := agree_blockLen_pos (p := p) k r
  have hq1 := agree_blockLen_le_one (p := p) k r
  have hlo := (le_div_iff₀ hδb).mp (hc ▸ Int.floor_le (p.tauN k r (s.parent 0 e) ω / δb))
  have hhi := (div_lt_iff₀ hδb).mp (hc ▸ Int.lt_floor_add_one (p.tauN k r (s.parent 0 e) ω / δb))
  have hc0 : (0 : ℝ) ≤ c := by
    have : (0 : ℤ) ≤ c := by
      rw [← hc]
      exact Int.floor_nonneg.mpr (div_nonneg hτ0 hδb.le)
    exact_mod_cast this
  have hdiff : ω.2 - s.agSrcTime δb e c =
      p.blockLen k r * (p.tauN k r (s.parent 0 e) ω - (c : ℝ) * δb) := by
    have h := agree_tauN_mul_add (s.parent 0 e) ω
    unfold agSrcTime
    linear_combination h
  have hst := agree_blockStart_nonneg (p := p) k r (s.parent 0 e)
  have hst1 := agree_blockStart_add_le_one (p := p) k r (s.parent 0 e)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdiff]
    exact mul_nonneg hq.le (by linarith)
  · rw [hdiff]
    have h1 : p.tauN k r (s.parent 0 e) ω - (c : ℝ) * δb ≤ δb := by linarith
    calc _ ≤ 1 * δb := mul_le_mul hq1 h1 (by linarith) zero_le_one
      _ = δb := one_mul δb
  · unfold agSrcTime
    have : 0 ≤ p.blockLen k r * ((c : ℝ) * δb) := mul_nonneg hq.le (mul_nonneg hc0 hδb.le)
    linarith
  · unfold agSrcTime
    have h1 : (c : ℝ) * δb ≤ 1 := by linarith
    have : p.blockLen k r * ((c : ℝ) * δb) ≤ p.blockLen k r * 1 :=
      mul_le_mul_of_nonneg_left h1 hq.le
    linarith

/-- The major coordinate of a source lies within `2 χ + (K + 1) δb` of its freezing point. -/
theorem agree_src_Z (hN : 0 < p.N k) (hχ1 : p.N k ^ (-m) ≤ 1) {δb : ℝ}
    (hδb : 0 < δb) {e : Fin (s.count 0)} {c : ℤ} {ω : α × ℝ} (hω : ω ∈ s.agSrc δb e c) :
    |p.x k ω.1 ω.2 1 - s.agSrcZ δb e c| ≤ 2 * p.N k ^ (-m) + (p.K k + 1) * δb := by
  obtain ⟨hgood, hB, ht, hC, -⟩ := s.agree_event_data0 hω.1
  have hunit : ω.2 ∈ Icc (0 : ℝ) 1 := agree_block_subset_unit k r _ ht
  obtain ⟨htag0, htag1⟩ := s.agree_coarse_tags hC
  have hχ : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  have htube := intercept_velocity_bin_tube hχ htag1 htag0 hunit
  obtain ⟨h0, h1, -, -⟩ := s.agree_src_time hδb hω
  have hb3 : |p.b k ω.1 3| ≤ p.K k := by
    have := hgood.2
    have h0 := abs_nonneg (p.b k ω.1 0)
    have h1 := abs_nonneg (p.b k ω.1 1)
    have h4 := abs_nonneg (p.b k ω.1 4)
    linarith
  have hv := agree_abs_sub_bin_le hχ htag0
  have hvel : |((s.layers 0).tag (s.coarse 0 e) 0 : ℝ) * p.N k ^ (-m)| ≤ p.K k + 1 := by
    have := abs_sub_abs_le_abs_sub (((s.layers 0).tag (s.coarse 0 e) 0 : ℝ) * p.N k ^ (-m))
      (p.b k ω.1 3)
    rw [abs_sub_comm] at this
    linarith
  have hx1 : p.x k ω.1 ω.2 1 = p.b k ω.1 0 + ω.2 * p.b k ω.1 3 := rfl
  have heq : p.x k ω.1 ω.2 1 - s.agSrcZ δb e c =
      (p.b k ω.1 0 + ω.2 * p.b k ω.1 3 -
        (((s.layers 0).tag (s.coarse 0 e) 1 : ℝ) * p.N k ^ (-m) +
          ω.2 * (((s.layers 0).tag (s.coarse 0 e) 0 : ℝ) * p.N k ^ (-m)))) +
        (ω.2 - s.agSrcTime δb e c) * (((s.layers 0).tag (s.coarse 0 e) 0 : ℝ) * p.N k ^ (-m)) := by
    rw [hx1]
    unfold agSrcZ
    ring
  rw [heq]
  calc _ ≤ _ := abs_add_le _ _
    _ = |p.b k ω.1 0 + ω.2 * p.b k ω.1 3 -
          (((s.layers 0).tag (s.coarse 0 e) 1 : ℝ) * p.N k ^ (-m) +
            ω.2 * (((s.layers 0).tag (s.coarse 0 e) 0 : ℝ) * p.N k ^ (-m)))| +
        |ω.2 - s.agSrcTime δb e c| *
          |((s.layers 0).tag (s.coarse 0 e) 0 : ℝ) * p.N k ^ (-m)| := by rw [abs_mul]
    _ ≤ 2 * p.N k ^ (-m) + δb * (p.K k + 1) := by
        gcongr
        rw [abs_of_nonneg h0]
        exact h1
    _ = _ := by ring

/-- Two incidences in one combined state are close in time, major and transverse coordinates
and native signal. -/
theorem agree_same_state_close {R : ℝ} (hat : p.AtDepth k r R) {δb δs : ℝ} (hδb : 0 < δb)
    (hδs : 0 < δs) {M : ℕ} {ω ω' : α × ℝ}
    {q : Fin (p.n k r) × {σ : Fin 4 → ℤ // σ ∈ agStateBox M}}
    (hq : s.agStF δb δs M ω = some q) (hq' : s.agStF δb δs M ω' = some q) :
    |ω.2 - ω'.2| ≤ δb ∧ |p.x k ω.1 ω.2 1 - p.x k ω'.1 ω'.2 1| ≤ (p.K k + 1) * δb ∧
      |p.uN k r q.1 ω - p.uN k r q.1 ω'| ≤ δb ∧
      |p.signal k ω.1 ω.2 - p.signal k ω'.1 ω'.2| ≤ δs := by
  obtain ⟨Q, σ⟩ := q
  obtain ⟨-, hσ⟩ := s.agree_stF_eq_some_iff.mp hq
  obtain ⟨-, hσ'⟩ := s.agree_stF_eq_some_iff.mp hq'
  have hst : p.nativeState k r Q δb δs ω = p.nativeState k r Q δb δs ω' := hσ.trans hσ'.symm
  have h0 := congrFun hst 0
  have h1 := congrFun hst 1
  have h2 := congrFun hst 2
  have h3 := congrFun hst 3
  rw [agree_nativeState_apply_zero, agree_nativeState_apply_zero] at h0
  rw [agree_nativeState_apply_one, agree_nativeState_apply_one] at h1
  rw [agree_nativeState_apply_two, agree_nativeState_apply_two] at h2
  rw [agree_nativeState_apply_three, agree_nativeState_apply_three] at h3
  have hτ := agree_abs_sub_lt_of_floor_eq hδb h0
  have hζ := agree_abs_sub_lt_of_floor_eq hδb h1
  have hU := agree_abs_sub_lt_of_floor_eq hδb h2
  have hX := agree_abs_sub_lt_of_floor_eq hδs h3
  have hq := agree_blockLen_pos (p := p) k r
  have hq1 := agree_blockLen_le_one (p := p) k r
  have ht : |ω.2 - ω'.2| ≤ δb := by
    rw [agree_tauN_mul_add Q ω, agree_tauN_mul_add Q ω']
    have : p.blockStart k r Q + p.blockLen k r * p.tauN k r Q ω -
        (p.blockStart k r Q + p.blockLen k r * p.tauN k r Q ω') =
        p.blockLen k r * (p.tauN k r Q ω - p.tauN k r Q ω') := by ring
    rw [this, abs_mul, abs_of_pos hq]
    calc _ ≤ 1 * δb := mul_le_mul hq1 hτ.le (abs_nonneg _) zero_le_one
      _ = δb := one_mul δb
  refine ⟨ht, ?_, hU.le, hX.le⟩
  rw [agree_zetaN_mul_add Q ω, agree_zetaN_mul_add Q ω']
  have hc1 := hat.agree_coeff_le Q 1
  have : p.c k r Q 0 + p.c k r Q 1 * ω.2 + p.blockLen k r * p.zetaN k r Q ω -
      (p.c k r Q 0 + p.c k r Q 1 * ω'.2 + p.blockLen k r * p.zetaN k r Q ω') =
      p.c k r Q 1 * (ω.2 - ω'.2) + p.blockLen k r * (p.zetaN k r Q ω - p.zetaN k r Q ω') := by
    ring
  rw [this]
  have hK0 : 0 ≤ p.K k := (abs_nonneg _).trans hc1
  calc _ ≤ |p.c k r Q 1 * (ω.2 - ω'.2)| +
        |p.blockLen k r * (p.zetaN k r Q ω - p.zetaN k r Q ω')| := abs_add_le _ _
    _ = |p.c k r Q 1| * |ω.2 - ω'.2| +
        p.blockLen k r * |p.zetaN k r Q ω - p.zetaN k r Q ω'| := by
        rw [abs_mul, abs_mul, abs_of_pos hq]
    _ ≤ p.K k * δb + 1 * δb := by
        gcongr
    _ = _ := by ring

end ComparedSample

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
