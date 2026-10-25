-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/Reg/LocalStage.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.Local
import Submission.Obl.k4_fixed_prior_chart_regularization.RegKernels

/-!
# Stage 1 at all large `N`

The tested widths are the grid `N^(-c k/J)`, `k ≤ J`, with `c/J ≤ ε/4`; every width
`q ∈ [N^(-c), 1]` lies within the factor `N^(c/J)` above a grid width (`exists_grid_width`).
With the floor `w^d/K'`, `K' = 4(J+1)K²`, the deletion costs at most `1/(4K)` in total and the
local counts have constant `4800 (J+1) K⁶ N^(c/J) ≤ N^ε` (`stageLocal`).
-/

open MeasureTheory Set Filter

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.Reg

/-- Every width above `N^(-c)` is at most the factor `N^(c/J)` above a grid width. -/
theorem exists_grid_width {N c q : ℝ} {J : ℕ} (hN : 1 ≤ N) (hJ : 0 < J) (hc : 0 < c)
    (hq : N ^ (-c) ≤ q) (hq1 : q ≤ 1) :
    ∃ k : ℕ, k ≤ J ∧ N ^ (-(c * k / J)) ≤ q ∧ q ≤ N ^ (c / J) * N ^ (-(c * k / J)) := by
  classical
  have hN0 : 0 < N := by linarith
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJJ : N ^ (-(c * (J : ℕ) / J)) ≤ q := by
    rwa [show c * ((J : ℕ) : ℝ) / J = c by field_simp]
  have hex : ∃ k : ℕ, N ^ (-(c * k / J)) ≤ q := ⟨J, hJJ⟩
  have hk : N ^ (-(c * (Nat.find hex : ℕ) / J)) ≤ q := Nat.find_spec hex
  have hkJ : Nat.find hex ≤ J := Nat.find_min' hex hJJ
  refine ⟨Nat.find hex, hkJ, hk, ?_⟩
  have hone : 1 ≤ N ^ (c / J) := Real.one_le_rpow hN (by positivity)
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0] at hk ⊢
    simp only [Nat.cast_zero, mul_zero, zero_div, neg_zero, Real.rpow_zero] at hk ⊢
    nlinarith
  · have hlt : ¬ N ^ (-(c * ((Nat.find hex - 1 : ℕ) : ℝ) / J)) ≤ q :=
      Nat.find_min hex (by omega)
    push Not at hlt
    have e : N ^ (c / J) * N ^ (-(c * (Nat.find hex : ℕ) / J)) =
        N ^ (-(c * ((Nat.find hex - 1 : ℕ) : ℝ) / J)) := by
      rw [← Real.rpow_add hN0]
      congr 1
      rw [Nat.cast_sub (by omega : 1 ≤ Nat.find hex)]
      field_simp
      ring
    linarith

set_option maxHeartbeats 2000000 in
/-- **Stage 1**: local scalar counts. -/
theorem stageLocal : StageLocal := by
  intro d hd hd1 c hc ε hε
  set J : ℕ := ⌈4 * c / ε⌉₊ + 1 with hJ_def
  have hJ : 0 < J := Nat.succ_pos _
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hcJ : c / J ≤ ε / 4 := by
    have h1 : 4 * c / ε ≤ (⌈4 * c / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (J : ℝ) = (⌈4 * c / ε⌉₊ : ℝ) + 1 := by rw [hJ_def]; push_cast; ring
    rw [div_le_iff₀ hJ']
    rw [div_le_iff₀ hε] at h1
    nlinarith
  set η : ℝ := ε / 40 with hη_def
  have hη : 0 < η := by positivity
  have hev1 := JetFit.eventually_mul_rpow_le (4800 * ((J : ℝ) + 1)) (x := 6 * η + c / J)
    (y := ε) (by linarith)
  have hev2 := JetFit.eventually_mul_rpow_le 2 (x := η) (y := ε) (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hev1.and hev2)
  refine ⟨η, hη, by linarith, max N₁ 2, le_max_right _ _, ?_⟩
  intro N hN Ω _ ν hν y β γ E F hU
  have hN1 : 1 ≤ N := le_trans (by norm_num) ((le_max_right _ _).trans hN)
  have hN0 : 0 < N := by linarith
  obtain ⟨hc1, hc2⟩ := hN₁ N ((le_max_left _ _).trans hN)
  set K : ℝ := N ^ η with hK_def
  have hK1 : 1 ≤ K := Real.one_le_rpow hN1 hη.le
  have hK0 : 0 < K := by linarith
  have hζ : 0 < N ^ (-c) := Real.rpow_pos_of_pos hN0 _
  set ws : Finset ℝ := (Finset.range (J + 1)).image (fun k : ℕ => N ^ (-(c * k / J)))
    with hws_def
  have hws : ∀ w ∈ ws, N ^ (-c) ≤ w ∧ w ≤ 1 := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
    have hkJ : (k : ℝ) ≤ J := by exact_mod_cast (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    constructor
    · apply Real.rpow_le_rpow_of_exponent_le hN1
      have : c * k / J ≤ c := by
        rw [div_le_iff₀ hJ']; nlinarith
      linarith
    · apply Real.rpow_le_one_of_one_le_of_nonpos hN1
      have : 0 ≤ c * k / J := by positivity
      linarith
  have hwscard : (ws.card : ℝ) ≤ J + 1 := by
    have := Finset.card_image_le (s := Finset.range (J + 1)) (f := fun k : ℕ => N ^ (-(c * k / J)))
    rw [Finset.card_range] at this
    exact_mod_cast this
  set K' : ℝ := 4 * ((J : ℝ) + 1) * K ^ 2 with hK'_def
  have hK'0 : 0 < K' := by positivity
  set τ : ℝ → ℝ := fun w => w ^ d / K' with hτ_def
  set E' := floorSet ν y β γ E F ws τ with hE'_def
  have hS := measurable_scal hU.measurable_y hU.measurable_β hU.measurable_γ hU.measurable_F
  have hE'm : MeasurableSet E' := measurableSet_floorSet hU.measurableSet_E hS ws τ
  have hE'sub : E' ⊆ E := fun p hp => hp.1
  -- the deleted mass
  have hdel : (ν.prod volume) (E \ E') ≤ ENNReal.ofReal (1 / (4 * K)) := by
    have hsub : E \ E' ⊆ ⋃ w ∈ ws, lightSet ν y β γ E F w (τ w) := by
      rintro p ⟨hpE, hpE'⟩
      have : ¬ ∀ w ∈ ws, ENNReal.ofReal (τ w) ≤
          binMass ν y β γ E F w p.2 ⌊FirstJet.scal y β γ F p.1 p.2 / w⌋ :=
        fun h => hpE' ⟨hpE, h⟩
      push Not at this
      obtain ⟨w, hw, hlt⟩ := this
      exact mem_iUnion₂.2 ⟨w, hw, hpE, hlt⟩
    have hterm : ∀ w ∈ ws, (ν.prod volume) (lightSet ν y β γ E F w (τ w)) ≤
        ENNReal.ofReal (K / K') := by
      intro w hw
      obtain ⟨hw1, hw2⟩ := hws w hw
      have hw0 : 0 < w := hζ.trans_le hw1
      refine (deleted_le hU w (τ w) hw1 hw2 (by positivity)).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      simp only [hτ_def]
      rw [Real.rpow_neg hw0.le]
      field_simp
    calc (ν.prod volume) (E \ E') ≤ (ν.prod volume) (⋃ w ∈ ws, lightSet ν y β γ E F w (τ w)) :=
          measure_mono hsub
      _ ≤ ∑ w ∈ ws, (ν.prod volume) (lightSet ν y β γ E F w (τ w)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _w ∈ ws, ENNReal.ofReal (K / K') := Finset.sum_le_sum hterm
      _ = ENNReal.ofReal (ws.card * (K / K')) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (1 / (4 * K)) := by
          apply ENNReal.ofReal_le_ofReal
          have : ws.card * (K / K') ≤ ((J : ℝ) + 1) * (K / K') :=
            mul_le_mul_of_nonneg_right hwscard (by positivity)
          refine this.trans (le_of_eq ?_)
          rw [hK'_def]; field_simp
  -- the retained mass
  have hmass : ENNReal.ofReal (N ^ ε)⁻¹ ≤ (ν.prod volume) E' := by
    have h1 : ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E' + ENNReal.ofReal (1 / (4 * K)) := by
      refine hU.mass.trans ?_
      calc (ν.prod volume) E ≤ (ν.prod volume) (E' ∪ (E \ E')) := by
            apply measure_mono; intro p hp
            by_cases h : p ∈ E'
            · exact Or.inl h
            · exact Or.inr ⟨hp, h⟩
        _ ≤ (ν.prod volume) E' + (ν.prod volume) (E \ E') := measure_union_le _ _
        _ ≤ _ := add_le_add le_rfl hdel
    have h2 : ENNReal.ofReal K⁻¹ = ENNReal.ofReal (3 / (4 * K)) + ENNReal.ofReal (1 / (4 * K)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; field_simp; ring
    rw [h2] at h1
    have h3 : ENNReal.ofReal (3 / (4 * K)) ≤ (ν.prod volume) E' :=
      (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h3
    -- `2 N^η ≤ N^ε`
    have hε0 : 0 < N ^ ε := Real.rpow_pos_of_pos hN0 _
    rw [inv_le_comm₀ hε0 (by positivity)]
    have : (3 / (4 * K))⁻¹ = 4 * K / 3 := by field_simp
    rw [this]
    have h2K : 2 * K ≤ N ^ ε := hc2
    linarith
  refine ⟨E', hE'sub, ?_, ?_⟩
  · have hle : K ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    exact (hU.mono_bound hK0 hle hζ.le).restrict_labels hE'm hE'sub hmass
  · intro t q r a hq hqr hr
    obtain ⟨k, hkJ, hwq, hqw⟩ := exists_grid_width hN1 hJ hc hq (hqr.trans hr)
    set w := N ^ (-(c * k / J)) with hw_def
    have hwws : w ∈ ws := Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩
    have hw0 : 0 < w := Real.rpow_pos_of_pos hN0 _
    have hq0 : 0 < q := hw0.trans_le hwq
    have hτw : 0 < τ w := by simp only [hτ_def]; positivity
    obtain ⟨C, hC, hmem⟩ := floorSet_localCount hU hK1 hζ ws τ t q r a w hwws hw0 hwq hτw
      (hq.trans hqr) hqr hr
    refine ⟨C, hC.trans ?_, hmem⟩
    -- `2 · 600 K⁴ r^d / (w^d/K') ≤ N^ε (r/q)^d`
    have hr0 : 0 < r := hq0.trans_le hqr
    have hrq : (r / w) ^ d = (r / q) ^ d * (q / w) ^ d := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      congr 1; field_simp
    have hqw1 : 1 ≤ q / w := by rw [le_div_iff₀ hw0]; linarith
    have hqwd : (q / w) ^ d ≤ N ^ (c / J) := by
      calc (q / w) ^ d ≤ (q / w) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hqw1 hd1.le
        _ = q / w := Real.rpow_one _
        _ ≤ N ^ (c / J) := by rw [div_le_iff₀ hw0]; linarith
    have hK6 : K ^ 6 = N ^ (6 * η) := by
      rw [hK_def, JetFit.rpow_mul_nat hN0]; push_cast; ring_nf
    have hrqd : 0 ≤ (r / q) ^ d := Real.rpow_nonneg (by positivity) _
    have e1 : 2 * (600 * K ^ 4 * r ^ d / τ w) = 1200 * K ^ 4 * K' * (r / w) ^ d := by
      simp only [hτ_def]
      rw [Real.div_rpow hr0.le hw0.le]
      have : 0 < w ^ d := Real.rpow_pos_of_pos hw0 _
      field_simp
      norm_num
    rw [e1, hrq]
    have e2 : 1200 * K ^ 4 * K' = 4800 * ((J : ℝ) + 1) * N ^ (6 * η) := by
      rw [hK'_def, ← hK6]; ring
    rw [e2]
    have hNcJ : N ^ (6 * η) * N ^ (c / J) = N ^ (6 * η + c / J) := by
      rw [← Real.rpow_add hN0]
    calc 4800 * ((J : ℝ) + 1) * N ^ (6 * η) * ((r / q) ^ d * (q / w) ^ d)
        ≤ 4800 * ((J : ℝ) + 1) * N ^ (6 * η) * ((r / q) ^ d * N ^ (c / J)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hqwd hrqd
      _ = (4800 * ((J : ℝ) + 1) * N ^ (6 * η + c / J)) * (r / q) ^ d := by
          rw [← hNcJ]; ring
      _ ≤ N ^ ε * (r / q) ^ d := mul_le_mul_of_nonneg_right hc1 hrqd

end Submission.Obl.k4_fixed_prior_chart_regularization.Reg

end
