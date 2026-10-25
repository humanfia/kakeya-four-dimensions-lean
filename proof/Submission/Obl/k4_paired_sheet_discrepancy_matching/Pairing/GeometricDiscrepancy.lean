/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/GeometricDiscrepancy.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.DiscrepancyGroups

/-! The per-group estimate adapts x0531's o156 DiscrepancyGroups.grp_le_light
(c7cfd90 in this LOT tree). Keeping the actual dyadic scale in the density
estimate permits geometrically decreasing light thresholds. -/

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open Set MeasureTheory Metric

variable {ι Λ Ω : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Λ] [MeasurableSpace Ω]
variable (J : JetData) (S : DiscSetup ι Λ Ω) (M₀ : ℝ) (θ : Λ → ℝ)

lemma grp_le_light_at_scale {d₀ ε₀ R₀ ε : ℝ} (hmb : MatchBound d₀ ε₀ R₀) (hR₀ : 2 ≤ R₀) (hε : 0 < ε)
    (hεε₀ : ε ≤ ε₀) (g : GLabel Λ J) (hM₀ : 0 < M₀) (hθ : 0 < θ g.2.1)
    (hR : R₀ * (2 * S.Δ) ≤ M₀) (hC : 3 * J.C₂ ≤ (M₀ / (2 * S.Δ)) ^ ε)
    (hρ : S.ρ g.2.1 * (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (-ε) ≤ θ g.2.1 / 2)
    (Γ : ℝ) (hΓ : Γ / θ g.2.1 ≤ (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (d₀ + ε))
    (hband : ∀ i, S.lab i = g.2.1 → S.Pm {p | S.lab (S.src p) = S.lab i ∧
      ‖S.φ i (emb (S.x p)) - (S.w p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ g.1)} ≤ ENNReal.ofReal Γ) :
    S.Pm (grp J S M₀ g) ≤
      2 * (ENNReal.ofReal (θ g.2.1) * ((srcSet J S M₀ g).card + (witSet J S M₀ g).card)) := by
  haveI := S.finite
  have hΔ := S.Δ_pos
  set m := S.Pm (grp J S M₀ g)
  have hmfin : m ≠ ⊤ := measure_ne_top _ _
  set n := max (heavySrc J S M₀ θ g).card (heavyWit J S M₀ θ g).card
  have hcore := core_le J S M₀ θ hmb hR₀ hε hεε₀ g hM₀ hθ hR hC Γ hΓ hband
  have hn : (n : ENNReal) * ENNReal.ofReal (θ g.2.1) ≤ m := by
    rcases max_choice (heavySrc J S M₀ θ g).card (heavyWit J S M₀ θ g).card with h | h
    · rw [show n = _ from h]; exact heavySrc_card_le J S M₀ θ g
    · rw [show n = _ from h]; exact heavyWit_card_le J S M₀ θ g
  have hcore' : S.Pm (core J S M₀ θ g) ≤ m / 2 := by
    refine hcore.trans ?_
    have h1 : S.ρ g.2.1 * (n : ℝ) * (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (-ε) ≤ (n : ℝ) * θ g.2.1 / 2 := by
      have := S.ρ_nonneg g.2.1
      calc S.ρ g.2.1 * (n : ℝ) * (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (-ε)
          = (n : ℝ) * (S.ρ g.2.1 * (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (-ε)) := by ring
        _ ≤ (n : ℝ) * (θ g.2.1 / 2) := mul_le_mul_of_nonneg_left hρ (by positivity)
        _ = (n : ℝ) * θ g.2.1 / 2 := by ring
    calc ENNReal.ofReal (S.ρ g.2.1 * (n : ℝ) * (M₀ * 2 ^ g.1 / (2 * S.Δ)) ^ (-ε))
        ≤ ENNReal.ofReal ((n : ℝ) * θ g.2.1 / 2) := ENNReal.ofReal_le_ofReal h1
      _ = (n : ENNReal) * ENNReal.ofReal (θ g.2.1) / 2 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
      _ ≤ m / 2 := by gcongr
  have hlight := light_le J S M₀ θ g
  have hsplit : m ≤ S.Pm (core J S M₀ θ g) + S.Pm (grp J S M₀ g \ core J S M₀ θ g) := by
    calc m ≤ S.Pm (core J S M₀ θ g ∪ (grp J S M₀ g \ core J S M₀ θ g)) := by
          apply measure_mono
          intro p hp
          by_cases hc : p ∈ core J S M₀ θ g
          · exact Or.inl hc
          · exact Or.inr ⟨hp, hc⟩
      _ ≤ _ := measure_union_le _ _
  set L := ENNReal.ofReal (θ g.2.1) * ((srcSet J S M₀ g).card + (witSet J S M₀ g).card)
  have h2 : m / 2 + m / 2 ≤ m / 2 + L := by
    rw [ENNReal.add_halves]
    exact hsplit.trans (add_le_add hcore' hlight)
  have h3 : m / 2 ≤ L := (ENNReal.add_le_add_iff_left (ENNReal.div_ne_top hmfin (by norm_num))).mp h2
  calc m = 2 * (m / 2) := (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).symm
    _ ≤ 2 * L := by gcongr

/-- A finite set with at most `B` elements per scale has a geometric weighted
count bounded independently of its largest scale. -/
theorem geometric_fiber_sum_le {α : Type*} [DecidableEq α]
    (G : Finset α) (scale : α → ℕ) (B : ℕ) {χ : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ < 1)
    (hcard : ∀ k, (G.filter (fun g => scale g = k)).card ≤ B) :
    (∑ g ∈ G, χ ^ scale g) ≤ (B : ℝ) / (1 - χ) := by
  let K := G.image scale
  have hnorm : ‖χ‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hχ] using hχ1
  have hsum : (∑ k ∈ K, χ ^ k) ≤ (1 - χ)⁻¹ := by
    calc _ ≤ ∑' k : ℕ, χ ^ k :=
          Summable.sum_le_tsum K (fun _ _ => pow_nonneg hχ _)
            (summable_geometric_of_norm_lt_one hnorm)
      _ = _ := tsum_geometric_of_norm_lt_one hnorm
  calc
    _ = ∑ k ∈ K, ∑ g ∈ G.filter (fun g => scale g = k), χ ^ scale g :=
      (Finset.sum_fiberwise_of_maps_to (fun g hg => Finset.mem_image_of_mem scale hg) _).symm
    _ ≤ ∑ k ∈ K, (B : ℝ) * χ ^ k := by
      apply Finset.sum_le_sum
      intro k _
      have heq : (∑ g ∈ G.filter (fun g => scale g = k), χ ^ scale g) =
          ((G.filter (fun g => scale g = k)).card : ℝ) * χ ^ k := by
        calc _ = ∑ _g ∈ G.filter (fun g => scale g = k), χ ^ k :=
              Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.mp hg).2])
          _ = _ := by simp [nsmul_eq_mul]
      rw [heq]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard k) (pow_nonneg hχ _)
    _ = (B : ℝ) * ∑ k ∈ K, χ ^ k := (Finset.mul_sum _ _ _).symm
    _ ≤ (B : ℝ) * (1 - χ)⁻¹ := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = _ := (div_eq_mul_inv _ _).symm

noncomputable def srcLabelsAt (k : ℕ) (i : ι) : Finset (GLabel Λ J) :=
  (Fintype.piFinset (fun vj : ↥J.V × Fin J.q =>
    Finset.Icc (sheetCube J S.φ M₀ k i vj - cubeRadius J)
      (sheetCube J S.φ M₀ k i vj + cubeRadius J))).image
    (fun Q => (k, S.lab i, sheetCube J S.φ M₀ k i, Q))

noncomputable def witLabelsAt (k : ℕ) (i : ι) : Finset (GLabel Λ J) :=
  (Fintype.piFinset (fun vj : ↥J.V × Fin J.q =>
    Finset.Icc (sheetCube J S.φ M₀ k i vj - cubeRadius J)
      (sheetCube J S.φ M₀ k i vj + cubeRadius J))).image
    (fun Q => (k, S.lab i, Q, sheetCube J S.φ M₀ k i))

theorem card_srcLabelsAt_le (k : ℕ) (i : ι) :
    (srcLabelsAt J S M₀ k i).card ≤
      (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) :=
  Finset.card_image_le.trans (card_box J _).le

theorem card_witLabelsAt_le (k : ℕ) (i : ι) :
    (witLabelsAt J S M₀ k i).card ≤
      (2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) :=
  Finset.card_image_le.trans (card_box J _).le

theorem mem_srcLabelsAt {g : GLabel Λ J} {i : ι} (hM₀ : 0 < M₀)
    (hi : i ∈ srcSet J S M₀ g) : g ∈ srcLabelsAt J S M₀ g.1 i := by
  classical
  obtain ⟨p, hp, hpi⟩ := (Finset.mem_filter.mp hi).2
  have hspec := mem_grp_spec J S M₀ hp hM₀
  simp only [srcLabelsAt, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨g.2.2.2, fun vj => ?_, ?_⟩
  · have hn := cube_neighbor J S M₀ hp hM₀ vj
    rw [hpi] at hspec
    rw [hspec.2.2.2.1]
    constructor <;> linarith [abs_le.mp hn]
  · rw [← hpi, hspec.2.2.1, hspec.2.2.2.1]

theorem mem_witLabelsAt {g : GLabel Λ J} {i : ι} (hM₀ : 0 < M₀)
    (hi : i ∈ witSet J S M₀ g) : g ∈ witLabelsAt J S M₀ g.1 i := by
  classical
  obtain ⟨p, hp, hpi⟩ := (Finset.mem_filter.mp hi).2
  have hspec := mem_grp_spec J S M₀ hp hM₀
  simp only [witLabelsAt, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨g.2.2.1, fun vj => ?_, ?_⟩
  · have hn := cube_neighbor J S M₀ hp hM₀ vj
    rw [hpi] at hspec
    rw [hspec.2.2.2.2]
    constructor <;> linarith [abs_le.mp hn]
  · rw [← hpi, ← S.lab_eq p, hspec.2.2.1, hspec.2.2.2.2]

theorem weighted_group_card_sum_le (E : GLabel Λ J → Finset ι)
    (hlabel : ∀ g i, i ∈ E g → S.lab i = g.2.1)
    (B : ℕ) {χ : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ < 1) (hθ : ∀ l, 0 ≤ θ l)
    (hcount : ∀ i k,
      ((groupLabels J S M₀).filter (fun g => i ∈ E g ∧ g.1 = k)).card ≤ B) :
    (∑ g ∈ groupLabels J S M₀, θ g.2.1 * χ ^ g.1 * (E g).card) ≤
      ((B : ℝ) / (1 - χ)) * ∑ i, θ (S.lab i) := by
  classical
  have hscale (i : ι) :
      (∑ g ∈ (groupLabels J S M₀).filter (fun g => i ∈ E g), χ ^ g.1) ≤
        (B : ℝ) / (1 - χ) := by
    apply geometric_fiber_sum_le _ Prod.fst B hχ hχ1
    intro k
    simpa only [Finset.filter_filter] using hcount i k
  calc
    _ = ∑ g ∈ groupLabels J S M₀, ∑ i : ι,
        if i ∈ E g then θ (S.lab i) * χ ^ g.1 else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [Finset.sum_congr rfl (fun i hi => by rw [hlabel g i hi])]
      simp [mul_comm, mul_left_comm]
    _ = ∑ i : ι, ∑ g ∈ groupLabels J S M₀,
        if i ∈ E g then θ (S.lab i) * χ ^ g.1 else 0 := Finset.sum_comm
    _ = ∑ i : ι, θ (S.lab i) *
        (∑ g ∈ (groupLabels J S M₀).filter (fun g => i ∈ E g), χ ^ g.1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter, Finset.mul_sum]
    _ ≤ ∑ i : ι, θ (S.lab i) * ((B : ℝ) / (1 - χ)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hscale i) (hθ _))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

theorem geometric_srcSet_sum_le (hM₀ : 0 < M₀) {χ : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ < 1) (hθ : ∀ l, 0 ≤ θ l) :
    (∑ g ∈ groupLabels J S M₀, θ g.2.1 * χ ^ g.1 * (srcSet J S M₀ g).card) ≤
      (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
        (1 - χ) * ∑ i, θ (S.lab i) := by
  apply weighted_group_card_sum_le J S M₀ θ (srcSet J S M₀)
    (fun g i hi => lab_of_mem_srcSet J S M₀ hM₀ hi) _ hχ hχ1 hθ
  intro i k
  refine (Finset.card_le_card ?_).trans (card_srcLabelsAt_le J S M₀ k i)
  intro g hg
  obtain ⟨hi, hk⟩ := (Finset.mem_filter.mp hg).2
  rw [← hk]
  exact mem_srcLabelsAt J S M₀ hM₀ hi

theorem geometric_witSet_sum_le (hM₀ : 0 < M₀) {χ : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ < 1) (hθ : ∀ l, 0 ≤ θ l) :
    (∑ g ∈ groupLabels J S M₀, θ g.2.1 * χ ^ g.1 * (witSet J S M₀ g).card) ≤
      (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
        (1 - χ) * ∑ i, θ (S.lab i) := by
  apply weighted_group_card_sum_le J S M₀ θ (witSet J S M₀)
    (fun g i hi => lab_of_mem_witSet J S M₀ hM₀ hi) _ hχ hχ1 hθ
  intro i k
  refine (Finset.card_le_card ?_).trans (card_witLabelsAt_le J S M₀ k i)
  intro g hg
  obtain ⟨hi, hk⟩ := (Finset.mem_filter.mp hg).2
  rw [← hk]
  exact mem_witLabelsAt J S M₀ hM₀ hi

/-- Geometrically decreasing light-label thresholds sum over every discrepancy
scale. No bound on the sizes or range of the algebraic sheets is required. -/
theorem discrepancy_mass_le_geometric {d₀ ε₀ R₀ ε χ : ℝ}
    (hmb : MatchBound d₀ ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) (hM₀ : 0 < M₀)
    (hχ : 0 < χ) (hχ1 : χ < 1) (hθ : ∀ l, 0 < θ l)
    (hR : R₀ * (2 * S.Δ) ≤ M₀) (hC : 3 * J.C₂ ≤ (M₀ / (2 * S.Δ)) ^ ε)
    (hρ : ∀ l k, S.ρ l * (M₀ * 2 ^ k / (2 * S.Δ)) ^ (-ε) ≤ θ l * χ ^ k / 2)
    (Γ : Λ → ℕ → ℝ)
    (hΓ : ∀ l k, Γ l k / (θ l * χ ^ k) ≤
      (M₀ * 2 ^ k / (2 * S.Δ)) ^ (d₀ + ε))
    (hband : ∀ i k, S.Pm {p | S.lab (S.src p) = S.lab i ∧
      ‖S.φ i (emb (S.x p)) - (S.w p : ℂ)‖ ≤ 2 * (M₀ * 2 ^ k)} ≤
        ENNReal.ofReal (Γ (S.lab i) k)) :
    S.Pm {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
      M₀ ≤ ‖S.φ (S.src p) (emb y) - S.φ (S.wit p) (emb y)‖} ≤
        ENNReal.ofReal (4 *
          (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
            (1 - χ) * ∑ i, θ (S.lab i)) := by
  classical
  have hθ0 : ∀ l, 0 ≤ θ l := fun l => (hθ l).le
  have hsub : {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
      M₀ ≤ ‖S.φ (S.src p) (emb y) - S.φ (S.wit p) (emb y)‖} ⊆
      ⋃ g ∈ groupLabels J S M₀, grp J S M₀ g := by
    rintro p ⟨y, hy, hle⟩
    exact bad_subset_iUnion_grp J S M₀ (hle.trans (le_sheetDisc S.sheet _ _ hy))
  have hgrp (g : GLabel Λ J) : S.Pm (grp J S M₀ g) ≤
      ENNReal.ofReal (2 * (θ g.2.1 * χ ^ g.1 * (srcSet J S M₀ g).card +
        θ g.2.1 * χ ^ g.1 * (witSet J S M₀ g).card)) := by
    have hθg : 0 < θ g.2.1 * χ ^ g.1 := mul_pos (hθ _) (pow_pos hχ _)
    refine (grp_le_light_at_scale J S M₀ (fun l => θ l * χ ^ g.1)
      hmb hR₀ hε hεε₀ g hM₀ hθg hR hC (hρ _ _) (Γ g.2.1 g.1) (hΓ _ _) ?_).trans_eq ?_
    · intro i hi
      rw [← hi]
      exact hband i g.1
    · rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_add
        (mul_nonneg hθg.le (Nat.cast_nonneg _)) (mul_nonneg hθg.le (Nat.cast_nonneg _)),
        ENNReal.ofReal_mul hθg.le, ENNReal.ofReal_mul hθg.le,
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, mul_add]
  have hs := geometric_srcSet_sum_le J S M₀ θ hM₀ hχ.le hχ1 hθ0
  have hw := geometric_witSet_sum_le J S M₀ θ hM₀ hχ.le hχ1 hθ0
  calc
    _ ≤ S.Pm (⋃ g ∈ groupLabels J S M₀, grp J S M₀ g) := measure_mono hsub
    _ ≤ ∑ g ∈ groupLabels J S M₀, S.Pm (grp J S M₀ g) := measure_biUnion_finset_le _ _
    _ ≤ ∑ g ∈ groupLabels J S M₀, ENNReal.ofReal
        (2 * (θ g.2.1 * χ ^ g.1 * (srcSet J S M₀ g).card +
          θ g.2.1 * χ ^ g.1 * (witSet J S M₀ g).card)) :=
      Finset.sum_le_sum (fun g _ => hgrp g)
    _ = ENNReal.ofReal (∑ g ∈ groupLabels J S M₀,
        2 * (θ g.2.1 * χ ^ g.1 * (srcSet J S M₀ g).card +
          θ g.2.1 * χ ^ g.1 * (witSet J S M₀ g).card)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro g _
      have := hθ0 g.2.1
      have := pow_nonneg hχ.le g.1
      positivity
    _ ≤ ENNReal.ofReal (4 *
        (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
          (1 - χ) * ∑ i, θ (S.lab i)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      calc _ ≤ 2 * (
          (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
            (1 - χ) * ∑ i, θ (S.lab i) +
          (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
            (1 - χ) * ∑ i, θ (S.lab i)) := by gcongr
        _ = _ := by ring

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
