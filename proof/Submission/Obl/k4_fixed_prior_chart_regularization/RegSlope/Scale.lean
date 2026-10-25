-- Adapted from LOT tree g-oai-074, obligation o245, session x0854, commit 3602b8f657fd9f9293587a9dd3e1bdba2451d373.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/RegSlope/Scale.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope.Entries

/-!
# Slope regularization: one width

At one width `s = N^(-c')`: keep the long labels' pair-prepared incidences whose code of
`(β, γ)` is heavy in its static group (`scale_codes`). This costs `2/K₂` (pair durations) plus
`(4K + 5)² N^(-η)` (light codes in the at most `(4K/s + 5)²` occurring groups), and the occurring
entries number at most `(1/s + 1) / (s^(2+d) N^(-ε₂))`.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope

open FirstJet Submission.Obl.k4_scalar_coefficient_clustering

/-- The occurring static groups at width `s`. -/
def groupBox (s K : ℝ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(⌈2 * K / s⌉ + 1)) (⌈2 * K / s⌉ + 1)

theorem groupBox_card_le {s K : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) :
    ((groupBox s K).card : ℝ) * s ^ 2 ≤ (4 * K + 5) ^ 2 := by
  have hR0 : 0 ≤ ⌈2 * K / s⌉ + 1 := by
    have : (0 : ℝ) ≤ ⌈2 * K / s⌉ := (by positivity : (0 : ℝ) ≤ 2 * K / s).trans (Int.le_ceil _)
    have : (0 : ℤ) ≤ ⌈2 * K / s⌉ := by exact_mod_cast this
    omega
  rw [groupBox, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [card_Icc_symm hR0]
  have hc : (⌈2 * K / s⌉ : ℝ) < 2 * K / s + 1 := Int.ceil_lt_add_one _
  have h1 : (2 * (((⌈2 * K / s⌉ + 1 : ℤ)) : ℝ) + 1) * s ≤ 4 * K + 5 := by
    push_cast
    have : (2 * K / s) * s = 2 * K := by field_simp
    nlinarith
  have h0 : 0 ≤ (2 * (((⌈2 * K / s⌉ + 1 : ℤ)) : ℝ) + 1) * s := by
    have : (0 : ℝ) ≤ ((⌈2 * K / s⌉ + 1 : ℤ) : ℝ) := by exact_mod_cast hR0
    positivity
  calc (2 * (((⌈2 * K / s⌉ + 1 : ℤ)) : ℝ) + 1) ^ 2 * s ^ 2
      = ((2 * (((⌈2 * K / s⌉ + 1 : ℤ)) : ℝ) + 1) * s) ^ 2 := by ring
    _ ≤ (4 * K + 5) ^ 2 := pow_le_pow_left₀ h0 h1 2

theorem group_mem_groupBox {Ω : Type*} {y : Ω → Fin 2 → ℝ} {K s : ℝ} (hs : 0 < s)
    (hy : ∀ l i, |y l i| ≤ K) (l : Ω) : (fun i => ⌊y l i / s⌋) ∈ groupBox s K := by
  rw [groupBox, Fintype.mem_piFinset]
  intro i
  have hK : 0 ≤ K := (abs_nonneg _).trans (hy l i)
  exact floor_mem_range hs ((hy l i).trans (by linarith))

/-- **Heavy codes at one width.** -/
theorem scale_codes {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ) (hd : 0 ≤ d) (hd1 : d < 1)
    {c' ε₂ ηc N : ℝ} (hN : 0 < N) (hHC : HeavyCoverAt d c' ε₂ ηc N)
    (hs : ζ ≤ N ^ (-c')) (hs1 : N ^ (-c') ≤ 1) {δ K₂ : ℝ} (hδ : 0 < δ)
    (hK₂ : 0 < K₂) (n1 : 2 * K ≤ N ^ ηc) (n2 : 4 * ((4 * K + 5) * K) / δ ≤ N ^ ηc)
    (n3 : 2 * (K₂ * ((4 * K + 3) * K)) ≤ N ^ ηc) :
    ∃ C : Set (Ω × ℝ), MeasurableSet C ∧ C ⊆ E ∩ longLabels E δ ×ˢ univ ∧
      (ν.prod volume) ((E ∩ longLabels E δ ×ˢ univ) \ C) ≤
        ENNReal.ofReal (2 / K₂ + (4 * K + 5) ^ 2 * N ^ (-ηc)) ∧
      ∃ Ent : Finset ((Fin 2 → ℤ) × (Fin 3 → ℤ) × ℤ),
        (Ent.card : ℝ) * ((N ^ (-c')) ^ 2 * ((N ^ (-c')) ^ d * N ^ (-ε₂))) ≤ 1 / N ^ (-c') + 1 ∧
        ∀ p ∈ C, entry (N ^ (-c')) y β γ p ∈ Ent := by
  classical
  set s := N ^ (-c') with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hN _
  have hK : 0 ≤ K := (abs_nonneg _).trans (hU.bound_F 0 0)
  set L := longLabels E δ with hLdef
  have hLm : MeasurableSet L := measurableSet_longLabels hU.measurableSet_E δ
  set Ea := E ∩ L ×ˢ univ with hEadef
  have hEam : MeasurableSet Ea := hU.measurableSet_E.inter (hLm.prod MeasurableSet.univ)
  have hEa01 : Ea ⊆ univ ×ˢ Icc (0 : ℝ) 1 := inter_subset_left.trans hU.subset_E
  -- the heavy codes of each group
  have hG := fun Y => group_cluster hU hd hd1 hN hHC hs hs1 hU.measurableSet_E subset_rfl hδ hK₂
    n1 n2 n3 Y
  choose G hGcard hGleft using hG
  set Eb := pairGood Ea s K₂ with hEbdef
  have hEbm : MeasurableSet Eb := measurableSet_pairGood hEam s K₂
  have ha := measurable_coefVec hU.measurable_β hU.measurable_γ
  have hgrp : Measurable fun l : Ω => fun i => ⌊y l i / s⌋ :=
    measurable_pi_iff.mpr fun i =>
      Int.measurable_floor.comp (((measurable_pi_apply i).comp hU.measurable_y).div_const s)
  set light : Set (Ω × ℝ) :=
    {p | coefficientCode s (coefVec β γ p.1) ∉ G (fun i => ⌊y p.1 i / s⌋)} with hlight
  have hlightm : MeasurableSet light := by
    have : Measurable fun p : Ω × ℝ =>
        (coefficientCode s (coefVec β γ p.1), fun i => ⌊y p.1 i / s⌋) :=
      ((measurable_coefficientCode s).comp (ha.comp measurable_fst)).prodMk
        (hgrp.comp measurable_fst)
    exact this (Set.to_countable {x : (Fin 3 → ℤ) × (Fin 2 → ℤ) | x.1 ∉ G x.2}).measurableSet
  refine ⟨Eb \ light, hEbm.diff hlightm, fun p hp => pairGood_subset _ _ _ hp.1, ?_, ?_⟩
  · -- the cost
    have h1 : (ν.prod volume) (Ea \ Eb) ≤ ENNReal.ofReal (2 / K₂) :=
      pairGood_mass hEam hEa01 hs0 hs1 hK₂
    have h2 : (ν.prod volume) (Eb ∩ light) ≤ ENNReal.ofReal ((4 * K + 5) ^ 2 * N ^ (-ηc)) := by
      calc (ν.prod volume) (Eb ∩ light)
          ≤ (ν.prod volume) (⋃ Y ∈ groupBox s K, groupSet E δ s K₂ y Y ∩
              {p | coefficientCode s (coefVec β γ p.1) ∉ G Y}) := by
            apply measure_mono
            rintro p ⟨hpb, hpl⟩
            refine mem_biUnion (group_mem_groupBox hs0 hU.bound_y p.1) ⟨⟨hpb, ?_⟩, hpl⟩
            exact ⟨fun i => rfl, trivial⟩
        _ ≤ ∑ Y ∈ groupBox s K, (ν.prod volume) (groupSet E δ s K₂ y Y ∩
              {p | coefficientCode s (coefVec β γ p.1) ∉ G Y}) := measure_biUnion_finset_le _ _
        _ ≤ ∑ _Y ∈ groupBox s K, ENNReal.ofReal (s ^ 2 * N ^ (-ηc)) :=
            Finset.sum_le_sum fun Y _ => hGleft Y
        _ = ENNReal.ofReal ((groupBox s K).card * s ^ 2 * N ^ (-ηc)) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            congr 1; ring
        _ ≤ ENNReal.ofReal ((4 * K + 5) ^ 2 * N ^ (-ηc)) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_right (groupBox_card_le hs0 hs1 hK)
              (Real.rpow_nonneg hN.le _)
    calc (ν.prod volume) (Ea \ (Eb \ light)) ≤ (ν.prod volume) ((Ea \ Eb) ∪ (Eb ∩ light)) := by
          apply measure_mono
          intro p hp
          by_cases hb : p ∈ Eb
          · right; exact ⟨hb, by_contra fun hl => hp.2 ⟨hb, hl⟩⟩
          · left; exact ⟨hp.1, hb⟩
      _ ≤ (ν.prod volume) (Ea \ Eb) + (ν.prod volume) (Eb ∩ light) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 / K₂) + ENNReal.ofReal ((4 * K + 5) ^ 2 * N ^ (-ηc)) :=
          add_le_add h1 h2
      _ = ENNReal.ofReal (2 / K₂ + (4 * K + 5) ^ 2 * N ^ (-ηc)) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  · -- the occurring entries
    set J : ℕ := ⌊1 / s⌋₊ with hJ
    set Ent : Finset ((Fin 2 → ℤ) × (Fin 3 → ℤ) × ℤ) :=
      (groupBox s K).biUnion fun Y => (G Y).biUnion fun q =>
        (Finset.range (J + 1)).image (fun j : ℕ => (Y, q, (j : ℤ))) with hEnt
    refine ⟨Ent, ?_, ?_⟩
    · have hfl : 0 < s ^ 2 * (s ^ d * N ^ (-ε₂)) := by positivity
      -- the groups' masses add up to at most one
      have hsumG : ∑ Y ∈ groupBox s K, ((G Y).card : ℝ) * (s ^ 2 * (s ^ d * N ^ (-ε₂))) ≤ 1 := by
        have hdisj : ((groupBox s K : Set (Fin 2 → ℤ))).PairwiseDisjoint
            fun Y => groupSet E δ s K₂ y Y := by
          intro Y _ Y' _ hne
          refine Set.disjoint_left.mpr fun p hp hp' => hne ?_
          funext i
          exact (hp.2.1 i).symm.trans (hp'.2.1 i)
        have hm : ∀ Y, MeasurableSet (groupSet E δ s K₂ y Y) := fun Y =>
          hEbm.inter ((measurableSet_group hU.measurable_y s Y).prod MeasurableSet.univ)
        have hfin : ∀ Y, (ν.prod volume) (groupSet E δ s K₂ y Y) ≠ ⊤ := fun Y =>
          ne_top_of_le_ne_top (b := (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1))
            (by rw [Measure.prod_prod]; simp) (measure_mono fun p hp => hEa01 hp.1.1)
        calc ∑ Y ∈ groupBox s K, ((G Y).card : ℝ) * (s ^ 2 * (s ^ d * N ^ (-ε₂)))
            ≤ ∑ Y ∈ groupBox s K, (ν.prod volume).real (groupSet E δ s K₂ y Y) :=
              Finset.sum_le_sum fun Y _ => hGcard Y
          _ = ((ν.prod volume) (⋃ Y ∈ groupBox s K, groupSet E δ s K₂ y Y)).toReal := by
              rw [measure_biUnion_finset hdisj fun Y _ => hm Y, ENNReal.toReal_sum fun Y _ => hfin Y]
              rfl
          _ ≤ ((ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1)).toReal := by
              apply ENNReal.toReal_mono (by rw [Measure.prod_prod]; simp)
              exact measure_mono (iUnion₂_subset fun Y _ p hp => hEa01 hp.1.1)
          _ = 1 := by rw [Measure.prod_prod]; simp
      have hcard : (Ent.card : ℝ) ≤ (J + 1) * ∑ Y ∈ groupBox s K, ((G Y).card : ℝ) := by
        calc (Ent.card : ℝ) ≤ ∑ Y ∈ groupBox s K, (((G Y).biUnion fun q =>
              (Finset.range (J + 1)).image (fun j : ℕ => (Y, q, (j : ℤ)))).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
          _ ≤ ∑ Y ∈ groupBox s K, ∑ q ∈ G Y, (((Finset.range (J + 1)).image
                (fun j : ℕ => (Y, q, (j : ℤ)))).card : ℝ) := by
              refine Finset.sum_le_sum fun Y _ => ?_
              exact_mod_cast Finset.card_biUnion_le
          _ ≤ ∑ Y ∈ groupBox s K, ∑ _q ∈ G Y, ((J : ℝ) + 1) := by
              refine Finset.sum_le_sum fun Y _ => Finset.sum_le_sum fun q _ => ?_
              have := Finset.card_image_le (s := Finset.range (J + 1))
                (f := fun j : ℕ => (Y, q, (j : ℤ)))
              rw [Finset.card_range] at this
              exact_mod_cast this
          _ = (J + 1) * ∑ Y ∈ groupBox s K, ((G Y).card : ℝ) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun Y _ => ?_
              rw [Finset.sum_const, nsmul_eq_mul]; ring
      have hJs : (J : ℝ) ≤ 1 / s := Nat.floor_le (by positivity)
      calc (Ent.card : ℝ) * (s ^ 2 * (s ^ d * N ^ (-ε₂)))
          ≤ ((J + 1) * ∑ Y ∈ groupBox s K, ((G Y).card : ℝ)) * (s ^ 2 * (s ^ d * N ^ (-ε₂))) :=
            mul_le_mul_of_nonneg_right hcard hfl.le
        _ = (J + 1) * ∑ Y ∈ groupBox s K, ((G Y).card : ℝ) * (s ^ 2 * (s ^ d * N ^ (-ε₂))) := by
            rw [mul_assoc, Finset.sum_mul]
        _ ≤ (J + 1) * 1 := by gcongr
        _ ≤ 1 / s + 1 := by linarith
    · rintro p ⟨hpb, hpl⟩
      have ht01 := (hEa01 hpb.1).2
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.floor_nonneg.mpr (div_nonneg ht01.1 hs0.le))
      have hnJ : n ≤ J := by
        have : (n : ℝ) ≤ p.2 / s := by rw [← Int.cast_natCast, ← hn]; exact Int.floor_le _
        exact Nat.le_floor (this.trans (div_le_div_of_nonneg_right ht01.2 hs0.le))
      have hq : coefficientCode s (coefVec β γ p.1) ∈ G (fun i => ⌊y p.1 i / s⌋) := by
        by_contra h; exact hpl h
      rw [hEnt, Finset.mem_biUnion]
      refine ⟨_, group_mem_groupBox hs0 hU.bound_y p.1, Finset.mem_biUnion.mpr
        ⟨_, hq, Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), ?_⟩⟩⟩
      simp only [entry, hn]
