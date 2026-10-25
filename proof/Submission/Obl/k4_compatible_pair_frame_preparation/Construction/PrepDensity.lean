-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepDensity.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/PrepDensity.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepBase
import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.NormalMeasure
import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.Saturation

/-!
# Capped densities of pair masses in base coordinates

The original law `(ν × vol)|_E` maps under `obs B δ` to `(vol × count).withDensity g`.
On incidences where `g ∘ obs ≤ cap` and whose observation lies in a set `Y` with at most
`n` hidden bins over each spacetime point, the spacetime marginal is at most
`cap · n · vol` (`capped_obs_mass_le`).  For the two-time pair law with the second time
in `I`, and base coordinates through `movingBasePoint`, this gives
`vol I · cap · n · (a³ |det Q| / q) · vol U` (`capped_pair_base_le`).

The hidden-bin sets used are the closed bins meeting a regular sublevel set of a test
(`hidClosed`, at most `16 (1 + ε / (β h))` bins) and the bins meeting a band
`|B x₃ - G| ≤ ρ` (`bandBins`, at most `2 ρ / δ + 2` bins).
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open MeasureTheory Set MvPolynomial
open scoped ENNReal

/-- **One-time capped mass.** -/
theorem capped_obs_mass_le (ν : Measure (ℕ × (Fin 6 → ℝ))) [SFinite ν]
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) {B δ : ℝ}
    (g : EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞) (hg : Measurable g)
    (hmap : Measure.map (obs B δ) ((ν.prod volume).restrict E) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity g)
    (Y : Set (EuclideanSpace ℝ (Fin 3) × ℤ)) (hY : MeasurableSet Y) (n : ℝ≥0∞)
    (hfib : ∀ z, Measure.count (Prod.mk z ⁻¹' Y) ≤ n) (cap : ℝ≥0∞)
    (X : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hXE : X ⊆ E)
    (hX : ∀ p ∈ X, g (obs B δ p) ≤ cap ∧ obs B δ p ∈ Y)
    (V : Set (EuclideanSpace ℝ (Fin 3))) (hV : MeasurableSet V) :
    (ν.prod volume) (X ∩ {p | (obs B δ p).1 ∈ V}) ≤ cap * n * volume V := by
  set Z : Set (EuclideanSpace ℝ (Fin 3) × ℤ) := (Prod.fst ⁻¹' V) ∩ Y ∩ {o | g o ≤ cap} with hZ
  have hZm : MeasurableSet Z :=
    ((measurable_fst hV).inter hY).inter (measurableSet_le hg measurable_const)
  have hsub : X ∩ {p | (obs B δ p).1 ∈ V} ⊆ E ∩ obs B δ ⁻¹' Z := by
    rintro p ⟨hpX, hpV⟩
    exact ⟨hXE hpX, ⟨⟨hpV, (hX p hpX).2⟩, (hX p hpX).1⟩⟩
  have hobs := measurable_obs B δ
  have hfib' : ∀ z, Measure.count (Prod.mk z ⁻¹' ((Prod.fst ⁻¹' V) ∩ Y)) ≤
      V.indicator (fun _ => n) z := by
    intro z
    by_cases hz : z ∈ V
    · rw [indicator_of_mem hz]
      refine le_trans (measure_mono ?_) (hfib z)
      intro m hm
      exact hm.2
    · rw [indicator_of_notMem hz]
      have : Prod.mk z ⁻¹' ((Prod.fst ⁻¹' V) ∩ Y) = ∅ := by
        ext m
        simp only [mem_preimage, mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hz
      rw [this, measure_empty]
  calc (ν.prod volume) (X ∩ {p | (obs B δ p).1 ∈ V})
      ≤ (ν.prod volume) (E ∩ obs B δ ⁻¹' Z) := measure_mono hsub
    _ ≤ ((ν.prod volume).restrict E) (obs B δ ⁻¹' Z) := by
        rw [Measure.restrict_apply (hobs hZm), inter_comm]
    _ = (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity g) Z := by
        rw [← hmap, Measure.map_apply hobs hZm]
    _ = ∫⁻ o in Z, g o ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count) :=
        withDensity_apply _ hZm
    _ ≤ ∫⁻ _ in Z, cap ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count) :=
        setLIntegral_mono' hZm (fun o ho => ho.2)
    _ = cap * ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count) Z :=
        setLIntegral_const _ _
    _ ≤ cap * ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count)
          ((Prod.fst ⁻¹' V) ∩ Y) := mul_le_mul' le_rfl (measure_mono inter_subset_left)
    _ ≤ cap * (n * volume V) := by
        apply mul_le_mul' le_rfl
        rw [Measure.prod_apply ((measurable_fst hV).inter hY)]
        calc ∫⁻ z, Measure.count (Prod.mk z ⁻¹' ((Prod.fst ⁻¹' V) ∩ Y)) ∂volume
            ≤ ∫⁻ z, V.indicator (fun _ => n) z ∂volume := lintegral_mono hfib'
          _ = n * volume V := lintegral_indicator_const hV n
    _ = cap * n * volume V := (mul_assoc _ _ _).symm

/-- The pair law with the second time in `I` factors. -/
theorem pair_measure_first_eq {ν : Measure (ℕ × (Fin 6 → ℝ))} [SFinite ν]
    (Ω : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hΩ : MeasurableSet Ω) (I : Set ℝ) (hI : MeasurableSet I) :
    (ν.prod ((volume : Measure ℝ).prod volume)) {p | (p.1, p.2.1) ∈ Ω ∧ p.2.2 ∈ I} =
      (ν.prod volume) Ω * volume I := by
  have hm : MeasurableSet {p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) | (p.1, p.2.1) ∈ Ω ∧ p.2.2 ∈ I} :=
    ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)) hΩ).inter
      (measurable_snd.comp measurable_snd hI)
  rw [Measure.prod_apply hm, Measure.prod_apply hΩ, ← lintegral_mul_const _
    (measurable_measure_prodMk_left hΩ)]
  apply lintegral_congr
  intro l
  have hs : Prod.mk l ⁻¹' {p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) | (p.1, p.2.1) ∈ Ω ∧ p.2.2 ∈ I} =
      (Prod.mk l ⁻¹' Ω) ×ˢ I := by
    ext q
    simp
  rw [hs, Measure.prod_prod]

/-- **Capped pair mass in base coordinates.** -/
theorem capped_pair_base_le (ν : Measure (ℕ × (Fin 6 → ℝ))) [SFinite ν]
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) {B δ : ℝ}
    (g : EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞) (hg : Measurable g)
    (hmap : Measure.map (obs B δ) ((ν.prod volume).restrict E) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity g)
    (Y : Set (EuclideanSpace ℝ (Fin 3) × ℤ)) (hY : MeasurableSet Y) (n : ℝ≥0∞)
    (hfib : ∀ z, Measure.count (Prod.mk z ⁻¹' Y) ≤ n) (cap : ℝ≥0∞)
    (X : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hXm : MeasurableSet X) (hXE : X ⊆ E)
    (hX : ∀ p ∈ X, g (obs B δ p) ≤ cap ∧ obs B δ p ∈ Y)
    {q a j : ℝ} (hq : 0 < q) (ha : 0 < a) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) (I : Set ℝ) (hI : MeasurableSet I) :
    (ν.prod ((volume : Measure ℝ).prod volume))
        {p | (p.1, p.2.1) ∈ X ∧ p.2.2 ∈ I ∧
          movingBasePoint q j a c u Q (obs B δ (p.1, p.2.1)).1 ∈ U} ≤
      volume I * (cap * n * (ENNReal.ofReal (a ^ 3 * |Q.det| / q) * volume U)) := by
  have hmbp := measurable_movingBasePoint q j a c u Q
  set Ω := X ∩ {p | (obs B δ p).1 ∈ movingBasePoint q j a c u Q ⁻¹' U} with hΩ
  have hΩm : MeasurableSet Ω :=
    hXm.inter ((measurable_fst.comp (measurable_obs B δ)) (hmbp hU))
  have hsub : {p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) | (p.1, p.2.1) ∈ X ∧ p.2.2 ∈ I ∧
      movingBasePoint q j a c u Q (obs B δ (p.1, p.2.1)).1 ∈ U} ⊆
      {p | (p.1, p.2.1) ∈ Ω ∧ p.2.2 ∈ I} := by
    rintro p ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3⟩, h2⟩
  calc _ ≤ (ν.prod ((volume : Measure ℝ).prod volume)) {p | (p.1, p.2.1) ∈ Ω ∧ p.2.2 ∈ I} :=
        measure_mono hsub
    _ = (ν.prod volume) Ω * volume I := pair_measure_first_eq Ω hΩm I hI
    _ ≤ (cap * n * volume (movingBasePoint q j a c u Q ⁻¹' U)) * volume I := by
        gcongr
        exact capped_obs_mass_le ν E g hg hmap Y hY n hfib cap X hXE hX _ (hmbp hU)
    _ = volume I * (cap * n * (ENNReal.ofReal (a ^ 3 * |Q.det| / q) * volume U)) := by
        rw [volume_movingBasePoint_preimage hq ha j c u Q hQ hU, mul_comm]

/-! ### Hidden-bin sets -/

/-- The observation of an incidence of a regular sublevel set lies in `hidClosed`. -/
theorem obs_mem_hidClosed {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (R : MvPolynomial (Fin 4) ℝ)
    {ε β : ℝ} {p : (ℕ × (Fin 6 → ℝ)) × ℝ} (hval : |eval (x p.1 p.2) R| ≤ ε)
    (hder : β ≤ |eval (x p.1 p.2) (pderiv 3 R)|) :
    obs B δ p ∈ hidClosed R ε β (δ / B) := by
  have hh : 0 < δ / B := div_pos hδ hB
  have hxe : ![(obs B δ p).1 0, (obs B δ p).1 1, (obs B δ p).1 2, (x p.1 p.2) 3] = x p.1 p.2 := by
    funext i
    fin_cases i <;> simp [obs, x]
  refine ⟨(x p.1 p.2) 3, ?_, ?_, ?_⟩
  · simp only [obs]
    set z := B * (x p.1 p.2) 3 / δ with hz
    have hfl1 := Int.floor_le z
    have hfl2 := Int.lt_floor_add_one z
    have hx3 : (x p.1 p.2) 3 = z * (δ / B) := by
      rw [hz]; field_simp
    rw [hx3]
    exact ⟨mul_le_mul_of_nonneg_right hfl1 hh.le, mul_le_mul_of_nonneg_right hfl2.le hh.le⟩
  · rw [hxe]; exact hval
  · rw [hxe]; exact hder

/-- Fibres of `hidClosed` have at most `16 (1 + ε / (β h))` bins. -/
theorem count_hidClosed_le (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    {ε β h : ℝ} (hε : 0 ≤ ε) (hβ : 0 < β) (hh : 0 < h) (z : EuclideanSpace ℝ (Fin 3)) :
    Measure.count (Prod.mk z ⁻¹' hidClosed R ε β h) ≤ ENNReal.ofReal (16 * (1 + ε / (β * h))) := by
  obtain ⟨hfin, hcard⟩ := hidClosed_card_le R hR hε hβ hh z
  have hs : Prod.mk z ⁻¹' hidClosed R ε β h = {n : ℤ | (z, n) ∈ hidClosed R ε β h} := rfl
  rw [hs, Measure.count_apply_finite _ hfin, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  rw [← Set.ncard_eq_toFinset_card _ hfin]
  exact hcard

/-- The hidden bins of width `δ` (in `w = B x₃`) meeting the band `|w - G| ≤ ρ`. -/
def bandBins (G : EuclideanSpace ℝ (Fin 3) → ℝ) (ρ δ : ℝ) : Set (EuclideanSpace ℝ (Fin 3) × ℤ) :=
  {o | (o.2 : ℝ) * δ ≤ G o.1 + ρ ∧ G o.1 - ρ ≤ ((o.2 : ℝ) + 1) * δ}

theorem measurableSet_bandBins {G : EuclideanSpace ℝ (Fin 3) → ℝ} (hG : Measurable G)
    (ρ δ : ℝ) : MeasurableSet (bandBins G ρ δ) := by
  have h2 : Measurable (fun o : EuclideanSpace ℝ (Fin 3) × ℤ => ((o.2 : ℤ) : ℝ)) :=
    measurable_from_top.comp measurable_snd
  have hG' : Measurable (fun o : EuclideanSpace ℝ (Fin 3) × ℤ => G o.1) := hG.comp measurable_fst
  exact (measurableSet_le (h2.mul_const δ) (hG'.add_const ρ)).inter
    (measurableSet_le (hG'.sub_const ρ) ((h2.add_const 1).mul_const δ))

theorem obs_mem_bandBins {B δ ρ : ℝ} (hδ : 0 < δ) (G : EuclideanSpace ℝ (Fin 3) → ℝ)
    {p : (ℕ × (Fin 6 → ℝ)) × ℝ} (hp : |B * (x p.1 p.2) 3 - G (obs B δ p).1| ≤ ρ) :
    obs B δ p ∈ bandBins G ρ δ := by
  have hfl1 := Int.floor_le (B * (x p.1 p.2) 3 / δ)
  have hfl2 := Int.lt_floor_add_one (B * (x p.1 p.2) 3 / δ)
  have e : B * (x p.1 p.2) 3 / δ * δ = B * (x p.1 p.2) 3 := by field_simp
  rw [abs_le] at hp
  refine ⟨?_, ?_⟩
  · show ((⌊B * (x p.1 p.2) 3 / δ⌋ : ℤ) : ℝ) * δ ≤ _
    have := mul_le_mul_of_nonneg_right hfl1 hδ.le
    rw [e] at this
    linarith [hp.2]
  · show _ ≤ (((⌊B * (x p.1 p.2) 3 / δ⌋ : ℤ) : ℝ) + 1) * δ
    have := mul_le_mul_of_nonneg_right hfl2.le hδ.le
    rw [e] at this
    linarith [hp.1]

/-- Fibres of `bandBins` have at most `2 ρ / δ + 2` bins. -/
theorem count_bandBins_le (G : EuclideanSpace ℝ (Fin 3) → ℝ) {ρ δ : ℝ} (hρ : 0 ≤ ρ)
    (hδ : 0 < δ) (z : EuclideanSpace ℝ (Fin 3)) :
    Measure.count (Prod.mk z ⁻¹' bandBins G ρ δ) ≤ ENNReal.ofReal (2 * ρ / δ + 2) := by
  set lo : ℤ := ⌈(G z - ρ) / δ - 1⌉ with hlo
  set hi : ℤ := ⌊(G z + ρ) / δ⌋ with hhi
  have hsub : Prod.mk z ⁻¹' bandBins G ρ δ ⊆ (Finset.Icc lo hi : Set ℤ) := by
    intro n hn
    simp only [mem_preimage, bandBins, mem_ofPred_eq] at hn
    simp only [Finset.coe_Icc, mem_Icc]
    constructor
    · rw [hlo, Int.ceil_le]
      have : (G z - ρ) / δ - 1 ≤ (n : ℝ) := by
        rw [sub_le_iff_le_add, div_le_iff₀ hδ]
        linarith [hn.2]
      exact this
    · rw [hhi, Int.le_floor, le_div_iff₀ hδ]
      exact hn.1
  calc Measure.count (Prod.mk z ⁻¹' bandBins G ρ δ)
      ≤ Measure.count ((Finset.Icc lo hi : Finset ℤ) : Set ℤ) := measure_mono hsub
    _ = ((Finset.Icc lo hi).card : ℝ≥0∞) := by
        rw [Measure.count_apply_finset]
    _ ≤ ENNReal.ofReal (2 * ρ / δ + 2) := by
        rw [Int.card_Icc, ← ENNReal.ofReal_natCast]
        apply ENNReal.ofReal_le_ofReal
        have h1 : (hi : ℝ) ≤ (G z + ρ) / δ := Int.floor_le _
        have h2 : (G z - ρ) / δ - 1 ≤ (lo : ℝ) := Int.le_ceil _
        have hdiv : (G z + ρ) / δ - ((G z - ρ) / δ - 1) = 2 * ρ / δ + 1 := by
          field_simp; ring
        rcases le_or_gt (hi + 1 - lo) 0 with hneg | hpos
        · rw [Int.toNat_of_nonpos hneg]
          simp only [Nat.cast_zero]
          positivity
        · have e : ((hi + 1 - lo).toNat : ℝ) = ((hi + 1 - lo : ℤ) : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hpos.le
          rw [e]
          push_cast
          linarith

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
