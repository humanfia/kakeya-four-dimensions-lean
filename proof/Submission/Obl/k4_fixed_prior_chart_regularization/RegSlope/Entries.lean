-- Adapted from LOT tree g-oai-074, obligation o245, session x0854, commit 3602b8f657fd9f9293587a9dd3e1bdba2451d373.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/RegSlope/Entries.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope.Cluster

/-!
# Slope regularization: entries and cubes

At width `s`, an *entry* is a static group, a code of `(β, γ)` and a time block; a *cube* is a
time block, a static group and a cell of `x̄`. Deleting the incidences of entries of mass
`< φ` costs at most `φ` per occurring entry (`light_entries_mass`). All incidences of one entry
lie within `(K + 2) s` in `x̄` of any of them, so the heavy entries meeting a cube number at most
`(2K + 9) K s³⁺ᵈ / φ` (mixed cap over the cube's box), and so do the slope bins `⌊γ/s⌋`
occurring in a cube (`cube_bins`).
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope

open FirstJet Submission.Obl.k4_scalar_coefficient_clustering

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Deleting light fibres: at most `φ` per occurring fibre. -/
theorem light_fibres_mass {X ι : Type*} [MeasurableSpace X] [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] (μ : Measure X) {A : Set X} {e : X → ι}
    (Ent : Finset ι) (hEnt : ∀ x ∈ A, e x ∈ Ent) (φ : ENNReal) :
    μ (A ∩ {x | μ (A ∩ e ⁻¹' {e x}) < φ}) ≤ Ent.card * φ := by
  classical
  calc μ (A ∩ {x | μ (A ∩ e ⁻¹' {e x}) < φ})
      ≤ μ (⋃ i ∈ Ent.filter (fun i => μ (A ∩ e ⁻¹' {i}) < φ), A ∩ e ⁻¹' {i}) := by
        apply measure_mono
        rintro x ⟨hx, hlt⟩
        exact mem_biUnion (Finset.mem_filter.mpr ⟨hEnt x hx, hlt⟩) ⟨hx, rfl⟩
    _ ≤ ∑ i ∈ Ent.filter (fun i => μ (A ∩ e ⁻¹' {i}) < φ), μ (A ∩ e ⁻¹' {i}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Ent, φ := by
        refine (Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.le).trans ?_
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = Ent.card * φ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The entry of an incidence at width `s`. -/
def entry (s : ℝ) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (p : Ω × ℝ) :
    (Fin 2 → ℤ) × (Fin 3 → ℤ) × ℤ :=
  (fun i => ⌊y p.1 i / s⌋, coefficientCode s (coefVec β γ p.1), ⌊p.2 / s⌋)

/-- The cube of an incidence at width `s`. -/
def cube (s : ℝ) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (p : Ω × ℝ) : Fin 4 → ℤ :=
  ![⌊p.2 / s⌋, ⌊y p.1 0 / s⌋, ⌊y p.1 1 / s⌋, ⌊xbar β γ p.1 p.2 / s⌋]

theorem measurable_entry {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} (hy : Measurable y)
    (hβ : Measurable β) (hγ : Measurable γ) (s : ℝ) : Measurable (entry s y β γ) := by
  unfold entry
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.mpr fun i =>
      Int.measurable_floor.comp ((((measurable_pi_apply i).comp hy).comp measurable_fst).div_const s)
  · exact (measurable_coefficientCode s).comp ((measurable_coefVec hβ hγ).comp measurable_fst)
  · exact Int.measurable_floor.comp (measurable_snd.div_const s)

theorem measurable_cube {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} (hy : Measurable y)
    (hβ : Measurable β) (hγ : Measurable γ) (s : ℝ) : Measurable (cube s y β γ) := by
  unfold cube
  refine measurable_pi_iff.mpr fun i => ?_
  have hx : Measurable fun p : Ω × ℝ => xbar β γ p.1 p.2 := by
    unfold xbar
    exact (hβ.comp measurable_fst).add (measurable_snd.mul (hγ.comp measurable_fst))
  fin_cases i
  · exact Int.measurable_floor.comp (measurable_snd.div_const s)
  · exact Int.measurable_floor.comp ((((measurable_pi_apply 0).comp hy).comp measurable_fst).div_const s)
  · exact Int.measurable_floor.comp ((((measurable_pi_apply 1).comp hy).comp measurable_fst).div_const s)
  · exact Int.measurable_floor.comp (hx.div_const s)

/-- The incidences of heavy entries. -/
def heavyEntries (μ : Measure (Ω × ℝ)) (A : Set (Ω × ℝ)) (s : ℝ) (y : Ω → Fin 2 → ℝ)
    (β γ : Ω → ℝ) (φ : ENNReal) : Set (Ω × ℝ) :=
  {p | p ∈ A ∧ φ ≤ μ (A ∩ entry s y β γ ⁻¹' {entry s y β γ p})}

theorem measurableSet_heavyEntries (μ : Measure (Ω × ℝ)) {A : Set (Ω × ℝ)}
    (hA : MeasurableSet A) {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} (hy : Measurable y)
    (hβ : Measurable β) (hγ : Measurable γ) (s : ℝ) (φ : ENNReal) :
    MeasurableSet (heavyEntries μ A s y β γ φ) := by
  have he := measurable_entry hy hβ hγ s
  have : Measurable fun p => μ (A ∩ entry s y β γ ⁻¹' {entry s y β γ p}) :=
    (measurable_of_countable (fun e => μ (A ∩ entry s y β γ ⁻¹' {e}))).comp he
  exact hA.inter (measurableSet_le measurable_const this)

theorem coefficientCode_one {β γ : Ω → ℝ} (s : ℝ) (l : Ω) :
    coefficientCode s (coefVec β γ l) 1 = ⌊γ l / s⌋ := by
  simp [coefficientCode]

theorem coefficientCode_zero {β γ : Ω → ℝ} (s : ℝ) (l : Ω) :
    coefficientCode s (coefVec β γ l) 0 = ⌊β l / s⌋ := by
  simp [coefficientCode]

/-- The box of a cube: its time block, its static group and `x̄` within `(K + 3) s` of its cell. -/
def cubeBox (s K : ℝ) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (z : Fin 4 → ℤ) : Set (Ω × ℝ) :=
  {p | ⌊p.2 / s⌋ = z 0 ∧ ⌊y p.1 0 / s⌋ = z 1 ∧ ⌊y p.1 1 / s⌋ = z 2 ∧
    |xbar β γ p.1 p.2 - z 3 * s| ≤ (K + 3) * s}

theorem box_mass {ν : Measure Ω} [SFinite ν] {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ}
    {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ) {s : ℝ} (hs0 : 0 < s) (hs : ζ ≤ s)
    (hs1 : s ≤ 1) (z : Fin 4 → ℤ) :
    (ν.prod volume) (E ∩ cubeBox s K y β γ z) ≤
      ENNReal.ofReal ((2 * K + 9) * K * (s * (s ^ 2 * s ^ d))) := by
  classical
  have hK : 0 ≤ K := (abs_nonneg _).trans (hU.bound_F 0 0)
  set R : ℤ := ⌈K⌉ + 3 with hR
  have hR0 : 0 ≤ R := by
    have : (0 : ℝ) ≤ ⌈K⌉ := hK.trans (Int.le_ceil _)
    have : (0 : ℤ) ≤ ⌈K⌉ := by exact_mod_cast this
    omega
  have hbm : MeasurableSet (E ∩ cubeBox s K y β γ z) := by
    have hx : Measurable fun p : Ω × ℝ => xbar β γ p.1 p.2 := by
      unfold xbar
      exact (hU.measurable_β.comp measurable_fst).add
        (measurable_snd.mul (hU.measurable_γ.comp measurable_fst))
    refine hU.measurableSet_E.inter ?_
    unfold cubeBox
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
    · exact (Int.measurable_floor.comp (measurable_snd.div_const s)) (measurableSet_singleton _)
    · exact (Int.measurable_floor.comp
        ((((measurable_pi_apply 0).comp hU.measurable_y).comp measurable_fst).div_const s))
        (measurableSet_singleton _)
    · exact (Int.measurable_floor.comp
        ((((measurable_pi_apply 1).comp hU.measurable_y).comp measurable_fst).div_const s))
        (measurableSet_singleton _)
    · exact measurableSet_le ((hx.sub_const _).abs) measurable_const
  have hslice : ∀ t : ℝ, ν ((fun l => (l, t)) ⁻¹' (E ∩ cubeBox s K y β γ z)) ≤
      {t' : ℝ | ⌊t' / s⌋ = z 0}.indicator
        (fun _ => ENNReal.ofReal ((2 * K + 9) * (K * s ^ 2 * s ^ d))) t := by
    intro t
    by_cases ht : ⌊t / s⌋ = z 0
    · rw [indicator_of_mem (show t ∈ {t' : ℝ | ⌊t' / s⌋ = z 0} from ht)]
      have hsub : (fun l => (l, t)) ⁻¹' (E ∩ cubeBox s K y β γ z) ⊆
          ⋃ j ∈ Finset.Icc (z 3 - R) (z 3 + R), {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / s⌋ = j ∧
            ⌊y l 0 / s⌋ = ![z 1, z 2] 0 ∧ ⌊y l 1 / s⌋ = ![z 1, z 2] 1} := by
        rintro l ⟨hl, -, h1, h2, hx⟩
        have hxs : |xbar β γ l t / s - z 3| ≤ K + 3 := by
          rw [show xbar β γ l t / s - z 3 = (xbar β γ l t - z 3 * s) / s by field_simp,
            abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
          exact hx
        rw [abs_le] at hxs
        have hc := Int.le_ceil K
        have hf1 := Int.floor_le (xbar β γ l t / s)
        have hf2 := Int.lt_floor_add_one (xbar β γ l t / s)
        have hmem : ⌊xbar β γ l t / s⌋ ∈ Finset.Icc (z 3 - R) (z 3 + R) := by
          rw [Finset.mem_Icc]
          constructor
          · have : ((z 3 - R : ℤ) : ℝ) < ⌊xbar β γ l t / s⌋ + 1 := by
              rw [hR]; push_cast; linarith
            have : z 3 - R < ⌊xbar β γ l t / s⌋ + 1 := by exact_mod_cast this
            omega
          · have : ((⌊xbar β γ l t / s⌋ : ℤ) : ℝ) ≤ ((z 3 + R : ℤ) : ℝ) := by
              rw [hR]; push_cast; linarith
            exact_mod_cast this
        exact mem_biUnion hmem ⟨hl, rfl, h1, h2⟩
      calc ν ((fun l => (l, t)) ⁻¹' (E ∩ cubeBox s K y β γ z))
          ≤ ∑ j ∈ Finset.Icc (z 3 - R) (z 3 + R), ν {l | (l, t) ∈ E ∧
            ⌊xbar β γ l t / s⌋ = j ∧ ⌊y l 0 / s⌋ = ![z 1, z 2] 0 ∧
              ⌊y l 1 / s⌋ = ![z 1, z 2] 1} :=
            (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
        _ ≤ ∑ _j ∈ Finset.Icc (z 3 - R) (z 3 + R), ENNReal.ofReal (K * s ^ 2 * s ^ d) :=
            Finset.sum_le_sum fun j _ => hU.mixedCap t s s hs hs1 hs hs1 ![z 1, z 2] j
        _ ≤ ENNReal.ofReal ((2 * K + 9) * (K * s ^ 2 * s ^ d)) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            apply ENNReal.ofReal_le_ofReal
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [Int.card_Icc]
            have e : z 3 + R + 1 - (z 3 - R) = 2 * R + 1 := by ring
            rw [e]
            have h : (((2 * R + 1).toNat : ℤ) : ℝ) = ((2 * R + 1 : ℤ) : ℝ) := by
              rw [Int.toNat_of_nonneg (by omega)]
            push_cast at h ⊢
            rw [h, hR]; push_cast
            have := Int.ceil_lt_add_one K
            linarith
    · rw [indicator_of_notMem (show t ∉ {t' : ℝ | ⌊t' / s⌋ = z 0} from ht)]
      have : (fun l => (l, t)) ⁻¹' (E ∩ cubeBox s K y β γ z) = ∅ := by
        ext l
        simp only [mem_preimage, mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        intro _ hb; exact ht hb.1
      rw [this, measure_empty]
  rw [Measure.prod_apply_symm hbm]
  calc ∫⁻ t, ν ((fun l => (l, t)) ⁻¹' (E ∩ cubeBox s K y β γ z))
      ≤ ∫⁻ t, {t' : ℝ | ⌊t' / s⌋ = z 0}.indicator
        (fun _ => ENNReal.ofReal ((2 * K + 9) * (K * s ^ 2 * s ^ d))) t := lintegral_mono hslice
    _ = ENNReal.ofReal ((2 * K + 9) * (K * s ^ 2 * s ^ d)) *
          volume {t' : ℝ | ⌊t' / s⌋ = z 0} := by
        rw [lintegral_indicator_const (measurableSet_block s (z 0))]
    _ ≤ ENNReal.ofReal ((2 * K + 9) * (K * s ^ 2 * s ^ d)) * ENNReal.ofReal s := by
        gcongr; exact volume_block_le hs0 (z 0)
    _ = ENNReal.ofReal ((2 * K + 9) * K * (s * (s ^ 2 * s ^ d))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

/-- **Few slope bins per cube among heavy entries.** -/
theorem cube_bins {ν : Measure Ω} [SFinite ν] {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ}
    {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ) {s : ℝ} (hs0 : 0 < s) (hs : ζ ≤ s)
    (hs1 : s ≤ 1) {A : Set (Ω × ℝ)} (hA : MeasurableSet A) (hAE : A ⊆ E) {φ : ℝ}
    (hφ : 0 < φ) (z : Fin 4 → ℤ) :
    ∃ T : Finset ℤ, (T.card : ℝ) ≤ (2 * K + 9) * K * (s * (s ^ 2 * s ^ d)) / φ ∧
      ∀ p ∈ heavyEntries (ν.prod volume) A s y β γ (ENNReal.ofReal φ),
        cube s y β γ p = z → ⌊γ p.1 / s⌋ ∈ T := by
  classical
  have hK : 0 ≤ K := (abs_nonneg _).trans (hU.bound_F 0 0)
  set H := heavyEntries (ν.prod volume) A s y β γ (ENNReal.ofReal φ) with hH
  set R : ℤ := ⌈2 * K / s⌉ + 1 with hR
  set T : Finset ℤ := (Finset.Icc (-R) R).filter
    (fun g => ∃ p ∈ H, cube s y β γ p = z ∧ ⌊γ p.1 / s⌋ = g) with hT
  refine ⟨T, ?_, ?_⟩
  · rcases T.eq_empty_or_nonempty with hTe | ⟨g₀, hg₀⟩
    · rw [hTe, Finset.card_empty, Nat.cast_zero]; positivity
    have hw : ∀ g ∈ T, ∃ p ∈ H, cube s y β γ p = z ∧ ⌊γ p.1 / s⌋ = g :=
      fun g hg => (Finset.mem_filter.mp hg).2
    haveI : Nonempty (Ω × ℝ) := ⟨(hw g₀ hg₀).choose⟩
    choose! w hwH hwz hwg using hw
    have he := measurable_entry hU.measurable_y hU.measurable_β hU.measurable_γ s
    set S : ℤ → Set (Ω × ℝ) := fun g => A ∩ entry s y β γ ⁻¹' {entry s y β γ (w g)} with hS
    have hSm : ∀ g, MeasurableSet (S g) := fun g => hA.inter (he (measurableSet_singleton _))
    have hSφ : ∀ g ∈ T, ENNReal.ofReal φ ≤ (ν.prod volume) (S g) := fun g hg => (hwH g hg).2
    have hdisj : (T : Set ℤ).PairwiseDisjoint S := by
      intro g hg g' hg' hne
      refine Set.disjoint_left.mpr fun p hp hp' => hne ?_
      have h1 : entry s y β γ (w g) = entry s y β γ (w g') := hp.2.symm.trans hp'.2
      have h2 := congrArg (fun e => e.2.1 1) h1
      simp only [entry, coefficientCode_one] at h2
      rw [← hwg g hg, ← hwg g' hg']
      exact h2
    have hsub : ∀ g ∈ T, S g ⊆ E ∩ cubeBox s K y β γ z := by
      intro g hg p hp
      obtain ⟨hpA, hpe⟩ := hp
      have hpe' : entry s y β γ p = entry s y β γ (w g) := hpe
      have hwz' := hwz g hg
      have ht := congrArg (fun e => e.2.2) hpe'
      have hy := congrArg (fun e => e.1) hpe'
      have hc := congrArg (fun e => e.2.1) hpe'
      simp only [entry] at ht hy hc
      have hc0 := congrFun hc 0
      have hc1 := congrFun hc 1
      rw [coefficientCode_zero, coefficientCode_zero] at hc0
      rw [coefficientCode_one, coefficientCode_one] at hc1
      have hz0 : ⌊(w g).2 / s⌋ = z 0 := by rw [← hwz']; simp [cube]
      have hz1 : ⌊y (w g).1 0 / s⌋ = z 1 := by rw [← hwz']; simp [cube]
      have hz2 : ⌊y (w g).1 1 / s⌋ = z 2 := by rw [← hwz']; simp [cube]
      have hz3 : ⌊xbar β γ (w g).1 (w g).2 / s⌋ = z 3 := by rw [← hwz']; simp [cube]
      refine ⟨hAE hpA, ht.trans hz0, (congrFun hy 0).trans hz1, (congrFun hy 1).trans hz2, ?_⟩
      -- the position of `p` is within `(K + 2) s` of the witness
      have hp01 := (hU.subset_E (hAE hpA)).2
      have hdt := abs_sub_lt_of_floor_eq hs0 ht
      have hdβ := abs_sub_lt_of_floor_eq hs0 hc0
      have hdγ := abs_sub_lt_of_floor_eq hs0 hc1
      have hγw := hU.bound_γ (w g).1
      have hx1 : (z 3 : ℝ) * s ≤ xbar β γ (w g).1 (w g).2 := by
        have := Int.floor_le (xbar β γ (w g).1 (w g).2 / s); rw [hz3] at this
        rwa [le_div_iff₀ hs0] at this
      have hx2 : xbar β γ (w g).1 (w g).2 < ((z 3 : ℝ) + 1) * s := by
        have := Int.lt_floor_add_one (xbar β γ (w g).1 (w g).2 / s); rw [hz3] at this
        rwa [div_lt_iff₀ hs0] at this
      have e : xbar β γ p.1 p.2 - xbar β γ (w g).1 (w g).2 =
          (β p.1 - β (w g).1) + p.2 * (γ p.1 - γ (w g).1) + (p.2 - (w g).2) * γ (w g).1 := by
        simp only [xbar]; ring
      have b1 : |p.2 * (γ p.1 - γ (w g).1)| ≤ s := by
        rw [abs_mul, abs_of_nonneg hp01.1]
        calc p.2 * |γ p.1 - γ (w g).1| ≤ 1 * s :=
              mul_le_mul hp01.2 hdγ.le (abs_nonneg _) zero_le_one
          _ = s := one_mul s
      have b2 : |(p.2 - (w g).2) * γ (w g).1| ≤ s * K := by
        rw [abs_mul]; exact mul_le_mul hdt.le hγw (abs_nonneg _) hs0.le
      have hd : |xbar β γ p.1 p.2 - xbar β γ (w g).1 (w g).2| ≤ s + s + s * K := by
        rw [e]
        calc |(β p.1 - β (w g).1) + p.2 * (γ p.1 - γ (w g).1) + (p.2 - (w g).2) * γ (w g).1|
            ≤ |β p.1 - β (w g).1| + |p.2 * (γ p.1 - γ (w g).1)| +
              |(p.2 - (w g).2) * γ (w g).1| := abs_add_three _ _ _
          _ ≤ s + s + s * K := by linarith [hdβ.le]
      rw [abs_le] at hd ⊢
      constructor <;> nlinarith
    have hsum : (T.card : ENNReal) * ENNReal.ofReal φ ≤
        ENNReal.ofReal ((2 * K + 9) * K * (s * (s ^ 2 * s ^ d))) := by
      calc (T.card : ENNReal) * ENNReal.ofReal φ = ∑ _g ∈ T, ENNReal.ofReal φ := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ g ∈ T, (ν.prod volume) (S g) := Finset.sum_le_sum hSφ
        _ = (ν.prod volume) (⋃ g ∈ T, S g) := (measure_biUnion_finset hdisj fun g _ => hSm g).symm
        _ ≤ (ν.prod volume) (E ∩ cubeBox s K y β γ z) :=
            measure_mono (iUnion₂_subset fun g hg => hsub g hg)
        _ ≤ _ := box_mass hU hs0 hs hs1 z
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hsum
    have h := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsum
    rw [le_div_iff₀ hφ]; exact h
  · intro p hp hpz
    refine Finset.mem_filter.mpr ⟨?_, p, hp, hpz, rfl⟩
    have hp01 := (hU.subset_E (hAE hp.1)).2
    have : |γ p.1| ≤ 2 * K := (hU.bound_γ p.1).trans (by linarith)
    exact floor_mem_range hs0 this

end Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope

end
