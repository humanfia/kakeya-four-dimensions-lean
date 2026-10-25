import Mathlib
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.Packets
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.QuadBounds

/-!
# Mass bounds through exact observation densities

The incidence mass of a set of trajectory--time pairs whose observations lie in a box and
whose observed density is at most `θ` is at most `θ` times the reference measure of the box.
We record the observation maps of the frozen statement, the reference measures of the boxes
used for chart packets, and the aggregate discard of packets that are mostly exceptional.
-/

namespace Submission.Obl.k4_scalar_terminal_chart_packet_extraction

open MeasureTheory Set
open scoped ENNReal

/-! ### Observation maps -/

/-- Exact base point and hidden bin of width `a` (the frozen depth observation). -/
noncomputable def obsL (a : ℝ) (p : Coeff × ℝ) : (Fin 2 → ℝ) × ℤ :=
  (![p.2, spatial p.1 p.2], ⌊hidden p.1 p.2 / a⌋)

/-- Exact base point, hidden bin of width `a` and velocity bin of width `b`. -/
noncomputable def obsG (a b : ℝ) (p : Coeff × ℝ) : ((Fin 2 → ℝ) × ℤ) × ℤ :=
  (obsL a p, ⌊p.1.2 1 / b⌋)

lemma measurable_spatial : Measurable (fun p : Coeff × ℝ => spatial p.1 p.2) := by
  unfold spatial; fun_prop

lemma measurable_hidden : Measurable (fun p : Coeff × ℝ => hidden p.1 p.2) := by
  unfold hidden; fun_prop

lemma measurable_obsL (a : ℝ) : Measurable (obsL a) := by
  unfold obsL
  refine Measurable.prodMk ?_ ((measurable_hidden.div_const a).floor)
  refine measurable_pi_iff.mpr (fun i => ?_)
  fin_cases i
  · simpa using measurable_snd
  · simpa using measurable_spatial

lemma measurable_obsG (a b : ℝ) : Measurable (obsG a b) := by
  unfold obsG
  refine (measurable_obsL a).prodMk ?_
  exact (show Measurable (fun p : Coeff × ℝ => p.1.2 1 / b) by fun_prop).floor

/-! ### Counting and volumes -/

lemma count_int_near_le (z R : ℝ) (hR : 0 ≤ R) :
    Measure.count {k : ℤ | |(k : ℝ) - z| ≤ R} ≤ ENNReal.ofReal (2 * R + 1) := by
  have hsub : {k : ℤ | |(k : ℝ) - z| ≤ R} ⊆ (Finset.Icc ⌈z - R⌉ ⌊z + R⌋ : Set ℤ) := by
    intro k hk
    have := abs_le.mp (show |(k : ℝ) - z| ≤ R from hk)
    simp only [Finset.coe_Icc, Set.mem_Icc]
    constructor
    · exact Int.ceil_le.mpr (by linarith)
    · exact Int.le_floor.mpr (by linarith)
  calc Measure.count {k : ℤ | |(k : ℝ) - z| ≤ R}
      ≤ Measure.count (Finset.Icc ⌈z - R⌉ ⌊z + R⌋ : Set ℤ) := measure_mono hsub
    _ = (Finset.Icc ⌈z - R⌉ ⌊z + R⌋).card := Measure.count_apply_finset _
    _ ≤ ENNReal.ofReal (2 * R + 1) := by
        rw [Int.card_Icc, ← ENNReal.ofReal_natCast]
        apply ENNReal.ofReal_le_ofReal
        set m : ℤ := ⌊z + R⌋ + 1 - ⌈z - R⌉ with hm
        have hmR : (m : ℝ) ≤ 2 * R + 1 := by
          rw [hm]; push_cast
          have h1 := Int.floor_le (z + R)
          have h2 := Int.le_ceil (z - R)
          linarith
        rcases le_or_gt m 0 with h | h
        · rw [Int.toNat_of_nonpos h]; simp; linarith
        · have : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
            have := Int.toNat_of_nonneg h.le
            exact_mod_cast this
          rw [this]; exact hmR

lemma volume_fin2_eq {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    volume {v : Fin 2 → ℝ | (v 0, v 1) ∈ S} = volume S :=
  (volume_preserving_finTwoArrow ℝ).measure_preimage hS.nullMeasurableSet

/-- The base parallelogram of a version-1 chart. -/
def chartPar (t₀ q c₀ c₁ w : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc t₀ (t₀ + q) ∧ |p.2 - (c₀ + c₁ * p.1)| ≤ w}

lemma measurableSet_chartPar (t₀ q c₀ c₁ w : ℝ) : MeasurableSet (chartPar t₀ q c₀ c₁ w) := by
  show MeasurableSet ((Prod.fst ⁻¹' Icc t₀ (t₀ + q)) ∩ {p : ℝ × ℝ | |p.2 - (c₀ + c₁ * p.1)| ≤ w})
  exact (measurableSet_Icc.preimage measurable_fst).inter (measurableSet_le (by fun_prop)
    (by fun_prop))

lemma volume_chartPar_le (t₀ q c₀ c₁ w : ℝ) (hw : 0 ≤ w) :
    volume (chartPar t₀ q c₀ c₁ w) ≤ ENNReal.ofReal (q * (2 * w)) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_chartPar t₀ q c₀ c₁ w)]
  calc ∫⁻ s, volume (Prod.mk s ⁻¹' chartPar t₀ q c₀ c₁ w)
      ≤ ∫⁻ s, (Icc t₀ (t₀ + q)).indicator (fun _ => ENNReal.ofReal (2 * w)) s := by
        apply lintegral_mono
        intro s
        dsimp only
        by_cases hs : s ∈ Icc t₀ (t₀ + q)
        · rw [Set.indicator_of_mem hs]
          calc volume (Prod.mk s ⁻¹' chartPar t₀ q c₀ c₁ w)
              ≤ volume (Icc (c₀ + c₁ * s - w) (c₀ + c₁ * s + w)) := by
                apply measure_mono
                intro y hy
                have := abs_le.mp hy.2
                exact ⟨by linarith, by linarith⟩
            _ = ENNReal.ofReal (2 * w) := by rw [Real.volume_Icc]; ring_nf
        · have : Prod.mk s ⁻¹' chartPar t₀ q c₀ c₁ w = ∅ := by
            ext y
            simp only [Set.mem_preimage, chartPar, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
              iff_false]
            exact fun h => hs h.1
          rw [this, measure_empty]
          exact bot_le
    _ = ENNReal.ofReal (2 * w) * ENNReal.ofReal q := by
        rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
        ring_nf
    _ = ENNReal.ofReal (q * (2 * w)) := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- Reference measure of the hidden-bin box over a base set `X`. -/
lemma prod_count_box_le {X : Set (Fin 2 → ℝ)} (hX : MeasurableSet X)
    {z : (Fin 2 → ℝ) → ℝ} (hz : Measurable z) {R : ℝ} (hR : 0 ≤ R) :
    (volume.prod Measure.count) {p : (Fin 2 → ℝ) × ℤ | p.1 ∈ X ∧ |(p.2 : ℝ) - z p.1| ≤ R} ≤
      ENNReal.ofReal (2 * R + 1) * volume X := by
  have hm : MeasurableSet {p : (Fin 2 → ℝ) × ℤ | p.1 ∈ X ∧ |(p.2 : ℝ) - z p.1| ≤ R} := by
    show MeasurableSet ((Prod.fst ⁻¹' X) ∩ {p : (Fin 2 → ℝ) × ℤ | |(p.2 : ℝ) - z p.1| ≤ R})
    refine (hX.preimage measurable_fst).inter (measurableSet_le ?_ measurable_const)
    have h2 : Measurable (fun p : (Fin 2 → ℝ) × ℤ => ((p.2 : ℤ) : ℝ)) :=
      (measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp measurable_snd
    exact (h2.sub (hz.comp measurable_fst)).abs
  rw [Measure.prod_apply hm]
  calc ∫⁻ v, Measure.count (Prod.mk v ⁻¹'
        {p : (Fin 2 → ℝ) × ℤ | p.1 ∈ X ∧ |(p.2 : ℝ) - z p.1| ≤ R})
      ≤ ∫⁻ v, X.indicator (fun _ => ENNReal.ofReal (2 * R + 1)) v := by
        apply lintegral_mono
        intro v
        dsimp only
        by_cases hv : v ∈ X
        · rw [Set.indicator_of_mem hv]
          calc Measure.count (Prod.mk v ⁻¹'
                {p : (Fin 2 → ℝ) × ℤ | p.1 ∈ X ∧ |(p.2 : ℝ) - z p.1| ≤ R})
              ≤ Measure.count {k : ℤ | |(k : ℝ) - z v| ≤ R} :=
                measure_mono (fun k hk => hk.2)
            _ ≤ ENNReal.ofReal (2 * R + 1) := count_int_near_le _ _ hR
        · have : Prod.mk v ⁻¹' {p : (Fin 2 → ℝ) × ℤ | p.1 ∈ X ∧ |(p.2 : ℝ) - z p.1| ≤ R} = ∅ := by
            ext k
            simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            exact fun h => hv h.1
          rw [this, measure_empty]
          exact bot_le
    _ = ENNReal.ofReal (2 * R + 1) * volume X := lintegral_indicator_const hX _

/-! ### Mass below a density threshold -/

/-- Incidences observed in a box `B` at density at most `θ` have mass at most `θ` times the
reference measure of `B`. -/
lemma mass_le_of_density_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ρ : Measure β} {φ : α → β} (hφ : Measurable φ) {G : β → ℝ≥0∞}
    (hG : Measurable G) (hmap : Measure.map φ μ = ρ.withDensity G) {B : Set β}
    (hB : MeasurableSet B) (θ : ℝ≥0∞) {P : Set α} (hP : P ⊆ φ ⁻¹' B) :
    μ (P \ {p | θ < G (φ p)}) ≤ θ * ρ B := by
  have hsub : P \ {p | θ < G (φ p)} ⊆ φ ⁻¹' (B ∩ {b | G b ≤ θ}) := by
    intro p hp
    exact ⟨hP hp.1, show G (φ p) ≤ θ from not_lt.mp hp.2⟩
  have hm : MeasurableSet (B ∩ {b | G b ≤ θ}) := hB.inter (measurableSet_le hG measurable_const)
  calc μ (P \ {p | θ < G (φ p)}) ≤ μ (φ ⁻¹' (B ∩ {b | G b ≤ θ})) := measure_mono hsub
    _ = (Measure.map φ μ) (B ∩ {b | G b ≤ θ}) := (Measure.map_apply hφ hm).symm
    _ = ∫⁻ b in B ∩ {b | G b ≤ θ}, G b ∂ρ := by rw [hmap, withDensity_apply _ hm]
    _ ≤ ∫⁻ _ in B ∩ {b | G b ≤ θ}, θ ∂ρ := setLIntegral_mono measurable_const (fun b hb => hb.2)
    _ = θ * ρ (B ∩ {b | G b ≤ θ}) := setLIntegral_const _ _
    _ ≤ θ * ρ B := by gcongr; exact inter_subset_left

/-- If the part of `P` outside `X` is at most half of `P`, then `P` is at most twice its part
inside `X`. -/
lemma le_two_mul_inter_of_diff_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {P X : Set α} {c : ℝ≥0∞} (hc : c ≠ ⊤) (hdiff : μ (P \ X) ≤ c) (h2c : 2 * c ≤ μ P) :
    μ P ≤ 2 * μ (P ∩ X) := by
  have hsplit : μ P ≤ μ (P ∩ X) + μ (P \ X) := by
    calc μ P ≤ μ ((P ∩ X) ∪ (P \ X)) := by rw [Set.inter_union_sdiff]
      _ ≤ μ (P ∩ X) + μ (P \ X) := measure_union_le _ _
  have h1 : μ P ≤ μ (P ∩ X) + c := hsplit.trans (add_le_add le_rfl hdiff)
  have h2 : c ≤ μ (P ∩ X) := by
    have : 2 * c ≤ μ (P ∩ X) + c := h2c.trans h1
    rw [two_mul] at this
    exact (ENNReal.add_le_add_iff_right hc).mp this
  calc μ P ≤ μ (P ∩ X) + c := h1
    _ ≤ μ (P ∩ X) + μ (P ∩ X) := add_le_add le_rfl h2
    _ = 2 * μ (P ∩ X) := (two_mul _).symm

/-! ### Aggregate discard -/

/-- Packets that are mostly exceptional carry, in total, at most twice the weighted
exceptional mass, provided packets of the same world are almost disjoint. -/
lemma weighted_bad_le {α : Type*} [MeasurableSpace α] {W n : ℕ} (ω : Fin W → ℝ≥0∞)
    (μ : Fin W → Measure α) (γ : Fin n → Fin W) (P : Fin n → Set α) (X : Fin W → Set α)
    (bad : Finset (Fin n)) (hPm : ∀ i, MeasurableSet (P i)) (hXm : ∀ g, MeasurableSet (X g))
    (hdisj : ∀ i ∈ bad, ∀ i' ∈ bad, i ≠ i' → γ i = γ i' → μ (γ i) (P i ∩ P i') = 0)
    (hbad : ∀ i ∈ bad, μ (γ i) (P i) ≤ 2 * μ (γ i) (P i ∩ X (γ i))) :
    ∑ i ∈ bad, ω (γ i) * μ (γ i) (P i) ≤ 2 * ∑ g, ω g * μ g (X g) := by
  have hfib : ∀ g : Fin W, ∑ i ∈ bad with γ i = g, μ g (P i ∩ X g) ≤ μ g (X g) := by
    intro g
    rw [← measure_biUnion_finset₀]
    · exact measure_mono (Set.iUnion₂_subset (fun i _ => Set.inter_subset_right))
    · intro i hi i' hi' hne
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hi'
      have h0 := hdisj i hi.1 i' hi'.1 hne (hi.2.trans hi'.2.symm)
      rw [hi.2] at h0
      refine measure_mono_null ?_ h0
      intro p hp
      exact ⟨hp.1.1, hp.2.1⟩
    · intro i _
      exact ((hPm i).inter (hXm g)).nullMeasurableSet
  calc ∑ i ∈ bad, ω (γ i) * μ (γ i) (P i)
      ≤ ∑ i ∈ bad, ω (γ i) * (2 * μ (γ i) (P i ∩ X (γ i))) :=
        Finset.sum_le_sum (fun i hi => by gcongr; exact hbad i hi)
    _ = ∑ g, ∑ i ∈ bad with γ i = g, ω (γ i) * (2 * μ (γ i) (P i ∩ X (γ i))) :=
        (Finset.sum_fiberwise bad γ _).symm
    _ = ∑ g, 2 * (ω g * ∑ i ∈ bad with γ i = g, μ g (P i ∩ X g)) := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        simp only [Finset.mem_filter] at hi
        rw [hi.2]
        ring
    _ ≤ ∑ g, 2 * (ω g * μ g (X g)) := by
        gcongr with g
        exact hfib g
    _ = 2 * ∑ g, ω g * μ g (X g) := by rw [Finset.mul_sum]

/-! ### Chart packets -/

/-- Along a chart block the hidden bin of an incidence is within `Λ + 1` bins of the
predictor, when the hidden coordinate is within `Λ a` of it. -/
lemma floor_near_of_fit {x F a Λ : ℝ} (ha : 0 < a) (h : |x - F| ≤ Λ * a) :
    |((⌊x / a⌋ : ℤ) : ℝ) - F / a| ≤ Λ + 1 := by
  have h1 := Int.floor_le (x / a)
  have h2 := Int.lt_floor_add_one (x / a)
  have h3 : |x / a - F / a| ≤ Λ := by
    rw [← sub_div, abs_div, abs_of_pos ha, div_le_iff₀ ha]; exact h
  have h4 : |((⌊x / a⌋ : ℤ) : ℝ) - x / a| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc |((⌊x / a⌋ : ℤ) : ℝ) - F / a| = |(((⌊x / a⌋ : ℤ) : ℝ) - x / a) + (x / a - F / a)| := by
        ring_nf
    _ ≤ |((⌊x / a⌋ : ℤ) : ℝ) - x / a| + |x / a - F / a| := abs_add_le _ _
    _ ≤ Λ + 1 := by linarith

/-- The velocity of a trajectory confined to a moving interval of half-width `w` around an
affine centre throughout a block of length `q` is within `2 w / q` of the centre velocity. -/
lemma velocity_near_of_conf {l : Coeff} {s q c₀ c₁ w : ℝ} (hq : 0 < q)
    (hconf : ∀ t ∈ Icc s (s + q), |spatial l t - (c₀ + c₁ * t)| ≤ w) :
    |l.2 1 - c₁| * q ≤ 2 * w := by
  have h1 := hconf s ⟨le_rfl, by linarith⟩
  have h2 := hconf (s + q) ⟨by linarith, le_rfl⟩
  have : (l.2 1 - c₁) * q = (spatial l (s + q) - (c₀ + c₁ * (s + q))) -
      (spatial l s - (c₀ + c₁ * s)) := by unfold spatial; ring
  rw [← abs_of_pos hq, ← abs_mul, this]
  calc _ ≤ |spatial l (s + q) - (c₀ + c₁ * (s + q))| + |spatial l s - (c₀ + c₁ * s)| :=
        abs_sub _ _
    _ ≤ 2 * w := by linarith

/-- A narrow chart packet (velocity window shorter than half a velocity bin) has its mass at
angular density at most `θ` bounded by `θ` times its reference box. -/
lemma narrow_packet_diff_le {μ : Measure (Coeff × ℝ)} {G : ((Fin 2 → ℝ) × ℤ) × ℤ → ℝ≥0∞}
    (hG : Measurable G) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmap : Measure.map (obsG a b) μ =
      ((volume.prod Measure.count).prod Measure.count).withDensity G)
    {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) {A : Set Coeff} {s q c₀ c₁ w Λ : ℝ} (hq : 0 < q)
    (hw : 0 ≤ w) (hΛ : 0 ≤ Λ)
    (hconf : ∀ l ∈ A, ∀ t ∈ Icc s (s + q),
      |spatial l t - (c₀ + c₁ * t)| ≤ w ∧ |hidden l t - f t (spatial l t)| ≤ Λ * a)
    (hnarrow : 4 * w ≤ b * q) (θ : ℝ≥0∞) :
    μ ((A ×ˢ Icc s (s + q)) \ {p | θ < G (obsG a b p)}) ≤
      θ * ENNReal.ofReal (4 * (2 * Λ + 3) * (q * (2 * w))) := by
  set BaseF : Set (Fin 2 → ℝ) := {v | (v 0, v 1) ∈ chartPar s q c₀ c₁ w} with hBaseF
  have hBaseFm : MeasurableSet BaseF :=
    (measurableSet_chartPar s q c₀ c₁ w).preimage (by fun_prop)
  set S : Set ((Fin 2 → ℝ) × ℤ) :=
    {x | x.1 ∈ BaseF ∧ |(x.2 : ℝ) - f (x.1 0) (x.1 1) / a| ≤ Λ + 1} with hS
  set V : Set ℤ := {k | |(k : ℝ) - c₁ / b| ≤ 3 / 2} with hV
  have hfm : Measurable (fun v : Fin 2 → ℝ => f (v 0) (v 1) / a) := by
    have h' : Continuous (fun v : Fin 2 → ℝ => f (v 0) (v 1)) :=
      hf.continuous.comp (f := fun v : Fin 2 → ℝ => (v 0, v 1)) (by fun_prop)
    exact h'.measurable.div_const a
  have hSm : MeasurableSet S := by
    show MeasurableSet ((Prod.fst ⁻¹' BaseF) ∩
      {x : (Fin 2 → ℝ) × ℤ | |(x.2 : ℝ) - f (x.1 0) (x.1 1) / a| ≤ Λ + 1})
    refine (hBaseFm.preimage measurable_fst).inter (measurableSet_le ?_ measurable_const)
    have h2 : Measurable (fun p : (Fin 2 → ℝ) × ℤ => ((p.2 : ℤ) : ℝ)) :=
      (measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp measurable_snd
    exact (h2.sub (hfm.comp measurable_fst)).abs
  have hVm : MeasurableSet V := (Set.to_countable V).measurableSet
  have hsub : A ×ˢ Icc s (s + q) ⊆ obsG a b ⁻¹' (S ×ˢ V) := by
    rintro ⟨l, t⟩ ⟨hl, ht⟩
    obtain ⟨hc, hx⟩ := hconf l hl t ht
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show (t, spatial l t) ∈ chartPar s q c₀ c₁ w
      exact ⟨ht, hc⟩
    · show |((⌊hidden l t / a⌋ : ℤ) : ℝ) - f t (spatial l t) / a| ≤ Λ + 1
      exact floor_near_of_fit ha hx
    · show |((⌊l.2 1 / b⌋ : ℤ) : ℝ) - c₁ / b| ≤ 3 / 2
      have hv := velocity_near_of_conf hq (fun t' ht' => (hconf l hl t' ht').1)
      have hv' : |l.2 1 / b - c₁ / b| ≤ 1 / 2 := by
        rw [← sub_div, abs_div, abs_of_pos hb, div_le_iff₀ hb]
        have : |l.2 1 - c₁| * q ≤ b / 2 * q := by linarith
        exact le_of_mul_le_mul_right (by linarith) hq
      have h1 := Int.floor_le (l.2 1 / b)
      have h2 := Int.lt_floor_add_one (l.2 1 / b)
      rw [abs_le] at hv' ⊢
      constructor <;> linarith [hv'.1, hv'.2]
  have hmain := mass_le_of_density_le (measurable_obsG a b) hG hmap (hSm.prod hVm) θ hsub
  refine hmain.trans ?_
  gcongr
  rw [Measure.prod_prod]
  calc (volume.prod Measure.count) S * Measure.count V
      ≤ (ENNReal.ofReal (2 * (Λ + 1) + 1) * volume BaseF) * ENNReal.ofReal (2 * (3 / 2) + 1) := by
        gcongr
        · exact prod_count_box_le hBaseFm hfm (by linarith)
        · exact count_int_near_le _ _ (by norm_num)
    _ ≤ (ENNReal.ofReal (2 * (Λ + 1) + 1) * ENNReal.ofReal (q * (2 * w))) *
          ENNReal.ofReal (2 * (3 / 2) + 1) := by
        gcongr
        rw [hBaseF, volume_fin2_eq (measurableSet_chartPar s q c₀ c₁ w)]
        exact volume_chartPar_le s q c₀ c₁ w hw
    _ = ENNReal.ofReal (4 * (2 * Λ + 3) * (q * (2 * w))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- A chart packet whose predictor values lie in `[-A₀, A₀]` has its mass at pure density at
most `θ` bounded by `θ` times `(2Λ + 3)` times the area of the part of its parallelogram where
`|f| ≤ A₀`. -/
lemma thin_packet_diff_le {μ : Measure (Coeff × ℝ)} {g : (Fin 2 → ℝ) × ℤ → ℝ≥0∞}
    (hg : Measurable g) {a : ℝ} (ha : 0 < a)
    (hmap : Measure.map (obsL a) μ = (volume.prod Measure.count).withDensity g)
    {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) {A : Set Coeff} {s q c₀ c₁ w Λ A₀ : ℝ} (hΛ : 0 ≤ Λ)
    (hconf : ∀ l ∈ A, ∀ t ∈ Icc s (s + q),
      |spatial l t - (c₀ + c₁ * t)| ≤ w ∧ |hidden l t - f t (spatial l t)| ≤ Λ * a)
    (hval : ∀ l ∈ A, ∀ t ∈ Icc s (s + q), |f t (spatial l t)| ≤ A₀) (θ : ℝ≥0∞) :
    μ ((A ×ˢ Icc s (s + q)) \ {p | θ < g (obsL a p)}) ≤
      θ * (ENNReal.ofReal (2 * Λ + 3) * volume {p : ℝ × ℝ |
        p.1 ∈ Icc s (s + q) ∧ |p.2 - (c₀ + c₁ * p.1)| ≤ w ∧ |f p.1 p.2| ≤ A₀}) := by
  set Z : Set (ℝ × ℝ) := {p : ℝ × ℝ |
    p.1 ∈ Icc s (s + q) ∧ |p.2 - (c₀ + c₁ * p.1)| ≤ w ∧ |f p.1 p.2| ≤ A₀} with hZ
  have hZm : MeasurableSet Z := by
    show MeasurableSet ((Prod.fst ⁻¹' Icc s (s + q)) ∩
      ({p : ℝ × ℝ | |p.2 - (c₀ + c₁ * p.1)| ≤ w} ∩ {p : ℝ × ℝ | |f p.1 p.2| ≤ A₀}))
    refine (measurableSet_Icc.preimage measurable_fst).inter ((measurableSet_le ?_ ?_).inter
      (measurableSet_le ?_ ?_))
    · fun_prop
    · fun_prop
    · exact (continuous_abs.comp hf.continuous).measurable
    · fun_prop
  set ZF : Set (Fin 2 → ℝ) := {v | (v 0, v 1) ∈ Z} with hZF
  have hZFm : MeasurableSet ZF := hZm.preimage (by fun_prop)
  have hfm : Measurable (fun v : Fin 2 → ℝ => f (v 0) (v 1) / a) := by
    have h' : Continuous (fun v : Fin 2 → ℝ => f (v 0) (v 1)) :=
      hf.continuous.comp (f := fun v : Fin 2 → ℝ => (v 0, v 1)) (by fun_prop)
    exact h'.measurable.div_const a
  set S : Set ((Fin 2 → ℝ) × ℤ) :=
    {x | x.1 ∈ ZF ∧ |(x.2 : ℝ) - f (x.1 0) (x.1 1) / a| ≤ Λ + 1} with hS
  have hSm : MeasurableSet S := by
    show MeasurableSet ((Prod.fst ⁻¹' ZF) ∩
      {x : (Fin 2 → ℝ) × ℤ | |(x.2 : ℝ) - f (x.1 0) (x.1 1) / a| ≤ Λ + 1})
    refine (hZFm.preimage measurable_fst).inter (measurableSet_le ?_ measurable_const)
    have h2 : Measurable (fun p : (Fin 2 → ℝ) × ℤ => ((p.2 : ℤ) : ℝ)) :=
      (measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp measurable_snd
    exact (h2.sub (hfm.comp measurable_fst)).abs
  have hsub : A ×ˢ Icc s (s + q) ⊆ obsL a ⁻¹' S := by
    rintro ⟨l, t⟩ ⟨hl, ht⟩
    obtain ⟨hc, hx⟩ := hconf l hl t ht
    refine ⟨?_, ?_⟩
    · show (t, spatial l t) ∈ Z
      exact ⟨ht, hc, hval l hl t ht⟩
    · show |((⌊hidden l t / a⌋ : ℤ) : ℝ) - f t (spatial l t) / a| ≤ Λ + 1
      exact floor_near_of_fit ha hx
  refine (mass_le_of_density_le (measurable_obsL a) hg hmap hSm θ hsub).trans ?_
  gcongr
  calc (volume.prod Measure.count) S ≤ ENNReal.ofReal (2 * (Λ + 1) + 1) * volume ZF :=
        prod_count_box_le hZFm hfm (by linarith)
    _ = ENNReal.ofReal (2 * Λ + 3) * volume Z := by
        rw [hZF, volume_fin2_eq hZm]
        congr 2
        ring

end Submission.Obl.k4_scalar_terminal_chart_packet_extraction
