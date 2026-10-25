import Mathlib

/-
Adapted from this LOT tree, o178, session x0596, `AngularTransfer.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Charging a few velocity bins per observation against the pure density

Abstract form of the angular-cap step used repeatedly in Section 10 (full-time
localization, angular fullness, projected angular caps).  An incidence law `μ`
has a joint law of (observation, velocity bin) with density `G` and an
observation law with density `g`.  On the *good* incidences, where
`G ≤ c * g`, the incidences whose velocity bin lies in a list of at most `m`
bins determined by the observation have mass at most `c * m * μ univ`.

No measurability of the good event is assumed beyond that of `G` and `g`;
the list of bins must have measurable membership events.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory

noncomputable section

variable {X Ω V : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace V]
  [Countable V] [MeasurableSingletonClass V]

/-- The event of incidences whose velocity bin is listed by the observation. -/
theorem measurableSet_listed (bins : Ω → Finset V)
    (hbins : ∀ w, MeasurableSet {o | w ∈ bins o}) :
    MeasurableSet {q : Ω × V | q.2 ∈ bins q.1} := by
  have : {q : Ω × V | q.2 ∈ bins q.1} = ⋃ w : V, {o | w ∈ bins o} ×ˢ {w} := by
    ext ⟨o, w⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · intro h; exact ⟨w, h, rfl⟩
    · rintro ⟨w', h, rfl⟩; exact h
  rw [this]
  exact MeasurableSet.iUnion fun w => (hbins w).prod (measurableSet_singleton w)

/-- **Angular charging.**  If the joint (observation, bin) law has density `G`,
the observation law has density `g`, and on the counted event `G ≤ c * g`, then
listing at most `m` bins per observation costs at most `c * m` times the mass. -/
theorem listed_bins_mass_le (μ : Measure X) (ρ : Measure Ω) [SFinite ρ]
    (O : X → Ω) (Vb : X → V) (hO : Measurable O) (hV : Measurable Vb)
    (G : Ω × V → ENNReal) (g : Ω → ENNReal) (hGm : Measurable G) (hgm : Measurable g)
    (hG : Measure.map (fun x => (O x, Vb x)) μ = (ρ.prod Measure.count).withDensity G)
    (hg : Measure.map O μ = ρ.withDensity g)
    (c : ENNReal) (bins : Ω → Finset V) (m : ℕ)
    (hbins : ∀ w, MeasurableSet {o | w ∈ bins o}) (hcard : ∀ o, (bins o).card ≤ m) :
    μ {x | G (O x, Vb x) ≤ c * g (O x) ∧ Vb x ∈ bins (O x)} ≤ c * m * μ Set.univ := by
  set Y : Set (Ω × V) := {q | G q ≤ c * g q.1 ∧ q.2 ∈ bins q.1} with hYdef
  have hYm : MeasurableSet Y := by
    refine MeasurableSet.inter ?_ (measurableSet_listed bins hbins)
    exact measurableSet_le hGm (measurable_const.mul (hgm.comp measurable_fst))
  have hΦ : Measurable fun x => (O x, Vb x) := hO.prodMk hV
  have hpre : {x | G (O x, Vb x) ≤ c * g (O x) ∧ Vb x ∈ bins (O x)} =
      (fun x => (O x, Vb x)) ⁻¹' Y := rfl
  rw [hpre, ← Measure.map_apply hΦ hYm, hG, withDensity_apply _ hYm]
  -- bound the density on `Y` by `c * g` of the observation
  have hle : ∫⁻ q in Y, G q ∂(ρ.prod Measure.count) ≤
      ∫⁻ q, Y.indicator (fun q => c * g q.1) q ∂(ρ.prod Measure.count) := by
    rw [lintegral_indicator hYm]
    apply setLIntegral_mono' hYm
    intro q hq
    exact hq.1
  refine hle.trans ?_
  have hmeas : Measurable (Y.indicator (fun q : Ω × V => c * g q.1)) :=
    (measurable_const.mul (hgm.comp measurable_fst)).indicator hYm
  rw [lintegral_prod _ hmeas.aemeasurable]
  -- the inner sum over bins
  have hinner : ∀ o, ∫⁻ w, Y.indicator (fun q : Ω × V => c * g q.1) (o, w) ∂Measure.count ≤
      (m : ENNReal) * (c * g o) := by
    intro o
    rw [lintegral_count]
    calc ∑' w, Y.indicator (fun q : Ω × V => c * g q.1) (o, w)
        ≤ ∑' w, (bins o : Set V).indicator (fun _ => c * g o) w := by
          apply ENNReal.tsum_le_tsum
          intro w
          by_cases hw : (o, w) ∈ Y
          · have hwb : w ∈ (bins o : Set V) := hw.2
            rw [Set.indicator_of_mem hw, Set.indicator_of_mem hwb]
          · rw [Set.indicator_of_notMem hw]
            exact bot_le
      _ = ∑ w ∈ bins o, c * g o := by
          rw [tsum_eq_sum (s := bins o)]
          · apply Finset.sum_congr rfl
            intro w hw
            rw [Set.indicator_of_mem (by simpa using hw)]
          · intro w hw
            rw [Set.indicator_of_notMem (by simpa using hw)]
      _ = (bins o).card * (c * g o) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ENNReal) * (c * g o) := by
          gcongr
          exact_mod_cast hcard o
  calc ∫⁻ o, ∫⁻ w, Y.indicator (fun q : Ω × V => c * g q.1) (o, w) ∂Measure.count ∂ρ
      ≤ ∫⁻ o, (m : ENNReal) * (c * g o) ∂ρ := lintegral_mono hinner
    _ = ∫⁻ o, ((m : ENNReal) * c) * g o ∂ρ := by
        congr 1; ext o; ring
    _ = (m : ENNReal) * c * ∫⁻ o, g o ∂ρ := lintegral_const_mul _ hgm
    _ = c * m * μ Set.univ := by
        have hu : ∫⁻ o, g o ∂ρ = μ Set.univ := by
          rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hg,
            Measure.map_apply hO MeasurableSet.univ, Set.preimage_univ]
        rw [hu]; ring

/-- **Angular charging with a support.**  If the bins vanish outside a measurable
set `S` of observations, the bound is `c * m` times the mass of `O ⁻¹' S`. -/
theorem listed_bins_mass_le_support (μ : Measure X) (ρ : Measure Ω) [SFinite ρ]
    (O : X → Ω) (Vb : X → V) (hO : Measurable O) (hV : Measurable Vb)
    (G : Ω × V → ENNReal) (g : Ω → ENNReal) (hGm : Measurable G) (hgm : Measurable g)
    (hG : Measure.map (fun x => (O x, Vb x)) μ = (ρ.prod Measure.count).withDensity G)
    (hg : Measure.map O μ = ρ.withDensity g)
    (c : ENNReal) (bins : Ω → Finset V) (m : ℕ)
    (hbins : ∀ w, MeasurableSet {o | w ∈ bins o}) (hcard : ∀ o, (bins o).card ≤ m)
    (S : Set Ω) (hS : MeasurableSet S) (hsupp : ∀ o, o ∉ S → bins o = ∅) :
    μ {x | G (O x, Vb x) ≤ c * g (O x) ∧ Vb x ∈ bins (O x)} ≤ c * m * μ (O ⁻¹' S) := by
  set Y : Set (Ω × V) := {q | G q ≤ c * g q.1 ∧ q.2 ∈ bins q.1} with hYdef
  have hYm : MeasurableSet Y := by
    refine MeasurableSet.inter ?_ (measurableSet_listed bins hbins)
    exact measurableSet_le hGm (measurable_const.mul (hgm.comp measurable_fst))
  have hΦ : Measurable fun x => (O x, Vb x) := hO.prodMk hV
  have hpre : {x | G (O x, Vb x) ≤ c * g (O x) ∧ Vb x ∈ bins (O x)} =
      (fun x => (O x, Vb x)) ⁻¹' Y := rfl
  rw [hpre, ← Measure.map_apply hΦ hYm, hG, withDensity_apply _ hYm]
  have hle : ∫⁻ q in Y, G q ∂(ρ.prod Measure.count) ≤
      ∫⁻ q, Y.indicator (fun q => c * g q.1) q ∂(ρ.prod Measure.count) := by
    rw [lintegral_indicator hYm]
    apply setLIntegral_mono' hYm
    intro q hq
    exact hq.1
  refine hle.trans ?_
  have hmeas : Measurable (Y.indicator (fun q : Ω × V => c * g q.1)) :=
    (measurable_const.mul (hgm.comp measurable_fst)).indicator hYm
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hinner : ∀ o, ∫⁻ w, Y.indicator (fun q : Ω × V => c * g q.1) (o, w) ∂Measure.count ≤
      S.indicator (fun o => (m : ENNReal) * (c * g o)) o := by
    intro o
    rw [lintegral_count]
    by_cases ho : o ∈ S
    · rw [Set.indicator_of_mem ho]
      calc ∑' w, Y.indicator (fun q : Ω × V => c * g q.1) (o, w)
          ≤ ∑' w, (bins o : Set V).indicator (fun _ => c * g o) w := by
            apply ENNReal.tsum_le_tsum
            intro w
            by_cases hw : (o, w) ∈ Y
            · have hwb : w ∈ (bins o : Set V) := hw.2
              rw [Set.indicator_of_mem hw, Set.indicator_of_mem hwb]
            · rw [Set.indicator_of_notMem hw]
              exact bot_le
        _ = ∑ w ∈ bins o, c * g o := by
            rw [tsum_eq_sum (s := bins o)]
            · apply Finset.sum_congr rfl
              intro w hw
              rw [Set.indicator_of_mem (by simpa using hw)]
            · intro w hw
              rw [Set.indicator_of_notMem (by simpa using hw)]
        _ = (bins o).card * (c * g o) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (m : ENNReal) * (c * g o) := by
            gcongr
            exact_mod_cast hcard o
    · rw [Set.indicator_of_notMem ho]
      have hempty := hsupp o ho
      apply le_of_eq
      rw [ENNReal.tsum_eq_zero]
      intro w
      apply Set.indicator_of_notMem
      intro hw
      have := hw.2
      rw [hempty] at this
      simp at this
  calc ∫⁻ o, ∫⁻ w, Y.indicator (fun q : Ω × V => c * g q.1) (o, w) ∂Measure.count ∂ρ
      ≤ ∫⁻ o, S.indicator (fun o => (m : ENNReal) * (c * g o)) o ∂ρ := lintegral_mono hinner
    _ = ∫⁻ o in S, (m : ENNReal) * (c * g o) ∂ρ := lintegral_indicator hS _
    _ = ∫⁻ o in S, ((m : ENNReal) * c) * g o ∂ρ := by
        congr 1; ext o; ring
    _ = (m : ENNReal) * c * ∫⁻ o in S, g o ∂ρ := lintegral_const_mul _ hgm
    _ = c * m * μ (O ⁻¹' S) := by
        have hu : ∫⁻ o in S, g o ∂ρ = μ (O ⁻¹' S) := by
          rw [← withDensity_apply _ hS, ← hg, Measure.map_apply hO hS]
        rw [hu]; ring

end

end Submission.Obl.k4_raw_localized_native_systems.C
