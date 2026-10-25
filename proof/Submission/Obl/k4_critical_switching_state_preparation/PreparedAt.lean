import Submission.Obl.k4_critical_switching_state_preparation.HorizontalAssembly
import Submission.Obl.k4_critical_switching_state_preparation.NormalizedPalette
import Submission.Obl.k4_critical_switching_state_preparation.ReferenceWeights
import Submission.Obl.k4_critical_switching_state_preparation.PreparationBudget
import Submission.Obl.k4_critical_switching_state_preparation.SourceMass
import Submission.Obl.k4_critical_switching_state_preparation.SimultaneousPruning

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Inherited
open scoped ENNReal

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original source, its actual fine table and native numerators assemble
into the frozen prepared probability, with transport in every exact bin. -/
theorem AssignmentLevel.prepared_at (h : cfg.Valid) {k : ℕ} {s η ζ δ : ℝ}
    {depths : Finset ℝ} {i : Fin (cfg.n k s)} {L : Fin 4 → ℝ}
    (parent : cfg.AssignmentLevel k s) (src : cfg.RegularPairSource k s (s / 16) η ζ depths i L)
    (hζδ : ζ ≤ δ)
    (hmass : ENNReal.ofReal (cfg.N k ^ (-η) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s i) ≤
        cfg.ρ k (cfg.primitiveEvent k s i L (cfg.N k ^ η * cfg.N k ^ (-s))))
    (Ffine : Finset (ℤ × (Fin 3 → ℤ)))
    (hFfine : ∀ p ∈ src.source, cfg.sourcePair k s i L (cfg.N k ^ (-s - s / 16))
      (cfg.N k ^ (-200 * s)) p ∈ Ffine)
    (hcard : (Ffine.card : ℝ) * (cfg.N k ^ (-200 * s)) ^ 3 ≤
      1073741824 * cfg.K k ^ 20 * cfg.N k ^ (cfg.d * (s / 16)))
    (hraw : ∀ (u : ℤ × (Fin 3 → ℤ)) (z : ℤ),
      cfg.μ k {p | p ∈ src.source ∧ cfg.sourcePair k s i L
        (cfg.N k ^ (-s - s / 16)) (cfg.N k ^ (-200 * s)) p = u ∧
          ⌊cfg.b k p.1 3 / cfg.N k ^ (-200 * s)⌋ = z} ≤
      ENNReal.ofReal (1536 * cfg.K k ^ 4 * cfg.timeLength k s ^ 4 *
        (cfg.N k ^ (-200 * s)) ^ 3 * (cfg.N k ^ (-s - s / 16)) ^ cfg.d) *
          cfg.π k {w | ⌊w / cfg.N k ^ (-200 * s)⌋ = z})
    (hdom : ((cfg.ρ k).restrict src.source).map (cfg.normalizeTime k s i) ≤
      ENNReal.ofReal (cfg.K k * cfg.timeLength k s) •
        ((cfg.ν k).restrict (cfg.A k s i)).prod volume)
    (hbound : 8 * cfg.K k ^ 4 ≤ cfg.N k ^ δ)
    (herror : cfg.N k ^ (-cfg.e₀) / cfg.timeLength k s ≤ cfg.N k ^ (-200 * s))
    (hbudget :
      4294967296 * cfg.K k ^ 22 * cfg.N k ^ (-(δ / 4)) ≤ cfg.N k ^ (-η) ∧
      4 * cfg.N k ^ (-(δ / 4)) ≤ cfg.N k ^ (-η) ∧
      2 * cfg.N k ^ (-δ) ≤ cfg.N k ^ (-η) ∧
      cfg.K k * cfg.N k ^ (δ / 4) ≤ cfg.N k ^ δ ∧
      3072 * cfg.K k ^ 4 * cfg.N k ^ (δ / 4) ≤ cfg.N k ^ δ)
    (hinterval : ∀ c z r : ℝ, cfg.N k ^ (-200 * s) ≤ r → r ≤ 1 →
      shiftedPalette (cfg.π k) (cfg.N k ^ (-200 * s)) c (Icc (z - r) (z + r)) ≤
        ENNReal.ofReal (cfg.N k ^ δ * r ^ cfg.S)) :
    cfg.PreparedSwitching k s η δ i L := by
  classical
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  letI : IsProbabilityMeasure (cfg.π k) := (h.basic k).2.2.1
  letI := h.residual_finite k
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hK := h.subpower.1 k
  let H := cfg.timeLength k s
  let ω := cfg.N k ^ (-200 * s)
  let a := cfg.N k ^ (-s - s / 16)
  let R := H ^ 4 * ω ^ 3 * a ^ cfg.d
  let τ := cfg.N k ^ (-(δ / 4))
  let m := (cfg.ν k).restrict (cfg.A k s i)
  let μ₀ := ((cfg.ρ k).restrict src.source).map (cfg.normalizeTime k s i)
  let G₀ := cfg.physicalTime k s i ⁻¹' src.source
  let key := cfg.normalizedPair k s i L a ω
  let W := (cfg.ρ k).real src.source
  let p := (cfg.ν k).real (cfg.A k s i)
  have hH : 0 < H := cfg.timeLength_pos k s
  have hω : 0 < ω := Real.rpow_pos_of_pos hN _
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  have hR : 0 < R := by dsimp [R]; positivity
  have hτ : 0 < τ := Real.rpow_pos_of_pos hN _
  have hp : 0 ≤ p := measureReal_nonneg
  have hW : 0 < W := ENNReal.toReal_pos (src.positive_mass h parent hmass).ne'
    (measure_ne_top (cfg.ρ k) _)
  have hG₀ : MeasurableSet G₀ := src.measurable_source.preimage (cfg.measurable_physicalTime k s i)
  have hpreG : cfg.normalizeTime k s i ⁻¹' G₀ = src.source := by
    ext q
    simp only [G₀, mem_preimage, physicalTime_normalizeTime]
  have hμG : μ₀ G₀ = cfg.ρ k src.source := by
    dsimp [μ₀]
    rw [Measure.map_apply (cfg.measurable_normalizeTime k s i) hG₀, hpreG,
      Measure.restrict_apply src.measurable_source, inter_self]
  have hμW : μ₀ G₀ = ENNReal.ofReal W := hμG.trans
    (ENNReal.ofReal_toReal (measure_ne_top (cfg.ρ k) _)).symm
  have hm : m univ = ENNReal.ofReal p := by
    simp [m, p, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top (cfg.ν k) _)]
  have hscale : a ^ cfg.d * cfg.N k ^ (cfg.d * (s / 16)) = (cfg.N k ^ (-s)) ^ cfg.d := by
    dsimp [a]
    rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN, ← Real.rpow_mul hN.le]
    congr 1
    ring
  have hmassreal := src.mass_floors_real h parent hmass
  have hloss := pruning_reference_losses hN hK hH (Real.rpow_pos_of_pos hN _) ha hω hp
    hscale hcard hmassreal.1 hmassreal.2 hbudget.1 hbudget.2.1 hbudget.2.2.1
  have hstrict := finite_reference_budget μ₀ m G₀ Ffine hR.le hτ.le (mul_pos hτ hH).le hp
    hW hμW hm hloss.1 hloss.2.1
  have hGunit : G₀ ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
    intro q hq
    refine ⟨mem_univ _, ?_⟩
    have hh := cfg.normalizeTime_mem_unit k s i (src.source_subset hq).2.1
    simpa only [normalizeTime_physicalTime] using hh
  have hkey : Measurable key := measurable_normalizedPair h k s i L a ω
  obtain ⟨E, hE, hEsub, hretain, hE0, hσ, hσfull, hσdom, hσtime, hσpal⟩ :=
    Pruning.exists_pruned_law m μ₀ ENNReal.ofReal_ne_top hdom hG₀ measurableSet_Icc
      (by simp [Real.volume_Icc]) hGunit hkey (finiteReferenceWeights Ffine R)
      (ENNReal.ofReal_ne_zero_iff.mpr hτ) ENNReal.ofReal_ne_top
      (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hτ hH)) ENNReal.ofReal_ne_top hstrict
  let σ := (μ₀ E)⁻¹ • μ₀.restrict E
  let π₀ := shiftedPalette (cfg.π k) ω (cfg.c k s i 1)
  have hsurvive := surviving_mass_of_finite_reference μ₀ m G₀ E Ffine hR.le hτ.le
    (mul_pos hτ hH).le hp hW hμW hm hloss.1 hloss.2.1 hloss.2.2 hretain
  have hνrepr : ENNReal.ofReal p = cfg.ν k (cfg.A k s i) :=
    ENNReal.ofReal_toReal (measure_ne_top (cfg.ν k) _)
  have hmassfinal : ENNReal.ofReal (cfg.N k ^ (-δ) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s i) ≤ μ₀ E := by
    rw [← hνrepr, ← ENNReal.ofReal_mul (by positivity)]
    convert hsurvive.2 using 1
    congr 1
  have htimefinal : σ ≤ ENNReal.ofReal (cfg.N k ^ δ) • ((σ.map Prod.fst).prod volume) := by
    apply hσtime.trans
    rw [pruning_time_coefficient hN hH]
    apply Measure.le_iff.mpr
    intro B hB
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hbudget.2.2.2.1) le_rfl
  have hsupport : ∀ᵐ q ∂μ₀, key q ∈ Ffine :=
    normalized_source_pair_support h k s i L a ω src.source src.measurable_source Ffine hFfine
  have hnormcap := normalized_source_palette_cap h k s i L a ω src.source hraw
  have hcoeff : 1536 * cfg.K k ^ 4 * cfg.timeLength k s ^ 4 * ω ^ 3 * a ^ cfg.d =
      (1536 * cfg.K k ^ 4) * R := by dsimp [R, H]; ring
  rw [hcoeff] at hnormcap
  have hshift := shifted_finite_reference_palette_cap μ₀ key (fun q => cfg.b k q.1 3)
    (cfg.π k) Ffine hsupport hω (by positivity : 0 ≤ 1536 * cfg.K k ^ 4) hnormcap
    (cfg.c k s i 1)
  have hshift' : ∀ u z, μ₀ {q | key q = u ∧ ⌊cfg.centeredVelocity k s i q.1 / ω⌋ = z} ≤
      ENNReal.ofReal (3072 * cfg.K k ^ 4) * finiteReferenceWeights Ffine R u *
        π₀ {w | ⌊w / ω⌋ = z} := by
    simpa only [show 2 * (1536 * cfg.K k ^ 4) = 3072 * cfg.K k ^ 4 by ring,
      centeredVelocity] using hshift
  have hpalcoef : ENNReal.ofReal (3072 * cfg.K k ^ 4) / ENNReal.ofReal τ ≤
      ENNReal.ofReal (cfg.N k ^ δ) := by
    rw [pruning_palette_coefficient hN]
    exact ENNReal.ofReal_le_ofReal hbudget.2.2.2.2
  have hpairpal : ∀ u z, σ {q | key q = u ∧ ⌊cfg.centeredVelocity k s i q.1 / ω⌋ = z} ≤
      ENNReal.ofReal (cfg.N k ^ δ) * σ {q | key q = u} * π₀ {w | ⌊w / ω⌋ = z} := by
    intro u z
    have hh := hσpal u {q | ⌊cfg.centeredVelocity k s i q.1 / ω⌋ = z}
      (ENNReal.ofReal (3072 * cfg.K k ^ 4)) (π₀ {w | ⌊w / ω⌋ = z}) (hshift' u z)
    exact hh.trans (mul_le_mul' (mul_le_mul' hpalcoef le_rfl) le_rfl)
  have hnatpal := palette_cap_of_encode σ key (fun q => ⌊cfg.centeredVelocity k s i q.1 / ω⌋)
    (fun z => π₀ {w | ⌊w / ω⌋ = z}) (ENNReal.ofReal (cfg.N k ^ δ)) hpairpal
  refine ⟨src.source, σ, π₀, cfg.fineState k s i L ω, E, src.pairs,
    src.measurable_source, src.source_subset, src.coefficients, ?_, ?_, ?_, ?_⟩
  · exact parent.horizontalLaw_of_final_bounds h src σ π₀ E hσ
      (shiftedPalette_probability _ _ _) hE hσfull (fun q hq => hEsub hq)
      hbound herror htimefinal hnatpal (hinterval (cfg.c k s i 1))
  · have hc := normalized_source_pair_support h k s i L (cfg.N k ^ (-s - s / 16))
      (cfg.N k ^ (-10 * s)) src.source src.measurable_source src.pairs
      (fun q hq => (src.pairs_exact _).mpr ⟨q, hq, rfl⟩)
    have hcσ := ae_mono hσdom (Measure.ae_smul_measure hc (μ₀ E)⁻¹)
    filter_upwards [hcσ] with q hq
    simpa only [normalizedPair_key] using hq
  · exact src.pairs_card.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  · intro j
    let B : Set (α × ℝ) := {q | cfg.midpointBin k s (s / 16) i L q.1 = j}
    have hB : MeasurableSet B := measurableSet_eq_fun
      ((measurable_midpointBin h k s (s / 16) i L).comp measurable_fst) measurable_const
    have htransport := mass_transport_of_scaled_domination σ μ₀ hE0 (measure_ne_top μ₀ E)
      hmassfinal hσdom B
    have hbin : μ₀ B = cfg.ρ k (src.source ∩ B) := by
      dsimp [μ₀]
      rw [Measure.map_apply (cfg.measurable_normalizeTime k s i) hB,
        Measure.restrict_apply ((cfg.measurable_normalizeTime k s i) hB)]
      congr 1
      ext q
      simp only [B, mem_inter_iff, mem_preimage, mem_setOf_eq, normalizeTime_fst, and_comm]
    rwa [hbin] at htransport

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
