import Submission.Obl.k4_critical_switching_state_preparation.StateCoding

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Time normalization preserves the original source event, exact pair state,
and raw velocity bin, so the native numerator passes without any mass loss. -/
theorem normalized_source_palette_cap (h : cfg.Valid) (k : ℕ) (s : ℝ)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (a ω : ℝ)
    (source : Set (α × ℝ)) {C : ℝ≥0∞}
    (hcap : ∀ (u : ℤ × (Fin 3 → ℤ)) (z : ℤ),
      cfg.μ k {p | p ∈ source ∧ cfg.sourcePair k s i L a ω p = u ∧
        ⌊cfg.b k p.1 3 / ω⌋ = z} ≤ C * cfg.π k {w | ⌊w / ω⌋ = z}) :
    ∀ (u : ℤ × (Fin 3 → ℤ)) (z : ℤ),
      ((cfg.ρ k).restrict source).map (cfg.normalizeTime k s i)
        {p | cfg.normalizedPair k s i L a ω p = u ∧ ⌊cfg.b k p.1 3 / ω⌋ = z} ≤
          C * cfg.π k {w | ⌊w / ω⌋ = z} := by
  intro u z
  have hb := (h.basic k).1
  have hkey := measurable_normalizedPair h k s i L a ω
  have hvel : Measurable (fun p : α × ℝ => ⌊cfg.b k p.1 3 / ω⌋) := by fun_prop
  have hB : MeasurableSet {p | cfg.normalizedPair k s i L a ω p = u ∧
      ⌊cfg.b k p.1 3 / ω⌋ = z} := (measurableSet_eq_fun hkey measurable_const).inter
    (measurableSet_eq_fun hvel measurable_const)
  rw [Measure.map_apply (cfg.measurable_normalizeTime k s i) hB,
    Measure.restrict_apply ((cfg.measurable_normalizeTime k s i) hB)]
  have heq : (cfg.normalizeTime k s i ⁻¹'
      {p | cfg.normalizedPair k s i L a ω p = u ∧ ⌊cfg.b k p.1 3 / ω⌋ = z}) ∩ source =
      {p | p ∈ source ∧ cfg.sourcePair k s i L a ω p = u ∧ ⌊cfg.b k p.1 3 / ω⌋ = z} := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, normalizedPair,
      physicalTime_normalizeTime, normalizeTime_fst]
    tauto
  rw [heq]
  exact ((h.basic k).2.2.2.2.1 _).trans (hcap u z)

/-- Actual finite source pairs remain actual pairs after changing time. -/
theorem normalized_source_pair_support (h : cfg.Valid) (k : ℕ) (s : ℝ)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (a ω : ℝ)
    (source : Set (α × ℝ)) (hsource : MeasurableSet source)
    (F : Finset (ℤ × (Fin 3 → ℤ)))
    (hF : ∀ p ∈ source, cfg.sourcePair k s i L a ω p ∈ F) :
    ∀ᵐ p ∂((cfg.ρ k).restrict source).map (cfg.normalizeTime k s i),
      cfg.normalizedPair k s i L a ω p ∈ F := by
  have hset : MeasurableSet {p | cfg.normalizedPair k s i L a ω p ∈ F} :=
    F.finite_toSet.measurableSet.preimage (measurable_normalizedPair h k s i L a ω)
  apply (ae_map_iff (cfg.measurable_normalizeTime k s i).aemeasurable hset).mpr
  filter_upwards [ae_restrict_mem hsource] with p hp
  simpa only [normalizedPair, physicalTime_normalizeTime] using hF p hp

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
