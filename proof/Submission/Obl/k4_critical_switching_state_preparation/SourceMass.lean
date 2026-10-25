import Submission.Obl.k4_critical_switching_state_preparation.CriticalSource

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The full original parent prior supplies exactly four powers of its actual
time length after multiplying by the primitive incidence floor. -/
theorem AssignmentLevel.primitive_floor_absolute (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (parent : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (η : ℝ) :
    ENNReal.ofReal (cfg.N k ^ (-η) * cfg.timeLength k s ^ 4 *
      (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2) ≤
      ENNReal.ofReal (cfg.N k ^ (-η) / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i) := by
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hA : ENNReal.ofReal (cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d /
      cfg.K k ^ 2) ≤ cfg.ν k (cfg.A k s i) := by
    have hh := ENNReal.ofReal_le_ofReal (parent.critical_prior_bounds h i).1
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top (cfg.ν k) _)] using hh
  calc
    _ = ENNReal.ofReal (cfg.N k ^ (-η) / (2 : ℝ) ^ cfg.T k s) *
        ENNReal.ofReal (cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d /
          cfg.K k ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [timeLength]
      ring
    _ ≤ _ := mul_le_mul' le_rfl hA

/-- A dense primitive has positive original residual mass on its exact regular source. -/
theorem RegularPairSource.positive_mass (h : cfg.Valid) {k : ℕ} {s v η δ : ℝ}
    {depths : Finset ℝ} {i : Fin (cfg.n k s)} {L : Fin 4 → ℝ}
    (src : cfg.RegularPairSource k s v η δ depths i L) (parent : cfg.AssignmentLevel k s)
    (hmass : ENNReal.ofReal (cfg.N k ^ (-η) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s i) ≤
        cfg.ρ k (cfg.primitiveEvent k s i L (cfg.N k ^ η * cfg.N k ^ (-s)))) :
    0 < cfg.ρ k src.source := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hH := cfg.timeLength_pos k s
  rw [src.source_mass]
  exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < cfg.N k ^ (-η) *
    cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2)).trans_le
      ((parent.primitive_floor_absolute h i η).trans hmass)

/-- Relative and absolute versions of the unchanged original primitive mass,
in real units for the simultaneous loss accounting. -/
theorem RegularPairSource.mass_floors_real (h : cfg.Valid) {k : ℕ} {s v η δ : ℝ}
    {depths : Finset ℝ} {i : Fin (cfg.n k s)} {L : Fin 4 → ℝ}
    (src : cfg.RegularPairSource k s v η δ depths i L) (parent : cfg.AssignmentLevel k s)
    (hmass : ENNReal.ofReal (cfg.N k ^ (-η) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s i) ≤
        cfg.ρ k (cfg.primitiveEvent k s i L (cfg.N k ^ η * cfg.N k ^ (-s)))) :
    cfg.N k ^ (-η) * cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i) ≤
        (cfg.ρ k).real src.source ∧
      cfg.N k ^ (-η) * cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2 ≤
        (cfg.ρ k).real src.source := by
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  letI := h.residual_finite k
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hH := cfg.timeLength_pos k s
  have hmass' : ENNReal.ofReal (cfg.N k ^ (-η) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s i) ≤ cfg.ρ k src.source := by rw [src.source_mass]; exact hmass
  have hrel := ENNReal.toReal_mono (measure_ne_top (cfg.ρ k) _) hmass'
  have habs := ENNReal.toReal_mono (measure_ne_top (cfg.ρ k) _)
    ((parent.primitive_floor_absolute h i η).trans hmass')
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hrel
  rw [ENNReal.toReal_ofReal (by positivity)] at habs
  refine ⟨?_, habs⟩
  simpa only [timeLength, measureReal_def, div_eq_mul_inv] using hrel

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
