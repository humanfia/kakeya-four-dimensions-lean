import Submission.Obl.k4_scalar_grid_cartesian_field.Interface
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreStatement

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter
open Submission.Obl.k4_scalar_noisy_block_packets (blockLeft blockLength blockInterval)

/-- The named dyadic interval equals the frozen interval exactly. -/
theorem I_eq_blockInterval (data : Data) (T : ℕ) (j : Fin (2 ^ T)) :
    I data T j = blockInterval T j := by
  unfold I blockInterval blockLeft blockLength
  congr 1
  ring

theorem y_eq_scalarY (data : Data) : y data = scalarY := rfl

theorem x_eq_scalarX (data : Data) : x data = scalarX := rfl

theorem phys_eq_physCube (data : Data) (k : ℕ) (r : ℝ) :
    phys data k r = physCube (data.N k) r := rfl

theorem rowbin_eq_rowBin (data : Data) (k : ℕ) (r : ℝ) :
    rowbin data k r = rowBin (data.N k) r := rfl

/-- Every original floor code used for pruning is measurable. -/
theorem measurable_scalarY_incidence : Measurable (fun p : Incidence => scalarY p.1 p.2) := by
  unfold scalarY
  fun_prop

theorem measurable_scalarX_incidence : Measurable (fun p : Incidence => scalarX p.1 p.2) := by
  unfold scalarX
  fun_prop

theorem measurable_physCube (N r : ℝ) : Measurable (physCube N r) := by
  apply Measurable.of_eval
  intro e
  fin_cases e
  · change Measurable (fun p : Incidence => (⌊p.2 / N ^ (-r)⌋ : ℤ))
    exact (measurable_snd.div_const _).floor
  · change Measurable (fun p : Incidence => (⌊scalarY p.1 p.2 / N ^ (-r)⌋ : ℤ))
    exact (measurable_scalarY_incidence.div_const _).floor
  · change Measurable (fun p : Incidence => (⌊scalarX p.1 p.2 / N ^ (-r)⌋ : ℤ))
    exact (measurable_scalarX_incidence.div_const _).floor

/-- Original incidence measures have finite mass from their original density and time support. -/
theorem original_incidence_finite {ν : Measure Trajectory} [IsProbabilityMeasure ν]
    (ρ : Measure Incidence) {K : ℝ}
    (hdensity : ρ ≤ ENNReal.ofReal K • ν.prod volume)
    (htime : ρ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) : IsFiniteMeasure ρ := by
  constructor
  have hmass : ρ univ ≤ ENNReal.ofReal K := by
    calc
      _ = ρ (univ ×ˢ Icc (0 : ℝ) 1) := by
        simpa using (measure_inter_conull htime (s := univ)).symm
      _ ≤ (ENNReal.ofReal K • ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := hdensity _
      _ = ENNReal.ofReal K := by
        simp [Measure.smul_apply, Measure.prod_prod]
  exact hmass.trans_lt ENNReal.ofReal_lt_top

/-- The frozen original density makes every world finite before any later restriction. -/
theorem original_finite_of_base (data : Data) (hb : baseHyp data) (k : ℕ) (g : Fin (data.W k)) :
    IsFiniteMeasure (data.ρ k g) := by
  obtain ⟨hν, _, _, hdensity, htime⟩ := (hb k).2.2.1 g
  letI := hν
  exact original_incidence_finite _ hdensity htime

/-- The original incidence law inherits the original a.e. coefficient bound from its full prior. -/
theorem original_incidence_coefficients (data : Data) (hb : baseHyp data) (k : ℕ) (g : Fin (data.W k)) :
    ∀ᵐ p ∂data.ρ k g, ∀ e, |p.1.2 e| ≤ data.K k := by
  obtain ⟨hν, _, hcoeff, hdensity, _⟩ := (hb k).2.2.1 g
  letI := hν
  have hbad : data.ν k g {l | ¬∀ e, |l.2 e| ≤ data.K k} = 0 := ae_iff.mp hcoeff
  rw [ae_iff]
  have heq : {p : Incidence | ¬∀ e, |p.1.2 e| ≤ data.K k} =
      {l : Trajectory | ¬∀ e, |l.2 e| ≤ data.K k} ×ˢ (univ : Set ℝ) := by ext p; simp
  rw [heq]
  apply le_antisymm ?_ bot_le
  calc
    _ ≤ (ENNReal.ofReal (data.K k) • (data.ν k g).prod volume)
        ({l : Trajectory | ¬∀ e, |l.2 e| ≤ data.K k} ×ˢ univ) := hdensity _
    _ = 0 := by simp only [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, hbad, zero_mul, mul_zero]

/-- The whole scalar coefficient crop is an original measurable trajectory event. -/
theorem measurableSet_coefficient_bound (K : ℝ) : MeasurableSet {l : Trajectory | ∀ e, |l.2 e| ≤ K} := by
  have heq : {l : Trajectory | ∀ e, |l.2 e| ≤ K} = ⋂ e : Fin 5, {l : Trajectory | |l.2 e| ≤ K} := by
    ext l
    simp
  rw [heq]
  exact MeasurableSet.iInter fun e =>
    measurableSet_le ((measurable_pi_apply e).comp measurable_snd).abs measurable_const

/-- The physical unsheared scalar base is measurable in the original incidence coordinates. -/
theorem measurable_scalar_base : Measurable (fun p : Incidence => (![p.2, scalarY p.1 p.2] : Fin 2 → ℝ)) := by
  apply Measurable.of_eval
  intro e
  fin_cases e
  · change Measurable (fun p : Incidence => p.2)
    exact measurable_snd
  · change Measurable (fun p : Incidence => scalarY p.1 p.2)
    exact measurable_scalarY_incidence

end Submission.Obl.k4_scalar_grid_cartesian_field
