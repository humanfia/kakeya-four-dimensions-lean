import Submission.Obl.k4_subcritical_endpoint_native_pairing.EndpointLevel
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing.Readers

/-! Elementary facts about the prepared data at one sample: velocity bins as
intervals, the finite incidence mass, and the null set of dyadic block
endpoints. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_subcritical_endpoint_native_pairing.Data

noncomputable section

theorem floor_div_eq_iff {χ w : ℝ} (hχ : 0 < χ) (v : ℤ) :
    ⌊w / χ⌋ = v ↔ w ∈ Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ) := by
  rw [Int.floor_eq_iff, le_div_iff₀ hχ, div_lt_iff₀ hχ]
  rfl

theorem binSet_eq {χ : ℝ} (hχ : 0 < χ) (v : ℤ) :
    {w : ℝ | ⌊w / χ⌋ = v} = Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ) := by
  ext w
  exact floor_div_eq_iff hχ v

theorem abs_sub_floor_mul_le {χ w : ℝ} (hχ : 0 < χ) :
    |w - (⌊w / χ⌋ : ℝ) * χ| ≤ χ := by
  have h := (floor_div_eq_iff hχ ⌊w / χ⌋).mp rfl
  rw [abs_le]
  constructor <;> nlinarith [h.1, h.2]

theorem mem_Icc_floor_mul {χ w : ℝ} (hχ : 0 < χ) :
    w ∈ Icc ((⌊w / χ⌋ : ℝ) * χ) (((⌊w / χ⌋ : ℝ) + 1) * χ) := by
  have h := (floor_div_eq_iff hχ ⌊w / χ⌋).mp rfl
  exact ⟨h.1, h.2.le⟩

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The reference budget of one depth. -/
def depthBudget (cfg : Data α) (k : ℕ) (s ζ δ : ℝ) : ℝ :=
  4320 * cfg.K k * (2 * cfg.K k + 2) * (δ / cfg.hiddenWidth k s) ^ cfg.d *
    (cfg.N k ^ ζ * cfg.K k + 4096 * cfg.K k ^ 6)

theorem velocityWeight_eq (k : ℕ) {χ : ℝ} (hχ : 0 < χ) (v : ℤ) :
    cfg.velocityWeight k χ v = cfg.π k {w | ⌊w / χ⌋ = v} := by
  rw [velocityWeight, binSet_eq hχ]

theorem velocityWeight_ne_top (h : cfg.Prepared) (k : ℕ) (χ : ℝ) (v : ℤ) :
    cfg.velocityWeight k χ v ≠ ⊤ := by
  letI : IsProbabilityMeasure (cfg.π k) := (h.basic k).2.2.1
  exact measure_ne_top _ _

/-- The original incidence law has mass at most `K`. -/
theorem incidence_mass_le (h : cfg.Prepared) (k : ℕ) :
    cfg.μ k univ ≤ ENNReal.ofReal (cfg.K k) := by
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hs : MeasurableSet (univ ×ˢ Icc (0 : ℝ) 1 : Set (α × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hdom := (h.basic k).2.2.2.1 (univ ×ˢ Icc (0 : ℝ) 1)
  have hz := (h.basic k).2.2.2.2.2.1
  have heq : cfg.μ k univ = cfg.μ k (univ ×ˢ Icc (0 : ℝ) 1) := by
    have hh := measure_add_measure_compl (μ := cfg.μ k) hs
    rw [hz, add_zero] at hh
    exact hh.symm
  rw [heq]
  simpa [Measure.smul_apply, Measure.prod_prod, Real.volume_Icc] using hdom

theorem residual_mass_le (h : cfg.Prepared) (k : ℕ) :
    cfg.ρ k univ ≤ ENNReal.ofReal (cfg.K k) :=
  ((h.basic k).2.2.2.2.1 univ).trans (incidence_mass_le h k)

/-- Incidence times lie in the unit interval almost surely. -/
theorem ae_unit_time (h : cfg.Prepared) (k : ℕ) :
    ∀ᵐ p ∂cfg.μ k, p.2 ∈ Icc (0 : ℝ) 1 := by
  have hz := (h.basic k).2.2.2.2.2.1
  rw [ae_iff]
  apply measure_mono_null _ hz
  intro p hp
  simp only [mem_setOf_eq] at hp
  simp only [mem_compl_iff, mem_prod, mem_univ, true_and]
  exact hp

/-- Incidence times avoid the dyadic block endpoints almost surely. -/
theorem ae_not_dyadic (h : cfg.Prepared) (k T : ℕ) :
    ∀ᵐ p ∂cfg.μ k, p.2 ∉ dyadicEndpoints T := by
  rw [ae_iff]
  simp only [not_not]
  exact measure_time_countable_eq_zero (cfg.ν k) (cfg.μ k) _ (h.basic k).2.2.2.1
    (dyadicEndpoints_countable T)

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing
