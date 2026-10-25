/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarHeavyGroups/StateMixtureCaps.lean at aca48c1.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit 24a2b6f49c14677c4ad0c1641d50a425c1b7b813,
Submission/Obl/k4_scalar_mesh_projection/StateMixtureCaps.lean.
-/

import Submission.Lib.K4ScalarCoreTools.HeavyGroups.PairRestriction

namespace Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Set MeasureTheory

/-- An original pencil cap transfers to a retained state fraction with
exactly the reciprocal fraction loss. Neither state law is normalized. -/
theorem relative_cap_of_original_fraction {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : Set Ω) (p δ : ℝ) (hp : 0 ≤ p) (hδ : 0 < δ)
    (hdom : ν ≤ μ) (hfloor : ENNReal.ofReal δ * μ univ ≤ ν univ)
    (hcap : μ S ≤ ENNReal.ofReal p * μ univ) :
    ν S ≤ ENNReal.ofReal (p / δ) * ν univ := by
  have hcapR := ENNReal.toReal_mono (by finiteness) ((hdom S).trans hcap)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp] at hcapR
  have hfloorR := ENNReal.toReal_mono (measure_ne_top ν univ) hfloor
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le] at hfloorR
  have hscaled : (ν S).toReal * δ ≤ p * (ν univ).toReal := by
    calc
      _ ≤ (p * (μ univ).toReal) * δ := mul_le_mul_of_nonneg_right hcapR hδ.le
      _ = p * (δ * (μ univ).toReal) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfloorR hp
  have hreal : (ν S).toReal ≤ p * (ν univ).toReal / δ := (le_div_iff₀ hδ).mpr hscaled
  calc
    ν S = ENNReal.ofReal ((ν S).toReal) := (ENNReal.ofReal_toReal (measure_ne_top ν S)).symm
    _ ≤ ENNReal.ofReal (p * (ν univ).toReal / δ) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (p / δ) * ν univ := by
      rw [show p * (ν univ).toReal / δ = (p / δ) * (ν univ).toReal by ring,
        ENNReal.ofReal_mul (div_nonneg hp hδ.le), ENNReal.ofReal_toReal (measure_ne_top ν univ)]

/-- Uniform relative caps survive arbitrary finite mixtures of original
state laws. The mixture weights are already included in the measures. -/
theorem relative_cap_finset_sum {Ω Q : Type*} [MeasurableSpace Ω]
    (G : Finset Q) (ν : Q → Measure Ω) (S : Set Ω) (c : ENNReal)
    (hcap : ∀ q ∈ G, ν q S ≤ c * ν q univ) :
    (∑ q ∈ G, ν q) S ≤ c * (∑ q ∈ G, ν q) univ := by
  simp only [Measure.finsetSum_apply]
  calc
    _ ≤ ∑ q ∈ G, c * ν q univ := Finset.sum_le_sum hcap
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Relative state floors give the pair-success input for a whole cell
mixture, even after intercept-group restrictions and whole-state deletion. -/
theorem pair_mass_of_retained_state_mixture {Ω Q : Type*} [MeasurableSpace Ω]
    (G : Finset Q) (μ ν : Q → Measure Ω)
    [∀ q, IsFiniteMeasure (μ q)] [∀ q, IsFiniteMeasure (ν q)]
    (T : Set (Ω × Ω)) (hT : MeasurableSet T)
    (p δ : ℝ) (hp : 0 ≤ p) (hδ : 0 < δ) (hsmall : 2 * p ≤ δ)
    (hdom : ∀ q ∈ G, ν q ≤ μ q)
    (hfloor : ∀ q ∈ G, ν q = 0 ∨ ENNReal.ofReal δ * μ q univ ≤ ν q univ)
    (hcap : ∀ q ∈ G, ∀ x, μ q (Prod.mk x ⁻¹' T) ≤ ENNReal.ofReal p * μ q univ) :
    ENNReal.ofReal (((∑ q ∈ G, ν q) univ).toReal ^ 2 / 2) ≤
      ((∑ q ∈ G, ν q).prod (∑ q ∈ G, ν q)) Tᶜ := by
  have hmix (x : Ω) : (∑ q ∈ G, ν q) (Prod.mk x ⁻¹' T) ≤
      ENNReal.ofReal (p / δ) * (∑ q ∈ G, ν q) univ := by
    apply relative_cap_finset_sum
    intro q hq
    rcases hfloor q hq with hz | hf
    · simp [hz]
    · exact relative_cap_of_original_fraction (μ q) (ν q) _ p δ hp hδ
        (hdom q hq) hf (hcap q hq x)
  have hsmall' : 2 * (p / δ) ≤ 1 := by
    rw [show 2 * (p / δ) = (2 * p) / δ by ring]
    exact (div_le_one hδ).mpr hsmall
  exact pair_mass_of_original_cap_and_fraction _ _ T hT (p / δ) 1
    (div_nonneg hp hδ.le) (by norm_num) hsmall' le_rfl (by simp) hmix

end Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
