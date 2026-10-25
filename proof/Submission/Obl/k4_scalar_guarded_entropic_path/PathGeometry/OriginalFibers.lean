/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/OriginalFibers.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathSupport
import Submission.Obl.k4_original_prior_line_extraction.FiniteDensities

/-! A tagged original submeasure has within-world laws under the unchanged
original mixture weights. Zero-weight worlds are handled without a positivity
assumption, and the aggregate original mass is preserved exactly. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

abbrev worldFiber {n : ℕ} (ρ : Measure (Fin n × State)) (g : Fin n) : Measure State :=
  Submission.Obl.k4_original_prior_line_extraction.component ρ g

theorem worldFiber_apply {n : ℕ} (ρ : Measure (Fin n × State)) (g : Fin n)
    {S : Set State} (hS : MeasurableSet S) :
    worldFiber ρ g S = ρ ({g} ×ˢ S) :=
  Submission.Obl.k4_original_prior_line_extraction.component_apply ρ g hS

theorem worldFiber_mono {n : ℕ} {ρ σ : Measure (Fin n × State)} (hρ : ρ ≤ σ) (g : Fin n) :
    worldFiber ρ g ≤ worldFiber σ g := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [worldFiber_apply _ _ hS, worldFiber_apply _ _ hS]
  exact hρ _

theorem worldFiber_worldMixture (p : Code) (k : ℕ) (g : Fin (W p k)) :
    worldFiber (worldMixture p k) g = ENNReal.ofReal (ω p k g) • mu p k g := by
  classical
  ext S hS
  rw [worldFiber_apply _ _ hS, worldMixture, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single g]
  · rw [Measure.map_apply measurable_prodMk_left ((measurableSet_singleton g).prod hS)]
    simp
  · intro j _ hj
    rw [Measure.map_apply measurable_prodMk_left ((measurableSet_singleton g).prod hS)]
    simp [hj]
  · simp

theorem sum_worldFiber_mass {n : ℕ} (ρ : Measure (Fin n × State)) :
    ∑ g, worldFiber ρ g univ = ρ univ :=
  (Submission.Obl.k4_original_prior_line_extraction.measure_univ_eq_sum_components ρ).symm

def originalFibers (p : Code) (k : ℕ) (ρ : Measure (Fin (W p k) × State))
    (g : Fin (W p k)) : Measure State :=
  (ENNReal.ofReal (ω p k g))⁻¹ • worldFiber ρ g

theorem worldFiber_eq_zero_of_weight_zero {p : Code} {k : ℕ}
    {ρ : Measure (Fin (W p k) × State)} (hρ : ρ ≤ worldMixture p k)
    (g : Fin (W p k)) (hg : ENNReal.ofReal (ω p k g) = 0) : worldFiber ρ g = 0 := by
  have hf := worldFiber_mono hρ g
  rw [worldFiber_worldMixture, hg, zero_smul] at hf
  exact le_antisymm hf bot_le

theorem originalFibers_le {p : Code} {k : ℕ}
    {ρ : Measure (Fin (W p k) × State)} (hρ : ρ ≤ worldMixture p k) (g : Fin (W p k)) :
    originalFibers p k ρ g ≤ mu p k g := by
  by_cases hg : ENNReal.ofReal (ω p k g) = 0
  · rw [originalFibers, worldFiber_eq_zero_of_weight_zero hρ g hg, smul_zero]
    exact bot_le
  · have hf := worldFiber_mono hρ g
    rw [worldFiber_worldMixture] at hf
    calc
      _ ≤ (ENNReal.ofReal (ω p k g))⁻¹ •
          (ENNReal.ofReal (ω p k g) • mu p k g) := by
        apply Measure.le_iff.mpr
        intro S _
        simp only [originalFibers, Measure.smul_apply, smul_eq_mul]
        exact mul_le_mul' le_rfl (hf S)
      _ = _ := by rw [smul_smul, ENNReal.inv_mul_cancel hg ENNReal.ofReal_ne_top, one_smul]

theorem weighted_originalFibers {p : Code} {k : ℕ}
    {ρ : Measure (Fin (W p k) × State)} (hρ : ρ ≤ worldMixture p k) (g : Fin (W p k)) :
    ENNReal.ofReal (ω p k g) • originalFibers p k ρ g = worldFiber ρ g := by
  by_cases hg : ENNReal.ofReal (ω p k g) = 0
  · rw [hg, zero_smul, worldFiber_eq_zero_of_weight_zero hρ g hg]
  · rw [originalFibers, smul_smul,
      ENNReal.mul_inv_cancel hg ENNReal.ofReal_ne_top, one_smul]

/-- Restore the original world's weights only once. These within-world
laws are original incidence submeasures, with exactly the common path mass. -/
theorem originalFibers_mass {p : Code} {k : ℕ}
    {ρ : Measure (Fin (W p k) × State)} (hρ : ρ ≤ worldMixture p k) :
    ∑ g, ENNReal.ofReal (ω p k g) * originalFibers p k ρ g univ = ρ univ := by
  have hf (g : Fin (W p k)) := congrArg (fun μ : Measure State => μ univ)
    (weighted_originalFibers hρ g)
  simp only [Measure.smul_apply, smul_eq_mul] at hf
  simp_rw [hf]
  exact sum_worldFiber_mass ρ

/-- All original events, not only the total mass, are recovered with the
original weights. The accepted finite-component decomposition is reused. -/
theorem reconstruct_originalFibers {p : Code} {k : ℕ}
    {ρ : Measure (Fin (W p k) × State)} (hρ : ρ ≤ worldMixture p k) :
    (∑ g, ENNReal.ofReal (ω p k g) • (originalFibers p k ρ g).map (Prod.mk g)) = ρ := by
  ext S hS
  rw [Measure.finsetSum_apply]
  calc
    _ = ∑ g, worldFiber ρ g ((Prod.mk g) ⁻¹' S) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [← Measure.map_smul _ measurable_prodMk_left.aemeasurable,
        weighted_originalFibers hρ g, Measure.map_apply measurable_prodMk_left hS]
    _ = ρ S :=
      (Submission.Obl.k4_original_prior_line_extraction.measure_eq_sum_components ρ hS).symm

namespace RefinementChain

def originalWorldLaw {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    (g : Fin (W p (chain.sample k))) : Measure State :=
  originalFibers p (chain.sample k) (chain.originalLaw k) g

theorem originalWorldLaw_le {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    (g : Fin (W p (chain.sample k))) :
    chain.originalWorldLaw k g ≤ mu p (chain.sample k) g :=
  originalFibers_le (chain.originalLaw_le k) g

theorem originalWorldLaw_mass {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    ∑ g, ENNReal.ofReal (ω p (chain.sample k) g) * chain.originalWorldLaw k g univ =
      chain.originalLaw k univ :=
  originalFibers_mass (chain.originalLaw_le k)

theorem originalWorldLaw_mass_subpower {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, ENNReal.ofReal (N z k ^ (-ε)) ≤
      ∑ g, ENNReal.ofReal (ω p (chain.sample k) g) * chain.originalWorldLaw k g univ := by
  simp_rw [chain.originalWorldLaw_mass]
  exact chain.originalLaw_mass_subpower hz ε hε

end RefinementChain

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
