import Submission.Obl.k4_uncapped_native_capping.PacketCapBounds
import Submission.Obl.k4_scalar_initial_true_horizon.InitialAsymptotic

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Filter Set
noncomputable section

/-- The profile, mask and grid tolerances precede all later geometric
losses and are independent of the problem and its packet formats. -/
theorem exists_capping_parameters {χ S : ℝ} (hχ : 0 < χ) (hS : 0 < S) :
    ∃ ξ τ ε σ : ℝ, 0 < ξ ∧ 0 < τ ∧ 0 < ε ∧ 0 < σ ∧ σ ≤ χ / 48 ∧
      χ / 4 + 3 * τ + (1 + S) * ε + 2 * ξ ≤ χ := by
  refine ⟨χ / 64, χ / 64, χ / (64 * (1 + S)), χ / 96,
    by positivity, by positivity, by positivity, by positivity, by linarith, ?_⟩
  have heq : (1 + S) * (χ / (64 * (1 + S))) = χ / 64 := by
    field_simp
  rw [heq]
  linarith

/-- A single finite original-world density preparation gives all masks
needed through the fixed signal and angular depths. Its exceptional cost
is power-small before any packet family is chosen. -/
theorem finite_capping_preparation
    {p : UWE.Problem} {S η s U ε τ : ℝ} (hp : p.Valid S η) (hL : p.L = 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hU : 0 ≤ U) (hUη : U ≤ η)
    (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ R V : Finset ℝ,
      (∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L) ∧
      (∀ u ∈ V, 0 < u ∧ u ≤ η * p.L) ∧
      UWE.coarseDepthGrid s ε ⊆ R ∧
      (∀ u ∈ UWE.coarseDepthGrid U ε, 0 < u → u ∈ V) ∧
      (∀ k γ, MeasurableSet (UWE.densityPreparationBad p S R V τ k γ)) ∧
      Submission.Obl.k4_native_grid_profile_extension.Profiles.IsPowerSmall p.N
        (fun k => ∑ γ, ENNReal.ofReal (p.ω k γ) *
          p.incidenceMeasure k γ (UWE.densityPreparationBad p S R V τ k γ)) := by
  classical
  let R := UWE.coarseDepthGrid s ε
  let V := (UWE.coarseDepthGrid U ε).filter (fun u => 0 < u)
  have hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L := by
    intro r hr
    have h := UWE.coarseDepthGrid_bounds hs hε hr
    exact ⟨h.1, h.2.trans (hL ▸ hs1)⟩
  have hV : ∀ u ∈ V, 0 < u ∧ u ≤ η * p.L := by
    intro u hu
    have hh := Finset.mem_filter.mp hu
    refine ⟨hh.2, ?_⟩
    simpa only [hL, mul_one] using
      (UWE.coarseDepthGrid_bounds hU hε hh.1).2.trans hUη
  refine ⟨R, V, hR, hV, fun _ h => h, ?_, ?_, ?_⟩
  · intro u hu hu0
    exact Finset.mem_filter.mpr ⟨hu, hu0⟩
  · exact fun k γ => hp.measurableSet_densityPreparationBad R V hR hV τ k γ
  · exact hp.finite_density_preparation R V hR hV hτ

/-- The fixed numerical prefactor is absorbed eventually, independently
of packet count, format, frame, and time depth. -/
theorem eventually_capping_constant
    {p : UWE.Problem} {S η χ : ℝ} (hp : p.Valid S η) (hχ : 0 < χ) :
    ∀ᶠ k in atTop, 25600 ≤ p.N k ^ (χ / 8) := by
  exact Submission.Obl.k4_scalar_initial_true_horizon.eventually_const_le_rpow hp.2.1
    (by positivity) 25600

end
end Submission.Obl.k4_uncapped_native_capping
