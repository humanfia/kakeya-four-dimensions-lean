import Submission.Obl.k4_profile_density_bounds.Support
import Submission.Obl.k4_profile_density_bounds.Profile

open MeasureTheory Set Filter
open scoped ENNReal

namespace Submission.Obl.k4_profile_density_bounds

lemma profile_endpoint_le {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (ν : ℕ → Measure Line) (E : ℕ → Set State)
    (hE : ∀ k, MeasurableSet (E k))
    (hvel : ∀ k, ∀ᵐ l ∂ν k, ‖velocity l‖ ≤ K k)
    (hmass : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ selected (ν k) (E k) univ)
    (hdens : ∀ k, ∃ G, Measurable G ∧
      (selected (ν k) (E k)).map (observe (N k) 1 0) = reference.withDensity G)
    {e σ C : ℝ} (hC : 0 ≤ C)
    (htyp : Typical N (fun k => selected (ν k) (E k)) (fun k => observe (N k) 1 0) e)
    (hcover : ∀ k, ∃ (m : ℕ) (z : Fin m → EuclideanSpace ℝ (Fin 4)),
      (m : ℝ) ≤ C * N k ^ (4 - σ) ∧
      ∀ p ∈ E k, ∃ j, ‖physical p - z j‖ ≤ C / N k) : e ≤ 1 - σ := by
  apply profile_le_of_support_bound hN hNt hK hsub
    (fun k => selected (ν k) (E k)) (fun k => observe (N k) 1 0)
    (fun k => measurable_observe _ _ _) hmass hdens (supportConstant_nonneg hC) 2 htyp
  intro k
  obtain ⟨m, z, hm, hz⟩ := hcover k
  have hkN : 0 < N k := by linarith [hN k]
  exact ⟨observationSupport z (N k) (K k) C,
    measurableSet_observationSupport z _ _ _,
    ae_mem_observationSupport z (ν k) (hE k) hkN (hK k) hC (hvel k) hz,
    reference_observationSupport_power_le z hkN (hK k) hC hm⟩

end Submission.Obl.k4_profile_density_bounds
