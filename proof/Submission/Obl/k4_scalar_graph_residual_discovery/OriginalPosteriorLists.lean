/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalPosteriorLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalParameterLists
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomStateLists

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Lib.K4CommonLocalChoice

namespace ScalarData

/-- The literal frozen coefficient-world count, together with the actual
zoom-cell labels, supplies the finite lists for the global OLD product
reference-weight budget. -/
theorem prepData.original_posterior_entry_lists {D : ScalarData}
    {H : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E₀) (hN : ∀ k, 2 ≤ D.N k) :
    ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ D.N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧
      M = D.prepMesh hprep ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ g : Fin (D.W k), ∀ r : ℝ,
        R⁻¹ ≤ r → r ≤ R → (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) →
        ∀ B : ℝ, r ≤ B → ∀ s : ℝ, 0 < s →
        (1 + 3 * (H k + 1)) * D.N k ^ (-B) ≤ D.N k ^ (-r) * s →
        ∀ E' : Set ScalarIncidence, E' ⊆ E₀ k g →
        (∀ z ∈ E', (D.ρ k g).restrict (E₀ k g)
          {p | D.phys k r p = D.phys k r z ∧ D.coeff k r p.1 = D.coeff k r z.1} ≠ 0) →
        ∀ (w : Fin 3 → ℤ) (c : ℤ), ∃ L : Finset ((Fin 5 → ℤ) × (Fin 3 → ℤ)),
          (L.card : ℝ) ≤ 512 * H k ∧
          ∀ z ∈ E', D.phys k B z = w → D.coeff k r z.1 1 = c →
            (D.coeff k r z.1, cell s (Zoom.position (D.N k ^ (-r)) (D.coeff k r z.1) z)) ∈ L := by
  obtain ⟨M, hM, hmesh, hlists⟩ := hprep.original_fine_state_parameter_lists hN
  refine ⟨M, hM, hmesh, ?_⟩
  have hpoints := (Classical.choose_spec hprep.2).2 2 (by norm_num)
  intro R hR
  filter_upwards [hlists R hR, hpoints] with k hk hp
  intro g r hrlo hrhi hrgrid B hrB s hs hsmall E' hEE hpositive w c
  obtain ⟨_, _, _, hbound, _, _, _, _, _⟩ := hp.2 g
  obtain ⟨Q, hQcard, hQmem⟩ := hk g r hrlo hrhi hrgrid B hrB E' hpositive w c
  let S : Set ScalarIncidence :=
    {p | p ∈ E' ∧ D.phys k B p = w ∧ D.coeff k r p.1 1 = c}
  have hN₀ : 0 < D.N k := by linarith [hN k]
  have hr₀ : 0 < r := (inv_pos.mpr (by linarith : 0 < R)).trans_le hrlo
  have hρ₁ : D.N k ^ (-r) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hN k]) (by linarith)
  obtain ⟨L, hLcard, hLmem⟩ := Zoom.posterior_entry_list
    (Real.rpow_pos_of_pos hN₀ _) hρ₁ (Real.rpow_pos_of_pos hN₀ _) hs
    (hprep.1.1 k) hsmall w S
    (fun p hp => (hbound p (hEE hp.1)).1)
    (fun p hp => (hbound p (hEE hp.1)).2)
    (fun p hp => hp.2.1) Q hQcard
    (fun p hp => hQmem p hp.1 hp.2.1 hp.2.2)
  refine ⟨L, hLcard.trans_eq (by ring), ?_⟩
  intro z hz hw hc
  exact hLmem z ⟨hz, hw, hc⟩

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
