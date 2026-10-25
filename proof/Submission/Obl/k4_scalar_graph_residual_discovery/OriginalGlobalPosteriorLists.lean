/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalGlobalPosteriorLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.GlobalPosteriorRecords

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Lib.K4CommonLocalChoice

namespace ScalarData

/-- The original preparation certificate gives the actual globally indexed
posterior lists before a coefficient world is selected. The original fine
state and coarse velocity column are the base record throughout. -/
theorem prepData.original_global_posterior_lists {D : ScalarData}
    {H : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E₀) (hN : ∀ k, 2 ≤ D.N k) :
    ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ g : Fin (D.W k), ∀ a : ℝ,
      R⁻¹ ≤ a → a ≤ R → (∃ m : ℕ, a = (m : ℝ) / (D.prepMesh hprep k : ℝ)) →
      ∀ B : ℝ, a ≤ B → ∀ E' : Set ScalarIncidence, E' ⊆ E₀ k g →
      (∀ p ∈ E', (D.ρ k g).restrict (E₀ k g)
        {p' | D.phys k a p' = D.phys k a p ∧ D.coeff k a p'.1 = D.coeff k a p.1} ≠ 0) →
      ∀ {σ : Type*} (s : σ → ℝ), (∀ i, 0 < s i) →
      (∀ i, (1 + 3 * (H k + 1)) * D.N k ^ (-B) ≤ D.N k ^ (-a) * s i) →
      ∃ lists : σ → ((Fin 3 → ℤ) × ℤ) → Finset ((Fin 5 → ℤ) × (Fin 3 → ℤ)),
        (∀ i w, ((lists i w).card : ℝ) ≤ 512 * H k) ∧
        ∀ i p, p ∈ E' →
          (Zoom.posteriorEntryRecord (D.N k ^ (-a)) (D.N k ^ (-B)) (s i) p).1 ∈
            lists i (Zoom.posteriorEntryRecord (D.N k ^ (-a)) (D.N k ^ (-B)) (s i) p).2 := by
  classical
  obtain ⟨M, _, hmesh, hlists⟩ := hprep.original_posterior_entry_lists hN
  subst M
  intro R hR
  filter_upwards [hlists R hR] with k hk
  intro g a halo hahi hagrid B haB E' hEE hpositive σ s hs hsmall
  have hfound : ∀ (i : σ) (w : (Fin 3 → ℤ) × ℤ),
      ∃ L : Finset ((Fin 5 → ℤ) × (Fin 3 → ℤ)), (L.card : ℝ) ≤ 512 * H k ∧
        ∀ p ∈ E', D.phys k B p = w.1 → D.coeff k a p.1 1 = w.2 →
          (D.coeff k a p.1,
            cell (s i) (Zoom.position (D.N k ^ (-a)) (D.coeff k a p.1) p)) ∈ L := by
    intro i w
    exact hk g a halo hahi hagrid B haB (s i) (hs i) (hsmall i) E' hEE hpositive w.1 w.2
  choose lists hcard hmem using hfound
  refine ⟨lists, hcard, ?_⟩
  intro i p hp
  rw [Zoom.posteriorEntryRecord_eq (Real.rpow_pos_of_pos (by linarith [hN k]) _)]
  exact hmem i _ p hp rfl rfl

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
