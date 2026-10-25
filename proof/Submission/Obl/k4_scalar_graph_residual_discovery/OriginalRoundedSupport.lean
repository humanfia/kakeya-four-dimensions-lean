/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalRoundedSupport.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalPhysicalSupport
import Submission.Obl.k4_scalar_graph_residual_discovery.RoundedHereditary
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldStripSupport

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Lib.K4CommonLocalChoice

namespace ScalarData

/-- Literal preparation counts give the hereditary lists at the ACTUAL
relative zoom widths. Exact selected-grid rounding costs only H, keeping
the raw constant subpower before the second common choice. -/
theorem prepData.original_rounded_assigned_support {D : ScalarData}
    {H : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E₀) (hN : ∀ k, 2 ≤ D.N k)
    (hd : 0 ≤ D.d) (hd₁ : D.d ≤ 1) :
    ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ D.N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧
      M = D.prepMesh hprep ∧
      ∀ T : ℝ, 1 < T → ∀ᶠ k in atTop, ∀ g : Fin (D.W k), ∀ u v : ℝ,
        T⁻¹ ≤ u → u ≤ T → T⁻¹ ≤ v → v ≤ u →
        (∃ m : ℕ, u = (m : ℝ) / (M k : ℝ)) →
        (∃ m : ℕ, v = (m : ℝ) / (M k : ℝ)) →
        ∀ b : ℝ, 0 < b → b ≤ D.N k ^ (-u) → ∀ E' : Set ScalarIncidence,
        (∀ z ∈ E', (D.ρ k g).restrict (E₀ k g)
          {p | D.phys k u p = D.phys k u z ∧ D.phys k v p = D.phys k v z} ≠ 0) →
        ∀ ρ r R : ℝ, 0 < ρ → 0 < r → 0 < R →
        D.N k ^ (-u) ≤ ρ * r → ρ * r ≤ H k * D.N k ^ (-u) →
        D.N k ^ (-v) ≤ ρ * R → ρ * R ≤ H k * D.N k ^ (-v) →
        ∀ q : Fin 3 → ℤ, ∃ L : Finset (Fin 3 → ℤ),
          (L.card : ℝ) ≤ (13824 * H k ^ 7) * (R / r) ^ ((2 : ℝ) + D.d) ∧
          ∀ z ∈ E', cell (ρ * R) (assignedPosition b z) = q →
            cell (ρ * r) (assignedPosition b z) ∈ L := by
  obtain ⟨M, hM, hMeq, hraw⟩ := hprep.original_assigned_physical_support hN
  refine ⟨M, hM, hMeq, ?_⟩
  intro T hT
  filter_upwards [hraw T hT] with k hk
  intro g u v hulo huhi hvlo hvu humesh hvmesh b hb hbβ E' hpositive
    ρ r R hρ hr hR hβle hβge hδle hδge q
  have hN₀ : 0 < D.N k := by linarith [hN k]
  have hβ : 0 < D.N k ^ (-u) := Real.rpow_pos_of_pos hN₀ _
  have hδ : 0 < D.N k ^ (-v) := Real.rpow_pos_of_pos hN₀ _
  have hH : 1 ≤ H k := hprep.1.1 k
  have hpow : (D.N k ^ (-v) / D.N k ^ (-u)) ^ ((2 : ℝ) + D.d) =
      D.N k ^ ((2 + D.d) * (u - v)) := by
    rw [← Real.rpow_sub hN₀, ← Real.rpow_mul hN₀.le]
    congr 1
    ring
  choose F hFcard hFmem using hk g u v hulo huhi hvlo hvu humesh hvmesh b hb hbβ E' hpositive
  have hcard (q : Fin 3 → ℤ) : ((F q).card : ℝ) ≤
      64 * H k * (D.N k ^ (-v) / D.N k ^ (-u)) ^ ((2 : ℝ) + D.d) := by
    rw [hpow]
    exact (hFcard q).trans_eq (by ring)
  obtain ⟨L, hL, hmem⟩ := hereditary_list_at_rounded_widths (assignedPosition b) E'
    hβ hδ (mul_pos hρ hr) (mul_pos hρ hR) hβle (by linarith : 0 ≤ H k) hδge F hcard
      (fun z hz => hFmem _ z hz rfl) q
  refine ⟨L, hL.trans ?_, hmem⟩
  simpa only [mul_assoc] using rounded_assigned_hereditary_constant hH hβ hδ hρ hr hR hd hd₁ hδle hβge

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
