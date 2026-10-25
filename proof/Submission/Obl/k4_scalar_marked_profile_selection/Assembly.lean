import Submission.Obl.k4_marked_scalar_grid_selection
import Submission.Obl.k4_scalar_grid_density_extension
import Submission.Obl.k4_scalar_profile_raw_certification
import Submission.Obl.k4_scalar_marked_profile_selection.Statements
import Submission.Obl.k4_scalar_marked_profile_selection.Atoms
import Submission.Obl.k4_scalar_marked_profile_selection.Pullback

noncomputable section

namespace Submission.Obl.k4_scalar_marked_profile_selection

open MeasureTheory Set Filter

theorem marked_profile_selection : selectionStatement := by
  have selectGrid : gridSelectionStatement := Submission.k4_marked_scalar_grid_selection
  have extendGrid : gridExtensionStatement := Submission.k4_scalar_grid_density_extension
  have certifyRaw : rawCertificationStatement := Submission.k4_scalar_profile_raw_certification
  intro N K hN₂ hN hK d s m C S U hd hd₁ hs hsm hC hS hU hUm
    c angular M H J b w mark hc htables hraw
  have hV : 0 < 4 * (m + s + 1) := by linarith
  obtain ⟨L, hL, hKL, mark₁, htable₁, hmark₁, hgrid⟩ :=
    selectGrid N K hN₂ hN hK s m (4 * (m + s + 1)) hs hsm hV M H J b w mark htables
  let μ : ℕ → Measure Incidence := fun k =>
    law (N k ^ (-m)) (H k) (J k) (b k) (w k) (mark k)
  let ν : ℕ → Measure Incidence := fun k =>
    law (N k ^ (-m)) (H k) (J k) (b k) (w k) (mark₁ k)
  have hmass : ∀ k, ENNReal.ofReal ((L k)⁻¹) ≤ ν k univ ∧ ν k univ ≤ 1 := by
    intro k
    have ht := htable₁ k
    refine ⟨ht.2.2.2.2.2.2.2.2, ?_⟩
    exact law_mass_le_one (Real.rpow_pos_of_pos (by linarith [hN₂ k]) _)
      (by omega) (b k) (w k) (mark₁ k) ht.2.2.2.2.2.1 ht.2.2.2.2.2.2.1
  obtain ⟨ψ, hψ, F, hregular, hhom⟩ :=
    extendGrid N L ν hN₂ hN hL s (4 * (m + s + 1)) hs hV hmass hgrid
  obtain ⟨φ, hφ, angular₀, C₀, hangular, hc₀, hnumeric⟩ :=
    certifyRaw (N ∘ ψ) (K ∘ ψ) (L ∘ ψ) (fun k => hN₂ (ψ k))
      (hN.comp hψ.tendsto_atTop) (subpower_comp hK hψ) (subpower_comp hL hψ)
      d s m C S U hd hd₁ hs hsm hC hS hU hUm (c ∘ ψ) (angular ∘ ψ)
      (μ ∘ ψ) (ν ∘ ψ) (fun k => hc (ψ k))
      (fun k => law_mono (hmark₁ (ψ k))) (fun k => (hmass (ψ k)).1)
      (fun k => hraw (ψ k)) F hhom
  refine ⟨ψ ∘ φ, hψ.comp hφ, L ∘ ψ ∘ φ,
    subpower_comp (subpower_comp hL hψ) hφ, fun k => hKL (ψ (φ k)),
    (fun k => mark₁ (ψ (φ k))), angular₀, hangular, C₀, F, ?_, hc₀,
    (fun k => htable₁ (ψ (φ k))), (fun k => hmark₁ (ψ (φ k))), ?_⟩
  · exact ⟨hregular.1, hregular.2, hnumeric⟩
  · exact homogeneous_comp hhom hφ

end Submission.Obl.k4_scalar_marked_profile_selection
