-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PreparedIncidenceParameterPalettes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PreparedIncidenceParameterPalettes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.IncidenceParameterPalettes

/-! # One original-law core with all parameter palettes

The roots of the coefficient zooms may vary with the query, so the same cut
prepares coarse-world menus (root 1) and finer menus (root rho) together.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

/-- Construct every tested parameter palette from actual current caps,
with one simultaneous original-prior entry deletion. -/
theorem prepare_incidence_parameter_palettes {Λ σ : Type*}
    [MeasurableSpace Λ] [Fintype σ]
    (μ : Measure (Λ × ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (ρ amplitude K C cut : σ → ℝ) (n : σ → ℕ)
    (hρ : ∀ i, 0 < ρ i) (hamp : ∀ i, 0 < amplitude i)
    (hK : ∀ i, 0 < K i) (hC : ∀ i, 0 ≤ C i) (hcut : ∀ i, 0 < cut i)
    (hfinite : ∀ i, ((fun z : Λ × ℝ =>
      parameterCode (ρ i*dyadicParameterWidth (n i)) (c z.1)) '' E).Finite)
    (π : σ → (Fin 2 → ℤ) → ENNReal) (hπtop : ∀ i v, π i v ≠ ∞)
    (hfloor : ∀ i z, z∈E →
      ENNReal.ofReal ((ρ i*dyadicParameterWidth (n i))^2*amplitude i/K i)*
        π i (parameterCode (ρ i*dyadicParameterWidth (n i)) (zv (c z.1))) ≤
      ν {l | parameterCode (ρ i*dyadicParameterWidth (n i)) (c l)=
        parameterCode (ρ i*dyadicParameterWidth (n i)) (c z.1)})
    (hcap : ∀ i world cell v,
      (μ.restrict E) {z | parameterCode (ρ i) (c z.1)=world ∧
        canonicalZoomCell c (ρ i) (dyadicParameterWidth (n i)) z=cell ∧
        parameterCode (ρ i*dyadicParameterWidth (n i)) (zv (c z.1))=v} ≤
      ENNReal.ofReal (C i*dyadicParameterWidth (n i)*
        (ρ i*dyadicParameterWidth (n i))^2*amplitude i)*π i v) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ i, ENNReal.ofReal (cut i*zoomBlockVisitConstant))*ν univ ∧
      ∃ palettes : σ → (((Fin 7 → ℤ) × (Fin 4 → ℤ)) × (Fin 2 → ℤ)) → Finset (Fin 7 → ℤ),
        (∀ i key, ((palettes i key).card : ℝ) ≤ C i*K i/cut i) ∧
        ∀ i z, z∈R → parameterCode (ρ i*dyadicParameterWidth (n i)) (c z.1) ∈
          palettes i ((parameterCode (ρ i) (c z.1),
            canonicalZoomCell c (ρ i) (dyadicParameterWidth (n i)) z),
            parameterCode (ρ i*dyadicParameterWidth (n i)) (zv (c z.1))) := by
  have hs1 (i) : dyadicParameterWidth (n i) ≤ 1 := by
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  obtain ⟨R,hR,hsub,hloss,hentry⟩ := prepare_original_parameter_cell_entries
    μ ν c hc E hE ht ρ (fun i => dyadicParameterWidth (n i)) cut hρ
    (fun i => dyadicParameterWidth_pos (n i)) hs1 (fun i => (hcut i).le)
    (fun i => original_zoom_blocks_finite_of_fine c E (hρ i) (n i) (hfinite i))
  have hex (i : σ) := parameter_cell_palettes_from_original_entries μ ν c hc E R hsub
    (hρ i) (dyadicParameterWidth_pos (n i)) (hamp i) (hK i) (hC i) (hcut i) (n i) rfl
    ((hfinite i).subset (Set.image_mono hsub)) (π i) (hπtop i)
    (fun z hz => hfloor i z (hsub hz)) (hentry i) (hcap i)
  choose palettes hcard hknown using hex
  exact ⟨R,hR,hsub,hloss,palettes,hcard,hknown⟩

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
