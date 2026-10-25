-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CanonicalResidualTables, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/CanonicalResidualTables.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/CanonicalResidualTables.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/CanonicalResidualTables.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomEntryFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ZoomResidualPalettes
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WorldResidualSelection


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Glue the genuine time-only rows of countably many original worlds.
The value at an incidence is its own world's row at its unchanged time. -/
theorem measurable_original_world_time_row {Λ W : Type*}
    [MeasurableSpace Λ] [MeasurableSpace W] [MeasurableSingletonClass W] [Countable W]
    (world : Λ → W) (hw : Measurable world) (F : W → ℝ → Fin 2 → ℝ)
    (hF : ∀ w, Measurable (F w)) : Measurable (fun z : Λ × ℝ => F (world z.1) z.2) := by
  intro S hS
  have heq : (fun z : Λ × ℝ => F (world z.1) z.2) ⁻¹' S =
      ⋃ w : W, ((fun z : Λ × ℝ => world z.1) ⁻¹' {w}) ∩ (Prod.snd ⁻¹' ((F w) ⁻¹' S)) := by
    ext z
    simp only [mem_preimage,mem_iUnion,mem_inter_iff,mem_singleton_iff]
    constructor
    · intro hz; exact ⟨world z.1,rfl,hz⟩
    · rintro ⟨w,hwz,hz⟩
      simpa only [hwz] using hz
  rw [heq]
  exact MeasurableSet.iUnion fun w =>
    (((hw.comp measurable_fst) (measurableSet_singleton w)).inter ((hF w hS).preimage measurable_snd))

/-- Construct the entire fine-velocity-conditioned residual table in
EVERY canonical original parameter zoom. The fine blocks are literal old
width-rho*s coefficient bins. Each has zoomed coefficient diameter s,
even though its original corner is shifted by the world subtraction. -/
theorem canonical_residual_tables_of_original_parameter_palettes {Λ V : Type*}
    [DecidableEq (Fin 7 → ℤ)]
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ)
    (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ) (velocity : Λ → V)
    (ρ s K blocks : ℝ) (hρ : 0 < ρ) (hs : 0 < s) (hρs : ρ ≤ s) (hK : 1 ≤ K)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (hF : ∀ z∈E, ‖F (parameterCode ρ (c z.1)) z.2‖ ≤ K)
    (hrow : ∀ z∈E, ∀ z'∈E, parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
      ‖F (parameterCode ρ (c z.1)) z.2-F (parameterCode ρ (c z'.1)) z'.2‖ ≤
        K*(|z.2-z'.2|+ρ))
    (palette : (((Fin 7 → ℤ) × (Fin 4 → ℤ)) × V) → Finset (Fin 7 → ℤ))
    (hcard : ∀ q, ((palette q).card : ℝ) ≤ blocks)
    (hknown : ∀ z∈E, parameterCode (ρ*s) (c z.1) ∈
      palette ((parameterCode ρ (c z.1),canonicalZoomCell c ρ s z),velocity z.1)) :
    ∃ table : (((Fin 7 → ℤ) × (Fin 4 → ℤ)) × V) → Finset ℤ,
      (∀ q, ((table q).card : ℝ) ≤ blocks*(22*K^2+5)) ∧
      ∀ z∈E, ⌊originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1)
        (fun y => F (parameterCode ρ (c y.1)) y.2) Prod.snd z / s⌋ ∈
          table ((parameterCode ρ (c z.1),canonicalZoomCell c ρ s z),velocity z.1) := by
  classical
  let world := fun l => parameterCode ρ (c l)
  let Ew := fun w : Fin 7 → ℤ => {z∈E | world z.1=w}
  let cw := fun w l => zoomCoefficients ρ (parameterCenter ρ w) (c l)
  have hex (w : Fin 7 → ℤ) := exists_velocity_conditioned_residual_lists (Ew w) (cw w) (F w)
    (fun l => parameterCode (ρ*s) (c l)) velocity s ρ K blocks hs hρs hK
    (fun z hz => ht z hz.1)
    (by
      intro z hz j
      have hh := original_parameter_zoom_coefficients_bound ρ hρ (c z.1) j
      have heq : world z.1=w := hz.2
      simpa only [canonicalZoomCoefficients,world,heq] using hh.trans hK)
    (by
      intro z hz
      have hh := hF z hz.1
      simpa only [show parameterCode ρ (c z.1)=w from hz.2] using hh)
    (by
      intro z hz z' hz' hb j
      have hh := zoom_piece_diameter ρ s hρ hs (parameterCenter ρ w) (c z.1) (c z'.1)
        (fun i => congrFun hb i)
      exact (norm_le_pi_norm (cw w z.1-cw w z'.1) j).trans hh)
    (by
      intro z hz z' hz'
      have hh := hrow z hz.1 z' hz'.1 (hz.2.trans hz'.2.symm)
      simpa only [show parameterCode ρ (c z.1)=w from hz.2,
        show parameterCode ρ (c z'.1)=w from hz'.2] using hh)
    (fun q => palette ((w,q.1),q.2))
    (fun q => hcard ((w,q.1),q.2))
    (by
      intro z hz
      have hh := hknown z hz.1
      have heq : parameterCode ρ (c z.1)=w := hz.2
      simpa only [heq,canonicalZoomCell,canonicalZoomCoefficients,cw] using hh)
  choose tables hsize hmem using hex
  refine ⟨fun q => tables q.1.1 (q.1.2,q.2),fun q => hsize _ _,?_⟩
  intro z hz
  have hh := hmem (world z.1) z ⟨hz,rfl⟩
  simpa only [world,cw,canonicalZoomCell,canonicalZoomCoefficients,originalResidualValue,zR] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
