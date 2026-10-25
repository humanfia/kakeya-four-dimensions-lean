-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.IncidenceCoarseParameterPalettes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/IncidenceCoarseParameterPalettes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetCoefficientMenus

/-! # Turn unit-world cell palettes into original-state world palettes

The bounded union construction adapts this LOT tree, o287, x1035,
Qualification/CoarseParameterPalettes.lean at a8628df2. Here its local palettes
are arbitrary actual palettes, in particular those constructed from current
incidence entries. No full-prior snapshot ceiling is required.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set
noncomputable section

/-- Construct the original-state coarse menus from the actual local
unit-world palettes. Both intervening geometric menus are constructed. -/
theorem original_state_parameter_palettes_from_unit_cells {Λ : Type*}
    (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    {b ρ H P : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hρ : 0 < ρ)
    (hH : 0 ≤ H) (hP : 0 ≤ P)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (hjets : ∀ z∈E, |c z.1 1|≤H ∧ |c z.1 2|≤H ∧ |c z.1 4|≤H ∧ |c z.1 6|≤H)
    (hsmall : (2+3*(H+1))*b ≤ ρ)
    (palettes : (((Fin 7 → ℤ) × (Fin 4 → ℤ)) × (Fin 2 → ℤ)) → Finset (Fin 7 → ℤ))
    (hpalettes : ∀ key, ((palettes key).card : ℝ) ≤ P)
    (hknown : ∀ z∈E, parameterCode ρ (c z.1) ∈
      palettes ((parameterCode 1 (c z.1),canonicalZoomCell c 1 ρ z),
        parameterCode ρ (zv (c z.1)))) :
    ∃ blocks : ((Fin 4 → ℤ) × (Fin 2 → ℤ)) → Finset (Fin 7 → ℤ),
      (∀ key, ((blocks key).card : ℝ) ≤ 256*(12*H+4)^7*P) ∧
      ∀ z∈E, parameterCode ρ (c z.1) ∈
        blocks (originalFineState c b z,parameterCode ρ (zv (c z.1))) := by
  classical
  obtain ⟨worlds,hworlds,hworldKnown⟩ := exists_unit_coefficient_world_menus E c hb hb1 hH ht hjets
  obtain ⟨cells,hcells,hcellKnown⟩ := exists_coefficient_world_cell_menus E c
    (b := b) (ρ := 1) (s := ρ) hb zero_lt_one le_rfl hρ hH hjets ht
    (by simpa only [one_mul] using hsmall)
  let blocks := fun key : (Fin 4 → ℤ) × (Fin 2 → ℤ) =>
    (worlds key.1).biUnion fun world =>
      (cells (key.1,world)).biUnion fun cell => palettes ((world,cell),key.2)
  refine ⟨blocks,?_,?_⟩
  · intro key
    have hlocal (world : Fin 7 → ℤ) :
        (((cells (key.1,world)).biUnion fun cell => palettes ((world,cell),key.2)).card : ℝ) ≤
          256*P := by
      calc
        _ ≤ ∑ cell∈cells (key.1,world), ((palettes ((world,cell),key.2)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _cell∈cells (key.1,world), P := Finset.sum_le_sum (fun cell _ => hpalettes _)
        _ = ((cells (key.1,world)).card : ℝ)*P := by simp
        _ ≤ 256*P := mul_le_mul_of_nonneg_right (by exact_mod_cast hcells _) hP
    calc
      ((blocks key).card : ℝ) ≤ ∑ world∈worlds key.1,
          (((cells (key.1,world)).biUnion fun cell => palettes ((world,cell),key.2)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _world∈worlds key.1, 256*P := Finset.sum_le_sum (fun world _ => hlocal world)
      _ = ((worlds key.1).card : ℝ)*(256*P) := by simp
      _ ≤ (12*H+4)^7*(256*P) := mul_le_mul_of_nonneg_right (hworlds _) (by positivity)
      _ = 256*(12*H+4)^7*P := by ring
  · intro z hz
    have heq : ParentSource.Broad.Source.CoefficientWorld.coeff c 1
        (Submission.Lib.K4CommonLocalChoice.cell 1 (c z.1)) z.1=
          canonicalZoomCoefficients c 1 z.1 := by
      funext i
      change (c z.1 i-(⌊c z.1 i/1⌋ : ℝ)*1)/1=
        (c z.1 i-1*(⌊c z.1 i/1⌋ : ℝ))/1
      ring
    have hcell : canonicalZoomCell c 1 ρ z∈cells (originalFineState c b z,parameterCode 1 (c z.1)) := by
      have hh := hcellKnown z hz
      rw [heq] at hh
      exact hh
    exact Finset.mem_biUnion.mpr ⟨_,hworldKnown z hz,
      Finset.mem_biUnion.mpr ⟨_,hcell,hknown z hz⟩⟩

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
