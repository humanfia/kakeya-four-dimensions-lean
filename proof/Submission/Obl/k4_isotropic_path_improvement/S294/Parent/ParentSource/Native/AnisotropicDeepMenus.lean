-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.AnisotropicDeepMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/AnisotropicDeepMenus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/AnisotropicDeepMenus.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DeepPhysicalMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PhysicalCodePruning
import Submission.Lib.K4SignalMeshSupport.Terminal

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

noncomputable section

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

/-- The same 108-code deep menu permits independent base and hidden
meshes. Only the base radius must resolve the finer base mesh. -/
theorem PathData.Valid.exists_deep_original_anisotropic_menu
    (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (old deep : Fin p.C) (hA : p.A deep ⊆ p.A old)
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (hsmall : p.deepBaseRadius Nk L δ₀ old deep ≤ baseMesh)
    (U : Set Ev) (hU : U ⊆ p.F deep)
    (hheight : ∀ q ∈ U, ∀ q' ∈ U,
      |packetSignal Nk p old q - packetSignal Nk p old q'| ≤ hidden) :
    ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card : ℝ) ≤ 108 ∧
      ∀ q ∈ U, p.originalPhysicalCode Nk old baseMesh hidden q ∈ Menu := by
  classical
  obtain ⟨Base, hBase, hbaseCover⟩ := hp.exists_deep_base_code_menu hN old deep hA hbase hsmall
  obtain ⟨G, hG, hcover⟩ := Submission.Lib.K4SignalMeshSupport.terminal_support_of_fiber_oscillation
    U (fun q => baseCode baseMesh (p.nativeBaseCoordinates old q)) (packetSignal Nk p old)
    Base hhidden (show (0 : ℝ) ≤ 1 by norm_num)
    (fun q hq => hbaseCover q (hU hq))
    (fun q hq q' hq' _ => by simpa only [one_mul] using hheight q hq q' hq')
  let pack : (Fin 3 → ℤ) × ℤ → Fin 4 → ℤ := fun k => Fin.snoc k.1 k.2
  refine ⟨G.image pack, ?_, ?_⟩
  · calc
      _ ≤ (G.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ ≤ (Base.card : ℝ) * (2 * 1 + 2) := hG
      _ = 108 := by rw [hBase]; norm_num
  · intro q hq
    exact Finset.mem_image.mpr
      ⟨(baseCode baseMesh (p.nativeBaseCoordinates old q), ⌊packetSignal Nk p old q / hidden⌋),
        hcover q hq, rfl⟩

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
