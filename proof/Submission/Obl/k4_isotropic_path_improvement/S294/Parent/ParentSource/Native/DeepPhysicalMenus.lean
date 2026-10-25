-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.DeepPhysicalMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/DeepPhysicalMenus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/DeepPhysicalMenus.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/DeepPhysicalMenus.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DeepCoreMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.GraphCells
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeLines

/-! Whole deep histories resolve local core diameters and physical codes.
The height oscillation comes from the earlier original value-norming
entry; no new floor is imposed on its later deep-history intersection. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Analytic
open scoped BigOperators

noncomputable def PathData.deepBaseRadius {W : ℕ} (p : PathData W)
    (Nk L δ₀ : ℝ) (old deep : Fin p.C) : ℝ :=
  (1 + p.κ ^ 3 * Nk ^ (2 * δ₀ * L) + 2 * p.κ) *
    ((2 : ℝ) ^ p.T (p.lev old) / (2 : ℝ) ^ p.T (p.lev deep))

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.deep_original_core_diameter
    (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (fine deep : Fin p.C) (hA : p.A deep ⊆ p.A fine)
    {K : ℝ} (hK : 0 ≤ K) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) :
    ∀ q ∈ p.F deep, ∀ q' ∈ p.F deep,
      ‖packetLocalCorePoint Nk B p fine K R c q - packetLocalCorePoint Nk B p fine K R c q'‖ ≤
        6 * K ^ R * p.deepBaseRadius Nk L δ₀ fine deep := by
  obtain ⟨anchor, hanchor⟩ := hp.deep_original_native_cube_box hN fine deep hA
  have hbox : ∀ q ∈ p.F deep, ∀ j : Fin 3,
      |packetNativeCubePoint Nk B p fine q j.castSucc - anchor j| ≤
        p.deepBaseRadius Nk L δ₀ fine deep := by
    simpa only [PathData.deepBaseRadius] using hanchor
  have hKR : 0 ≤ K ^ R := pow_nonneg hK _
  have hcoord (q : Event) (j : Fin 3) : packetLocalCorePoint Nk B p fine K R c q j =
      K ^ R * (packetNativeCubePoint Nk B p fine q j.castSucc - c j) := by
    fin_cases j <;> rfl
  intro q hq q' hq'
  calc
    _ ≤ ∑ j : Fin 3, |(packetLocalCorePoint Nk B p fine K R c q -
        packetLocalCorePoint Nk B p fine K R c q') j| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _j : Fin 3, K ^ R * (2 * p.deepBaseRadius Nk L δ₀ fine deep) := by
      apply Finset.sum_le_sum
      intro j _
      have hraw : |packetNativeCubePoint Nk B p fine q j.castSucc -
          packetNativeCubePoint Nk B p fine q' j.castSucc| ≤
          2 * p.deepBaseRadius Nk L δ₀ fine deep := by
        calc
          _ ≤ |packetNativeCubePoint Nk B p fine q j.castSucc - anchor j| +
              |anchor j - packetNativeCubePoint Nk B p fine q' j.castSucc| := abs_sub_le _ _ _
          _ ≤ _ := by rw [abs_sub_comm (anchor j)]; linarith [hbox q hq j, hbox q' hq' j]
      change |packetLocalCorePoint Nk B p fine K R c q j -
        packetLocalCorePoint Nk B p fine K R c q' j| ≤ _
      rw [hcoord, hcoord, show K ^ R * (packetNativeCubePoint Nk B p fine q j.castSucc - c j) -
        K ^ R * (packetNativeCubePoint Nk B p fine q' j.castSucc - c j) =
        K ^ R * (packetNativeCubePoint Nk B p fine q j.castSucc -
          packetNativeCubePoint Nk B p fine q' j.castSucc) by ring,
        abs_mul, abs_of_nonneg hKR]
      exact mul_le_mul_of_nonneg_left hraw hKR
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Combining the actual27 base codes with old-signal oscillation of one
physical mesh gives at most108 four-dimensional physical codes. Apply
path_old_signal_deep_entry_oscillation using deep_original_core_diameter
for the height hypothesis. Empty later entries incur no loss or floor. -/
theorem PathData.Valid.exists_deep_original_physical_menu
    (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (old deep : Fin p.C) (hA : p.A deep ⊆ p.A old)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (hsmall : p.deepBaseRadius Nk L δ₀ old deep ≤ mesh)
    (U : Set Event) (hU : U ⊆ p.F deep)
    (hheight : ∀ q ∈ U, ∀ q' ∈ U,
      |MvPolynomial.eval (xp q.1 q.2) (p.R old) / δ Nk (p.r (p.lev old)) -
        MvPolynomial.eval (xp q'.1 q'.2) (p.R old) / δ Nk (p.r (p.lev old))| ≤ mesh) :
    ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card : ℝ) ≤ 108 ∧
      ∀ q ∈ U, PhysicalGraphCells.pointCode mesh (p.nativeBaseCoordinates old q)
        (MvPolynomial.eval (xp q.1 q.2) (p.R old) / δ Nk (p.r (p.lev old))) ∈ Menu := by
  obtain ⟨Base, hBase, hbase⟩ := hp.exists_deep_base_code_menu hN old deep hA hmesh hsmall
  obtain ⟨Menu, hcard, hcover⟩ := PhysicalGraphCells.graph_cells_over_base_cover
    (p.nativeBaseCoordinates old)
    (fun q => MvPolynomial.eval (xp q.1 q.2) (p.R old) / δ Nk (p.r (p.lev old)))
    U (show (0 : ℝ) ≤ 1 by norm_num) hmesh Base
    (fun q hq => hbase q (hU hq))
    (fun q hq q' hq' _ => by simpa only [one_mul] using hheight q hq q' hq')
  refine ⟨Menu, hcard.trans ?_, hcover⟩
  rw [hBase]
  norm_num

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
