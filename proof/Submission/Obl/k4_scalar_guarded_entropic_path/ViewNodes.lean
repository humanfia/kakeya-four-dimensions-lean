import Submission.Obl.k4_scalar_guarded_entropic_path.GridRounding
import Submission.Obl.k4_scalar_guarded_entropic_path.StageLayout
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ViewGrid

/-! An actual candidate parent has a node map at every requested tangent
depth, on the same dense grid used for the original true layers. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalView

open Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {root final : Code} {D S₀ η₀ : ℝ} {stage : ℕ} {R δ κ η : ℝ}

/-- The original grid of every candidate gives an actual finite selector
throughout the requested compact tangent range. -/
theorem exists_layout_node (a : OriginalView root final D S₀ η₀)
    (q : StageLayout stage R δ κ η) (hR : 1 < R) (hcount : q.C ≤ a.count)
    {error : ℝ} (herror : 0 ≤ error)
    (hgrid : PathNodes.TrueGridPath.GridControl a κ (q.scale * q.mesh) 1 error) :
    ∃ node : ℝ → Fin a.count, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R →
      |a.depth (node s) / q.scale - s| ≤ q.mesh + 3 * error / q.scale := by
  classical
  have hC : 0 < q.C := by have := q.coarse_lt; omega
  have hn : 0 < a.count := hC.trans_le hcount
  let n := a.count - 1
  have hsucc : n + 1 = a.count := by dsimp [n]; omega
  let depth : Fin (n + 1) → ℝ := fun j => a.depth (Fin.cast hsucc j)
  have hd : ∀ j : Fin (n + 1),
      |depth j - ((j.val : ℝ) + 1) * (q.scale * q.mesh)| ≤ error := by
    intro j
    simpa only [depth, Fin.val_cast, mul_one] using (hgrid (Fin.cast hsucc j)).1
  obtain ⟨node, hnode⟩ := exists_node_near_grid (mul_pos q.scale_pos q.mesh_pos)
    herror q.scale_pos depth hd
  refine ⟨fun s => Fin.cast hsucc (node s), ?_⟩
  intro s hs₁ hs₂
  have hR0 : 0 < R := by linarith
  have hmesh : q.mesh ≤ s := by
    have hRinv : 0 < R⁻¹ := inv_pos.mpr hR0
    linarith [q.mesh_range]
  have hupper : s ≤ ((n : ℝ) + 1) * q.mesh := by
    have hcountR : (q.C : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (hcount.trans_eq hsucc.symm)
    have hm := mul_le_mul_of_nonneg_right hcountR q.mesh_pos.le
    linarith [q.covers_range]
  have hlow : q.scale * q.mesh ≤ q.scale * s :=
    mul_le_mul_of_nonneg_left hmesh q.scale_pos.le
  have hhigh : q.scale * s ≤ ((n : ℝ) + 1) * (q.scale * q.mesh) := by
    have h := mul_le_mul_of_nonneg_left hupper q.scale_pos.le
    nlinarith only [h]
  have h := hnode s hlow hhigh
  change |depth (node s) / q.scale - s| ≤ _
  convert h using 1
  field_simp [q.scale_pos.ne']

/-- A small outer grid error gives the original raw-stage power budget
for the SAME node selector, at any tangent resolution at least one. -/
theorem exists_layout_node_power_bound (a : OriginalView root final D S₀ η₀)
    (q : StageLayout stage R δ κ η) (hR : 1 < R) (hcount : q.C ≤ a.count)
    {error N : ℝ} (herror : 0 ≤ error) (hsmall : error ≤ q.scale * δ / 100)
    (hgrid : PathNodes.TrueGridPath.GridControl a κ (q.scale * q.mesh) 1 error)
    (hN : 1 ≤ N) :
    ∃ node : ℝ → Fin a.count, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R →
      N ^ |a.depth (node s) / q.scale - s| ≤ N ^ δ := by
  obtain ⟨node, hn⟩ := a.exists_layout_node q hR hcount herror hgrid
  refine ⟨node, ?_⟩
  intro s hs₁ hs₂
  apply Real.rpow_le_rpow_of_exponent_le hN
  apply (hn s hs₁ hs₂).trans
  have hδ : 0 < δ := by linarith [q.mesh_pos, q.mesh_error]
  have he : error / q.scale ≤ δ / 100 := by
    apply (div_le_iff₀ q.scale_pos).mpr
    nlinarith [hsmall]
  rw [mul_div_assoc]
  linarith only [he, q.mesh_error, hδ]

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalView
