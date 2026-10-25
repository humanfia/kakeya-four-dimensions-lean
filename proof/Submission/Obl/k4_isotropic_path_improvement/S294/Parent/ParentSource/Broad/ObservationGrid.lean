-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.ObservationGrid, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/ObservationGrid.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/ObservationGrid.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.BaseLines

/-!
# The observation grid

An observation cell is a base cube of side `p` in the base coordinates `(t, y)` times a hidden
bin of the frozen observation `obs Bv a`, that is the bin `⌊Bv x₃ / a⌋`.  The cell of an
incidence is given by the index `cellIdx p Bv a`, a measurable map to a countable type, so cells
are the fibres of a measurable map and every set of cells is measurable.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad

open MeasureTheory Set

noncomputable section

/-- The base cube index of an incidence at mesh `p`. -/
def cubeIdx (p : ℝ) (q : Ev) : Fin 3 → ℤ := fun e => ⌊basePoint q e / p⌋

/-- The hidden bin of an incidence, as in the frozen observation `obs Bv a`. -/
def binIdx (Bv a : ℝ) (q : Ev) : ℤ := ⌊Bv * xp q.1 q.2 3 / a⌋

/-- The observation cell index. -/
def cellIdx (p Bv a : ℝ) (q : Ev) : (Fin 3 → ℤ) × ℤ := (cubeIdx p q, binIdx Bv a q)

lemma binIdx_eq_obs (Bv a : ℝ) (q : Ev) : binIdx Bv a q = (obs Bv a q).2 := by
  simp [binIdx, obs, xp, x]

lemma basePoint_apply_zero (q : Ev) : basePoint q 0 = q.2 := by simp [basePoint]

lemma basePoint_apply_one (q : Ev) : basePoint q 1 = xp q.1 q.2 1 := by simp [basePoint, xp]

lemma basePoint_apply_two (q : Ev) : basePoint q 2 = xp q.1 q.2 2 := by simp [basePoint, xp]

lemma measurable_basePoint_apply (e : Fin 3) : Measurable fun q : Ev => basePoint q e := by
  fin_cases e <;> simp [basePoint] <;> fun_prop

lemma measurable_cubeIdx (p : ℝ) : Measurable (cubeIdx p) := by
  rw [measurable_pi_iff]
  intro e
  exact Int.measurable_floor.comp ((measurable_basePoint_apply e).div_const p)

lemma measurable_binIdx (Bv a : ℝ) : Measurable (binIdx Bv a) := by
  unfold binIdx
  refine Int.measurable_floor.comp (Measurable.div_const (Measurable.const_mul ?_ Bv) a)
  simp only [xp]
  fun_prop

lemma measurable_cellIdx (p Bv a : ℝ) : Measurable (cellIdx p Bv a) :=
  (measurable_cubeIdx p).prodMk (measurable_binIdx Bv a)

/-- Two points with the same cube index have base coordinates within `p`. -/
lemma abs_basePoint_sub_lt_of_cubeIdx_eq {p : ℝ} (hp : 0 < p) {q q' : Ev}
    (h : cubeIdx p q = cubeIdx p q') (e : Fin 3) : |basePoint q e - basePoint q' e| < p := by
  have he : ⌊basePoint q e / p⌋ = ⌊basePoint q' e / p⌋ := congrFun h e
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor he
  rw [← sub_div, abs_div, abs_of_pos hp, div_lt_one hp] at h1
  exact h1

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad
