import Submission.Obl.k4_finite_row_graph_assembly.Planar

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/FiniteGraph.lean.
import Submission.Obl.k4_finite_row_graph_assembly.Witness

open MeasureTheory

namespace Submission.Obl.k4_finite_row_graph_assembly

/-- The finite construction keeps original measurable witnesses, independently of
any Fourier or planar rigidity statement. -/
noncomputable def finite_graph_construction {α : Type} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (z T : α × ℝ → Fin 2 → ℝ)
    {h E K R s L : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hK : 1 ≤ K) (hR : 2 ≤ R) (hKR : K ≤ R) (hs : 0 ≤ s) (hL : LossBounds K R s L)
    (f : FiniteIncidenceData h K R s) (cw : CellWitnessData μ z T h E K R s f)
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod volume)) :
    RowGraphWitness ν μ z T h E L s := by
  let c := f.selected hh (by linarith : 0 < K)
  have hRle : R ≤ L := by
    have hp : 1 ≤ R ^ 2 := one_le_pow₀ (by linarith : 1 ≤ R)
    have he : R * R ^ 2 = R ^ 3 := by ring
    have ht := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ R)
    nlinarith [hL.ratio]
  have hRpos : 0 < R := by linarith
  refine {
    planar := c.planar hh hh1 hK hR hKR hs hL
    v₁ := f.velocity c.first
    v₂ := f.velocity c.second
    velocity_bound₁ := (f.velocity_bound c.first c.first_mem).trans hL.base
    velocity_bound₂ := (f.velocity_bound c.second c.second_mem).trans hL.base
    velocity_separation := (one_div_le_one_div_of_le hRpos hRle).trans c.separation
    domination := hdom.trans ?_
    witness := c.edgeWitness cw
    measurable_witness := c.measurable_edgeWitness cw
    disjoint_witness := c.disjoint_edgeWitness cw
    witness_mass := ?_
    witness_bounds := ?_
    witness_projections := ?_ }
  · intro A
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hL.base)
      (zero_le : (0 : ENNReal) ≤ (ν.prod volume) A)
  · intro i e he
    exact c.edgeWitness_mass cw hh.le (by linarith) hL.witness_mass
      (c.index i) (c.index i).property e he
  · intro i e he p hp
    exact c.edgeWitness_bounds cw hL.base e p hp
  · intro i e he p hp
    exact c.edgeWitness_projections cw hh.le hL.witness_error e p hp

end Submission.Obl.k4_finite_row_graph_assembly
