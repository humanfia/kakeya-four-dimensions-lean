import Submission.Obl.k4_finite_row_graph_assembly.Selected

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/Witness.lean.

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Submission.Obl.k4_finite_row_graph_assembly

theorem mesh_linear_error {h a b A B u : ℝ} (hh : 0 ≤ h)
    (ha : |a - h * A| ≤ h) (hb : |b - h * B| ≤ h) :
    |a + u * b - h * (⌊A + u * B⌋ : ℝ)| ≤ (2 + |u|) * h := by
  have he : |h * ((A + u * B) - (⌊A + u * B⌋ : ℝ))| ≤ h := by
    rw [abs_mul, abs_of_nonneg hh]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (show |(A + u * B) - (⌊A + u * B⌋ : ℝ)| ≤ 1 by
        simpa only [abs_sub_comm] using floor_abs_error (A + u * B)) hh
  calc
    _ = |(a - h * A) + u * (b - h * B) +
        h * ((A + u * B) - (⌊A + u * B⌋ : ℝ))| := by congr 1; ring
    _ ≤ |a - h * A| + |u * (b - h * B)| +
        |h * ((A + u * B) - (⌊A + u * B⌋ : ℝ))| := abs_add_three _ _ _
    _ ≤ h + |u| * h + h := by
      rw [abs_mul u (b - h * B)]
      exact add_le_add (add_le_add ha
        (mul_le_mul_of_nonneg_left hb (abs_nonneg u))) he
    _ = _ := by ring

namespace SelectedCells

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {z T : X → Fin 2 → ℝ}
  {h E K R s : ℝ} {f : FiniteIncidenceData h K R s}
  (c : SelectedCells f) (cw : CellWitnessData μ z T h E K R s f)

noncomputable def edgeWitness (e : RealEdge) : Set X :=
  ⋃ p ∈ f.points.filter (fun p => c.edgeMap p = e), cw.cell p

theorem mem_edgeWitness {e : RealEdge} {x : X} : x ∈ c.edgeWitness cw e ↔
    ∃ p ∈ f.points, c.edgeMap p = e ∧ x ∈ cw.cell p := by
  simp only [edgeWitness, mem_iUnion, Finset.mem_filter]
  aesop

theorem measurable_edgeWitness (e : RealEdge) : MeasurableSet (c.edgeWitness cw e) :=
  Finset.measurableSet_biUnion _ (fun p _ => cw.measurable_cell p)

theorem disjoint_edgeWitness : Pairwise (fun e g =>
    Disjoint (c.edgeWitness cw e) (c.edgeWitness cw g)) := by
  intro e g heg
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨p, hp, hpe, hxp⟩ := (c.mem_edgeWitness cw).mp hx
  obtain ⟨q, hq, hqg, hxq⟩ := (c.mem_edgeWitness cw).mp hy
  have hpq : p ≠ q := by
    intro heq
    subst q
    exact heg (hpe.symm.trans hqg)
  exact (Set.disjoint_left.mp (cw.disjoint_cell hpq)) hxp hxq

theorem edgeWitness_mass {L : ℝ} (hh : 0 ≤ h) (hK : 0 < K)
    (hKL : 8 * K ^ 5 ≤ L) (d : ℤ) (hd : d ∈ c.directions)
    (e : RealEdge) (he : e ∈ c.graph d) :
    ENNReal.ofReal (h ^ 2 / L) ≤ μ (c.edgeWitness cw e) := by
  obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp he
  calc
    _ ≤ ENNReal.ofReal (h ^ 2 / (8 * K ^ 5)) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (sq_nonneg h) (by positivity) hKL)
    _ ≤ ENNReal.ofReal (∑ d ∈ f.directions, f.mass p d) :=
      ENNReal.ofReal_le_ofReal (c.marginal_floor d hd p hp)
    _ ≤ μ (cw.cell p) := cw.cell_mass p (c.cells_subset d hd hp)
    _ ≤ μ (c.edgeWitness cw e) := measure_mono (fun x hx =>
      (c.mem_edgeWitness cw).mpr ⟨p, c.cells_subset d hd hp, hpe, hx⟩)

theorem edgeWitness_bounds {L : ℝ} (hKL : K ≤ L) (e : RealEdge)
    (x : X) (hx : x ∈ c.edgeWitness cw e) :
    |z x 0| ≤ 1 ∧ |z x 1| ≤ L ∧ ∀ j, |T x j| ≤ L := by
  obtain ⟨p, hp, _, hxp⟩ := (c.mem_edgeWitness cw).mp hx
  obtain ⟨hz₀, hz₁, hT⟩ := cw.bounds p hp x hxp
  exact ⟨hz₀, hz₁.trans hKL, fun j => (hT j).trans hKL⟩

theorem cell_projection_error (hh : 0 ≤ h) (p : Point) (hp : p ∈ f.points)
    (x : X) (hx : x ∈ cw.cell p) (u : ℝ) :
    |z x 1 - u * z x 0 - (meshVertex h (roundedProjection u p)).1| ≤ (2 + |u|) * h ∧
    |(h / E) * (T x 0 + u * T x 1) -
      (meshVertex h (roundedProjection u p)).2| ≤ (2 + |u|) * h := by
  constructor
  · have hb := mesh_linear_error (u := -u) hh
      (cw.position_error p hp x hx 1) (cw.position_error p hp x hx 0)
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      abs_neg, meshVertex, roundedProjection, pointProjection, sub_eq_add_neg, neg_mul] using hb
  · have hb := mesh_linear_error (u := u) hh
      (cw.row_error p hp x hx 0) (cw.row_error p hp x hx 1)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hb
    convert hb using 1
    congr 1
    dsimp [meshVertex, roundedProjection, pointProjection]
    ring

theorem edgeWitness_projections {L : ℝ} (hh : 0 ≤ h) (hKL : 2 + K ≤ L)
    (e : RealEdge) (x : X) (hx : x ∈ c.edgeWitness cw e) :
    |z x 1 - f.velocity c.first * z x 0 - e.1.1| ≤ L * h ∧
    |(h / E) * (T x 0 + f.velocity c.first * T x 1) - e.1.2| ≤ L * h ∧
    |z x 1 - f.velocity c.second * z x 0 - e.2.1| ≤ L * h ∧
    |(h / E) * (T x 0 + f.velocity c.second * T x 1) - e.2.2| ≤ L * h := by
  obtain ⟨p, hp, hpe, hxp⟩ := (c.mem_edgeWitness cw).mp hx
  obtain ⟨h₁, h₂⟩ := cell_projection_error cw hh p hp x hxp (f.velocity c.first)
  obtain ⟨h₃, h₄⟩ := cell_projection_error cw hh p hp x hxp (f.velocity c.second)
  have hB₁ : (2 + |f.velocity c.first|) * h ≤ L * h :=
    mul_le_mul_of_nonneg_right (by linarith [f.velocity_bound c.first c.first_mem]) hh
  have hB₂ : (2 + |f.velocity c.second|) * h ≤ L * h :=
    mul_le_mul_of_nonneg_right (by linarith [f.velocity_bound c.second c.second_mem]) hh
  subst e
  exact ⟨h₁.trans hB₁, h₂.trans hB₁, h₃.trans hB₂, h₄.trans hB₂⟩

end SelectedCells
end Submission.Obl.k4_finite_row_graph_assembly
