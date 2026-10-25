import Submission.Obl.k4_finite_row_graph_assembly.FiniteInput

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/Selected.lean.
import Submission.Obl.k4_finite_row_graph_assembly.Lattice
import Submission.Obl.k4_finite_row_graph_assembly.Loss

namespace Submission.Obl.k4_finite_row_graph_assembly

open scoped BigOperators

structure SelectedCells {h K R s : ℝ} (f : FiniteIncidenceData h K R s) where
  first : ℤ
  second : ℤ
  first_mem : first ∈ f.directions
  second_mem : second ∈ f.directions
  separation : 1 / R ≤ |f.velocity second - f.velocity first|
  directions : Finset ℤ
  directions_subset : directions ⊆ f.directions
  directions_nonempty : directions.Nonempty
  directions_card : (f.directions.card : ℝ) / (512 * K ^ 9) ≤ directions.card
  separated : ∀ d ∈ directions, 1 / R ≤ |f.velocity d - f.velocity first| ∧
    1 / R ≤ |f.velocity d - f.velocity second|
  cells : ℤ → Finset Point
  cells_subset : ∀ d ∈ directions, cells d ⊆ f.points
  first_positive : ∀ d ∈ directions, ∀ p ∈ cells d, 0 < f.mass p first
  second_positive : ∀ d ∈ directions, ∀ p ∈ cells d, 0 < f.mass p second
  third_positive : ∀ d ∈ directions, ∀ p ∈ cells d, 0 < f.mass p d
  marginal_floor : ∀ d ∈ directions, ∀ p ∈ cells d,
    h ^ 2 / (8 * K ^ 5) ≤ ∑ e ∈ f.directions, f.mass p e
  cells_card : ∀ d ∈ directions, 1 / (2048 * K ^ 11 * h ^ 2) ≤ ((cells d).card : ℝ)

noncomputable def FiniteIncidenceData.selected {h K R s : ℝ}
    (f : FiniteIncidenceData h K R s) (hh : 0 < h) (hK : 0 < K) : SelectedCells f := Classical.choice (by
  classical
  obtain ⟨d₁, hd₁, d₂, hd₂, hsep, D, hD, hsepD, hcard, hcells⟩ := f.select hh hK
  have hM : (0 : ℝ) < f.directions.card := by
    exact_mod_cast (f.directions_nonempty hK).card_pos
  have hDne : D.Nonempty := by
    have hDpos : (0 : ℝ) < D.card := lt_of_lt_of_le (by positivity) hcard
    exact Finset.card_pos.mp (Nat.cast_pos.mp hDpos)
  let P := fun d => f.points.filter (fun p =>
    h ^ 2 / (2 * K ^ 2 * f.directions.card) ≤ f.mass p d₁ ∧
    h ^ 2 / (2 * K ^ 2 * f.directions.card) ≤ f.mass p d₂ ∧
    h ^ 2 / (2 * K ^ 2 * f.directions.card) ≤ f.mass p d ∧
    h ^ 2 / (8 * K ^ 5) ≤ ∑ e ∈ f.directions, f.mass p e)
  have hfloor : 0 < h ^ 2 / (2 * K ^ 2 * f.directions.card) := by positivity
  refine ⟨⟨d₁, d₂, hd₁, hd₂, hsep, D, hD, hDne, hcard, hsepD, P,
    (fun d _ => Finset.filter_subset _ _), ?_, ?_, ?_, ?_, hcells⟩⟩
  · intro d hd p hp
    exact hfloor.trans_le (Finset.mem_filter.mp hp).2.1
  · intro d hd p hp
    exact hfloor.trans_le (Finset.mem_filter.mp hp).2.2.1
  · intro d hd p hp
    exact hfloor.trans_le (Finset.mem_filter.mp hp).2.2.2.1
  · intro d hd p hp
    exact (Finset.mem_filter.mp hp).2.2.2.2)

namespace SelectedCells

variable {h K R s : ℝ} {f : FiniteIncidenceData h K R s} (c : SelectedCells f)

noncomputable def edgeMap (p : Point) : RealEdge :=
  meshEdge h (projectionPair (f.velocity c.first) (f.velocity c.second) p)

noncomputable def graph (d : ℤ) : Finset RealEdge := (c.cells d).image c.edgeMap

noncomputable def left : Finset (ℝ × ℝ) :=
  (f.points.filter (fun p => 0 < f.mass p c.first)).image
    (fun p => meshVertex h (roundedProjection (f.velocity c.first) p))

noncomputable def right : Finset (ℝ × ℝ) :=
  (f.points.filter (fun p => 0 < f.mass p c.second)).image
    (fun p => meshVertex h (roundedProjection (f.velocity c.second) p))

theorem graph_subset (d : ℤ) (hd : d ∈ c.directions) :
    c.graph d ⊆ c.left ×ˢ c.right := by
  classical
  intro e he
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
  have hpP := c.cells_subset d hd hp
  exact Finset.mem_product.mpr
    ⟨Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
      ⟨hpP, c.first_positive d hd p hp⟩, rfl⟩,
     Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
      ⟨hpP, c.second_positive d hd p hp⟩, rfl⟩⟩

theorem left_card (hh : h ≠ 0) : (c.left.card : ℝ) ≤ K / h := by
  classical
  have heq : c.left =
      (((f.points.filter (fun p => 0 < f.mass p c.first)).image
        (roundedProjection (f.velocity c.first))).image (meshVertex h)) := by
    rw [Finset.image_image]
    rfl
  rw [heq, Finset.card_image_of_injective _ (meshVertex_injective hh)]
  exact f.projection_cover c.first c.first_mem

theorem right_card (hh : h ≠ 0) : (c.right.card : ℝ) ≤ K / h := by
  classical
  have heq : c.right =
      (((f.points.filter (fun p => 0 < f.mass p c.second)).image
        (roundedProjection (f.velocity c.second))).image (meshVertex h)) := by
    rw [Finset.image_image]
    rfl
  rw [heq, Finset.card_image_of_injective _ (meshVertex_injective hh)]
  exact f.projection_cover c.second c.second_mem

theorem graph_card (hh : 0 < h) (hR : 1 ≤ R) (hKR : K ≤ R)
    (hK : 0 < K) (d : ℤ) (hd : d ∈ c.directions) :
    1 / (graphDenominator K R * h ^ 2) ≤ ((c.graph d).card : ℝ) := by
  classical
  have hP := c.cells_card d hd
  have hmult : ((c.cells d).card : ℝ) ≤ ((c.graph d).card : ℝ) * (6 * R ^ 2 + 2) ^ 4 := by
    apply Submission.Obl.k4_scalar_coefficient_clustering.card_le_image_mul_fiber
    intro e he
    obtain ⟨p₀, hp₀, heq⟩ := Finset.mem_image.mp he
    have hsub : (c.cells d).filter (fun p => c.edgeMap p = e) ⊆
        (c.cells d).filter (fun p => projectionPair (f.velocity c.first)
          (f.velocity c.second) p = projectionPair (f.velocity c.first)
          (f.velocity c.second) p₀) := by
      intro p hp
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, ?_⟩
      apply meshEdge_injective hh.ne'
      exact (Finset.mem_filter.mp hp).2.trans heq.symm
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (projectionPair_fiber_card _ hR
        ((f.velocity_bound c.first c.first_mem).trans hKR)
        ((f.velocity_bound c.second c.second_mem).trans hKR) c.separation _)
  have hB : 0 < (6 * R ^ 2 + 2) ^ 4 := by positivity
  have hD : 0 < 2048 * K ^ 11 * h ^ 2 := by positivity
  calc
    1 / (graphDenominator K R * h ^ 2) =
        (1 / (2048 * K ^ 11 * h ^ 2)) / (6 * R ^ 2 + 2) ^ 4 := by
      dsimp [graphDenominator]
      field_simp
    _ ≤ ((c.cells d).card : ℝ) / (6 * R ^ 2 + 2) ^ 4 :=
      div_le_div_of_nonneg_right hP hB.le
    _ ≤ ((c.graph d).card : ℝ) := (div_le_iff₀ hB).mpr hmult

end SelectedCells
end Submission.Obl.k4_finite_row_graph_assembly
