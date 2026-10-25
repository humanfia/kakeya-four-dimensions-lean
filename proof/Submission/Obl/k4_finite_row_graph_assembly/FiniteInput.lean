import Submission.Obl.k4_finite_row_graph_assembly.Geometry

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/FiniteInput.lean.
import Submission.Obl.k4_finite_row_graph_assembly.Selection

open scoped BigOperators

namespace Submission.Obl.k4_finite_row_graph_assembly

/-- The finite information retained from the incidence measure.  `K` pays for
regularization and `R` for separating velocities. -/
structure FiniteIncidenceData (h K R s : ℝ) where
  points : Finset Point
  directions : Finset ℤ
  velocity : ℤ → ℝ
  mass : Point → ℤ → ℝ
  mass_nonneg : ∀ p d, 0 ≤ mass p d
  points_card : (points.card : ℝ) ≤ K / h ^ 2
  mass_upper : ∀ p ∈ points, ∀ d ∈ directions,
    mass p d ≤ K * h ^ 2 / directions.card
  mass_total : 1 / K ≤ ∑ p ∈ points, ∑ d ∈ directions, mass p d
  velocity_bound : ∀ d ∈ directions, |velocity d| ≤ K
  center_bound : ∀ p ∈ points, ∀ j, |h * (p j : ℝ)| ≤ K
  position_fiber : ∀ q : ℤ × ℤ,
    ((points.filter (fun p => (p 0, p 1) = q)).card : ℝ) ≤ K
  projection_cover : ∀ d ∈ directions,
    (((points.filter (fun p => 0 < mass p d)).image
      (roundedProjection (velocity d))).card : ℝ) ≤ K / h
  direction_cap : ∀ x r : ℝ, h ≤ r → r ≤ 1 →
    ((directions.filter (fun d => velocity d ∈ Set.Icc x (x + r))).card : ℝ) ≤
      K * r ^ s * directions.card
  near_cap : ∀ d₀ ∈ directions,
    ((directions.filter (fun d => |velocity d - velocity d₀| < 1 / R)).card : ℝ) ≤
      directions.card / (16 * K ^ 3)

namespace FiniteIncidenceData

theorem directions_nonempty {h K R s : ℝ} (f : FiniteIncidenceData h K R s)
    (hK : 0 < K) : f.directions.Nonempty := by
  by_contra h
  have he : f.directions = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hm := f.mass_total
  simp only [he, Finset.sum_empty, Finset.sum_const_zero] at hm
  exact (one_div_pos.mpr hK).not_ge hm

/-- The finite selection stage, with the mesh dependence canceled explicitly. -/
theorem select {h K R s : ℝ} (f : FiniteIncidenceData h K R s)
    (hh : 0 < h) (hK : 0 < K) :
    ∃ d₁ ∈ f.directions, ∃ d₂ ∈ f.directions,
      1 / R ≤ |f.velocity d₂ - f.velocity d₁| ∧
      ∃ D₃ : Finset ℤ, D₃ ⊆ f.directions ∧
      (∀ d ∈ D₃, 1 / R ≤ |f.velocity d - f.velocity d₁| ∧
        1 / R ≤ |f.velocity d - f.velocity d₂|) ∧
      (f.directions.card : ℝ) / (512 * K ^ 9) ≤ (D₃.card : ℝ) ∧
      ∀ d ∈ D₃,
        1 / (2048 * K ^ 11 * h ^ 2) ≤
          ((f.points.filter (fun p =>
            h ^ 2 / (2 * K ^ 2 * f.directions.card) ≤ f.mass p d₁ ∧
            h ^ 2 / (2 * K ^ 2 * f.directions.card) ≤ f.mass p d₂ ∧
            h ^ 2 / (2 * K ^ 2 * f.directions.card) ≤ f.mass p d ∧
            h ^ 2 / (8 * K ^ 5) ≤ ∑ e ∈ f.directions, f.mass p e)).card : ℝ) := by
  classical
  have hM : (0 : ℝ) < f.directions.card := by
    exact_mod_cast (f.directions_nonempty hK).card_pos
  let sep : ℤ → ℤ → Prop := fun d e => 1 / R ≤ |f.velocity e - f.velocity d|
  have hbad : ∀ d₀ ∈ f.directions,
      ((f.directions.filter (fun d => ¬ sep d₀ d)).card : ℝ) ≤
        f.directions.card / (16 * K ^ 3) := by
    intro d₀ hd₀
    simpa only [sep, not_le] using f.near_cap d₀ hd₀
  have heq₁ : (1 / K) / (4 * (K * h ^ 2 / f.directions.card) * (K / h ^ 2)) =
      f.directions.card / (4 * K ^ 3) := by field_simp
  have heq₂ : (1 / K) / (2 * (K / h ^ 2) * f.directions.card) =
      h ^ 2 / (2 * K ^ 2 * f.directions.card) := by field_simp
  have heq₃ : (f.directions.card : ℝ) / (4 * K ^ 3) *
      (h ^ 2 / (2 * K ^ 2 * f.directions.card)) = h ^ 2 / (8 * K ^ 5) := by
    field_simp; ring
  obtain ⟨d₁, hd₁, d₂, hd₂, hsep, D₃, hD₃, hsep₃, hcard, hcommon⟩ :=
    select_directions f.points f.directions f.mass sep f.mass_nonneg f.mass_upper
      (one_div_pos.mpr hK) (by positivity) f.mass_total f.points_card hbad
      (by positivity) (by rw [heq₁]; field_simp; ring_nf; exact le_rfl)
  refine ⟨d₁, hd₁, d₂, hd₂, hsep, D₃, hD₃, hsep₃, ?_, ?_⟩
  · convert hcard using 1
    rw [heq₁]
    field_simp; ring
  · intro d hd
    have hc := hcommon d hd
    rw [heq₁, heq₂, heq₃] at hc
    convert hc using 1
    field_simp; ring

end FiniteIncidenceData

/-- Original-incidence witnesses for the finite cells.  The edge construction
uses whole cells, so its mass floors survive all later direction selections. -/
structure CellWitnessData {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (z T : α → Fin 2 → ℝ) (h E K R s : ℝ)
    (f : FiniteIncidenceData h K R s) where
  cell : Point → Set α
  measurable_cell : ∀ p, MeasurableSet (cell p)
  disjoint_cell : Pairwise (fun p q => Disjoint (cell p) (cell q))
  cell_mass : ∀ p ∈ f.points,
    ENNReal.ofReal (∑ d ∈ f.directions, f.mass p d) ≤ μ (cell p)
  bounds : ∀ p ∈ f.points, ∀ x ∈ cell p,
    |z x 0| ≤ 1 ∧ |z x 1| ≤ K ∧ ∀ j, |T x j| ≤ K
  position_error : ∀ p ∈ f.points, ∀ x ∈ cell p, ∀ j : Fin 2,
    |z x j - h * ((![p 0, p 1] : Fin 2 → ℤ) j : ℝ)| ≤ h
  row_error : ∀ p ∈ f.points, ∀ x ∈ cell p, ∀ j : Fin 2,
    |(h / E) * T x j - h * ((![p 2, p 3] : Fin 2 → ℤ) j : ℝ)| ≤ h

end Submission.Obl.k4_finite_row_graph_assembly
