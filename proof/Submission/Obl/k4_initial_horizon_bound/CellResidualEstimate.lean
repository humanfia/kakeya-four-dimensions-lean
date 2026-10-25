import Submission.Obl.k4_initial_horizon_bound.ResidualEstimate
import Submission.Obl.k4_initial_horizon_bound.CellCount
import Submission.Obl.k4_initial_horizon_bound.VisitedCells

/-! The residual bound with the visited-cell table eliminated using its
original whole-cell witnesses. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_initial_horizon_bound

open Submission.Lib.K4ContinuousPlanks
open Submission.Obl.k4_plank_projected_multiplicity (expandProjectedCells localCellOffsets)

theorem stopped_residual_old_cell_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
      (b u : α → EuclideanSpace ℝ (Fin 2)),
      Measurable b → Measurable u → (∀ x, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
      ∀ E : Set (α × ℝ), MeasurableSet E → E ⊆ univ ×ˢ Icc (0 : ℝ) 1 →
      ∀ τ A n : ℝ, 0 < τ → 0 < A → 0 < n → (D : ℝ) ^ (-η) ≤ τ →
      (∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ),
        ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → 0 < a → a ≤ β →
        (ν.withDensity (incidenceDuration E))
          {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β} ≤
            ENNReal.ofReal (A * a * β)) →
      ∀ (old : Measure (α × ℝ)) [IsFiniteMeasure old]
        (F : Finset (ℕ × (Fin 2 → ℤ))),
      (∀ p ∈ E, actualBaseCell D b u p ∈ F) →
      (∀ z ∈ F, n / (D : ℝ) ^ 3 ≤ old.real (actualBaseCell D b u ⁻¹' {z})) →
      (ν.prod volume) E ≤ ENNReal.ofReal τ * ν univ +
        ENNReal.ofReal (C * (A / n) * (D : ℝ) ^ ε / τ * old.real univ) := by
  obtain ⟨η, hη, C₀, hC₀, H⟩ := stopped_residual_mass_le ε hε
  refine ⟨η, hη, 121 * C₀, by positivity, ?_⟩
  intro D hD α _ ν _ b u hb hu hbu E hE hunit τ A n hτ hA hn hlong hstop old _ F hF hfloor
  have hDp : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  let V := expandProjectedCells F localCellOffsets
  have hV : ∀ x, ENNReal.ofReal τ ≤ incidenceDuration E x →
      ∀ j ∈ positiveTimeMarks D E x,
        Submission.Lib.K4PlankGeometry.cellCode D (b x) (u x) j ∈ V := by
    intro x _ j hj
    exact positiveTimeMarks_visited_table hD b u (fun x => (hbu x).2) E F hF x j hj
  have hmass := H D hD α ν b u hb hu hbu E hE hunit τ A hτ hA hlong hstop V hV
  have hcard : (V.card : ℝ) ≤ 121 * (old.real univ / (n / (D : ℝ) ^ 3)) := by
    have hnat : V.card ≤ 121 * F.card := expanded_visited_table_card F
    calc
      (V.card : ℝ) ≤ 121 * (F.card : ℝ) := by exact_mod_cast hnat
      _ ≤ 121 * (old.real univ / (n / (D : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left
          (original_cell_card_le old (actualBaseCell D b u)
            (measurable_actualBaseCell D b u hb hu) F (by positivity) hfloor) (by norm_num)
  refine hmass.trans (add_le_add (le_refl _) (ENNReal.ofReal_le_ofReal ?_))
  calc
    C₀ * (A / τ) * (D : ℝ) ^ ε / (D : ℝ) ^ 3 * (V.card : ℝ) ≤
        C₀ * (A / τ) * (D : ℝ) ^ ε / (D : ℝ) ^ 3 *
          (121 * (old.real univ / (n / (D : ℝ) ^ 3))) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (121 * C₀) * (A / n) * (D : ℝ) ^ ε / τ * old.real univ := by
      field_simp
      <;> ring

end Submission.Obl.k4_initial_horizon_bound
