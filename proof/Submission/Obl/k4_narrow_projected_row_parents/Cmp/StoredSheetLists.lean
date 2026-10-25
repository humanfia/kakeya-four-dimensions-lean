/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/StoredSheetLists.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_scalar_grid_parameter_preparation.PaletteScaledCellCount

/-!
# Counting nearby sheets with stored original witnesses

The list count in Lemma 8.3 uses a label's stored original witness set. No mass floor for
that index in a later pair law is needed. The identical original palette mass cancels
between the stored floors and the graph tube ceiling.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set
open scoped ENNReal Classical

noncomputable section

/-- Nearby sheets are few because their disjoint stored witnesses all lie in one graph
tube. The palette factor is exactly the same on both sides. -/
theorem stored_sheet_list_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ} {radius : ℝ}
    (witness : Fin n → Set Ω) (hdisj : Pairwise (fun i j => Disjoint (witness i) (witness j)))
    (hmeas : ∀ i, MeasurableSet (witness i))
    (base : Ω → EuclideanSpace ℝ (Fin 3)) (signal : Ω → ℂ)
    (f : Fin n → EuclideanSpace ℝ (Fin 3) → ℂ)
    (ref : EuclideanSpace ℝ (Fin 3) → ℂ)
    {a M K B T d : ℝ} (ha : 0 < a) (hM : a ≤ M) (hK : 0 < K) (hB : 0 ≤ B) (hT : 0 < T)
    (palette : ℝ≥0∞) (hp : palette ≠ 0) (hpt : palette ≠ ⊤)
    (hfloor : ∀ i, ENNReal.ofReal (T / K) * palette ≤ μ (witness i))
    (hfit : ∀ i, ∀ p ∈ witness i,
      ‖base p‖ ≤ radius ∧ ‖signal p - f i (base p)‖ ≤ a)
    (hcap : μ {p | ‖base p‖ ≤ radius ∧ ‖signal p - ref (base p)‖ ≤ 2 * M} ≤
      ENNReal.ofReal (B * T * (M / a) ^ d) * palette) :
    ((Finset.univ.filter fun i : Fin n => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ radius →
      ‖f i x - ref x‖ ≤ M).card : ℝ) ≤ B * K * (M / a) ^ d := by
  classical
  have hMpos : 0 < M := ha.trans_le hM
  let F := Finset.univ.filter fun i : Fin n => ∀ x : EuclideanSpace ℝ (Fin 3),
    ‖x‖ ≤ radius → ‖f i x - ref x‖ ≤ M
  have hcover : ∀ i ∈ F, witness i ⊆
      {p | ‖base p‖ ≤ radius ∧ ‖signal p - ref (base p)‖ ≤ 2 * M} := by
    intro i hi p hpw
    have hnear := (Finset.mem_filter.mp hi).2
    have hw := hfit i p hpw
    refine ⟨hw.1, ?_⟩
    calc ‖signal p - ref (base p)‖ ≤ ‖signal p - f i (base p)‖ + ‖f i (base p) - ref (base p)‖ :=
          by simpa only [dist_eq_norm] using dist_triangle (signal p) (f i (base p)) (ref (base p))
      _ ≤ a + M := add_le_add hw.2 (hnear (base p) hw.1)
      _ ≤ 2 * M := by linarith
  have hcount := Submission.Obl.k4_scalar_grid_parameter_preparation.palette_scaled_old_cell_count
    μ F witness (fun i _ j _ hij => hdisj hij) (fun i _ => hmeas i) _ hcover
    (T / K) (B * T * (M / a) ^ d) (by positivity) (by positivity)
    palette hp hpt (fun i _ => hfloor i) hcap
  calc (F.card : ℝ) ≤ (B * T * (M / a) ^ d) / (T / K) := hcount
    _ = B * K * (M / a) ^ d := by field_simp [hT.ne', hK.ne']

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
