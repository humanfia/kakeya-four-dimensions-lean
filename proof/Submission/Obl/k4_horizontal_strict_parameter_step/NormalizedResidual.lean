import Submission.Obl.k4_horizontal_strict_parameter_step.AffineUpgrade
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NormalizedResidual.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set

noncomputable section

/-- The time-only row obtained by subtracting the old full-time predictor from
one chosen true affine entry, in normalized static parameter coordinates. -/
def normalizedRow (f h : Fin 6 → ℝ) (D a t : ℝ) : Fin 2 → ℝ :=
  ![D / a * (f 2 + f 3 * t - h 2 - h 3 * t),
    D / a * (f 4 + f 5 * t - h 4 - h 5 * t)]

def normalizedResidual (f h : Fin 6 → ℝ) (D a p₀ q₀ t p q x : ℝ) : ℝ :=
  (x - predictor h t p q) / a -
    normalizedRow f h D a t 0 * ((p - p₀) / D) -
    normalizedRow f h D a t 1 * ((q - q₀) / D)

/-- Subtracting the row leaves a scalar error around a time-only graph value. -/
theorem normalizedResidual_eq (f h : Fin 6 → ℝ) {D a : ℝ} (hD : D ≠ 0)
    (ha : a ≠ 0) (p₀ q₀ t p q x : ℝ) :
    normalizedResidual f h D a p₀ q₀ t p q x =
      (x - predictor f t p q) / a +
        (predictor f t p₀ q₀ - predictor h t p₀ q₀) / a := by
  simp only [normalizedResidual, normalizedRow, predictor,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- A whole-domain bound on the difference of the true entries controls the
variation of their difference across the smaller static parameter square. -/
theorem predictor_difference_spatial {f g : Fin 6 → ℝ} {t p q p₀ q₀ L D : ℝ}
    (hL : 0 ≤ L) (hp : |p - p₀| ≤ D) (hq : |q - q₀| ≤ D)
    (hgrad : |g 2 + g 3 * t - f 2 - f 3 * t| ≤ L ∧
      |g 4 + g 5 * t - f 4 - f 5 * t| ≤ L) :
    |(predictor g t p q - predictor f t p q) -
      (predictor g t p₀ q₀ - predictor f t p₀ q₀)| ≤ 2 * L * D := by
  have heq : (predictor g t p q - predictor f t p q) -
      (predictor g t p₀ q₀ - predictor f t p₀ q₀) =
      (g 2 + g 3 * t - f 2 - f 3 * t) * (p - p₀) +
      (g 4 + g 5 * t - f 4 - f 5 * t) * (q - q₀) := by
    dsimp [predictor]; ring
  rw [heq]
  calc
    _ ≤ |(g 2 + g 3 * t - f 2 - f 3 * t) * (p - p₀)| +
      |(g 4 + g 5 * t - f 4 - f 5 * t) * (q - q₀)| := abs_add_le _ _
    _ ≤ L * D + L * D := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul hgrad.1 hp (abs_nonneg _) hL)
        (mul_le_mul hgrad.2 hq (abs_nonneg _) hL)
    _ = _ := by ring

/-- A deeper true entry gives one scalar support center. Its slope bound is
measured on its earlier full domain; only its variation across the current box is used. -/
theorem normalizedResidual_child_error {f g h : Fin 6 → ℝ}
    {D a a₁ p₀ q₀ t p q x L : ℝ} (hD : 0 < D) (ha : 0 < a) (hL : 0 ≤ L)
    (hp : |p - p₀| ≤ D) (hq : |q - q₀| ≤ D)
    (hfit : |x - predictor g t p q| ≤ a₁)
    (hgrad : |g 2 + g 3 * t - f 2 - f 3 * t| ≤ L ∧
      |g 4 + g 5 * t - f 4 - f 5 * t| ≤ L) :
    |normalizedResidual f h D a p₀ q₀ t p q x -
      (predictor g t p₀ q₀ - predictor h t p₀ q₀) / a| ≤ (a₁ + 2 * L * D) / a := by
  rw [normalizedResidual_eq f h hD.ne' ha.ne']
  have heq : (x - predictor f t p q) / a +
      (predictor f t p₀ q₀ - predictor h t p₀ q₀) / a -
      (predictor g t p₀ q₀ - predictor h t p₀ q₀) / a =
      ((x - predictor g t p q) + ((predictor g t p q - predictor f t p q) -
        (predictor g t p₀ q₀ - predictor f t p₀ q₀))) / a := by ring
  rw [heq, abs_div, abs_of_pos ha]
  apply div_le_div_of_nonneg_right _ ha.le
  exact (abs_add_le _ _).trans (add_le_add hfit (predictor_difference_spatial hL hp hq hgrad))

/-- A finite list of approximate scalar centers gives a finite list of scalar
bins, with a uniform count independent of the positions of those centers. -/
theorem scalar_bins_of_centers {α : Type*} {n : ℕ} (E : Set α) (S : α → ℝ)
    (centers : Fin n → ℝ) {w K : ℝ} (hw : 0 < w) (hK : 0 ≤ K)
    (hcover : ∀ l ∈ E, ∃ i, |S l - centers i| ≤ K * w) :
    ∃ Γ : Finset ℤ, (Γ.card : ℝ) ≤ (2 * K + 5) * n ∧
      ∀ l ∈ E, ⌊S l / w⌋ ∈ Γ := by
  classical
  let O : Finset ℤ := Finset.Icc (-⌈K + 1⌉) ⌈K + 1⌉
  let Γ : Finset ℤ := Finset.univ.biUnion fun i : Fin n => O.image (fun j => j + ⌊centers i / w⌋)
  refine ⟨Γ, ?_, ?_⟩
  · have hcard : Γ.card ≤ n * O.card := by
      calc
        Γ.card ≤ ∑ i : Fin n, (O.image (fun j => j + ⌊centers i / w⌋)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin n, O.card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
        _ = n * O.card := by simp
    have hcard' : (Γ.card : ℝ) ≤ (n : ℝ) * O.card := by exact_mod_cast hcard
    calc
      _ ≤ (n : ℝ) * O.card := hcard'
      _ ≤ (n : ℝ) * (2 * K + 5) := mul_le_mul_of_nonneg_left
        (Submission.Obl.k4_fixed_budget_quadratic_recovery.card_floor_offsets_le hK) (Nat.cast_nonneg _)
      _ = _ := by ring
  · intro l hl
    obtain ⟨i, hi⟩ := hcover l hl
    have hoff := Submission.Obl.k4_fixed_budget_quadratic_recovery.floor_offset_mem hw hi
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
    exact ⟨_, hoff, sub_add_cancel _ _⟩

end

end Submission.Obl.k4_horizontal_strict_parameter_step
