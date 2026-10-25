import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GridCells

/-! Put a bounded normalized packet box, including its thickened grid cells, inside the unit box. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

def normalizeBase (H : ℝ) (u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => 1 / 2 + u i / (4 * H)

theorem normalizeBase_margin {H : ℝ} (hH : 0 < H) (u : Fin 2 → ℝ)
    (hu : ∀ i, |u i| ≤ H) (i : Fin 2) :
    1 / 4 ≤ normalizeBase H u i ∧ normalizeBase H u i ≤ 3 / 4 := by
  have hr : |u i / (4 * H)| ≤ 1 / 4 := by
    have h4 : 0 < 4 * H := by positivity
    rw [abs_div, abs_of_pos h4]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [hu i]
  have hb := abs_le.mp hr
  dsimp [normalizeBase]
  constructor <;> linarith

theorem normalizeBase_inverse {H : ℝ} (hH : H ≠ 0) (u : Fin 2 → ℝ) :
    (fun i => -2 * H + (4 * H) * normalizeBase H u i) = u := by
  ext i
  dsimp [normalizeBase]
  field_simp
  ring

theorem baseGridTag_normalizeBase {H ξ : ℝ} (hH : H ≠ 0) (hξ : ξ ≠ 0) (u : Fin 2 → ℝ) :
    baseGridTag (fun _ => (1 : ℝ) / 2) (ξ / (4 * H)) (normalizeBase H u) =
      baseGridTag 0 ξ u := by
  ext i
  change (⌊((1 / 2 + u i / (4 * H)) - 1 / 2) / (ξ / (4 * H))⌋ : ℤ) =
    ⌊(u i - 0) / ξ⌋
  congr 1
  field_simp
  ring

theorem normalized_baseGridCell_subset_unit {H ξ : ℝ} (hH : 0 < H) (hξ : 0 < ξ)
    (hξH : ξ ≤ H) (u : Fin 2 → ℝ) (hu : ∀ i, |u i| ≤ H) :
    baseGridCell (fun _ => (1 : ℝ) / 2) (ξ / (4 * H))
      (baseGridTag (fun _ => (1 : ℝ) / 2) (ξ / (4 * H)) (normalizeBase H u)) ⊆
        Set.Icc (0 : Fin 2 → ℝ) 1 := by
  intro x hx
  have hmesh : 0 < ξ / (4 * H) := by positivity
  have hmesh1 : ξ / (4 * H) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hd : dist x (normalizeBase H u) ≤ ξ / (4 * H) :=
    dist_le_of_same_baseGridCell _ hmesh hx ((mem_baseGridCell_iff _ hmesh _ _).mpr rfl)
  have hcoord (i : Fin 2) : |x i - normalizeBase H u i| ≤ ξ / (4 * H) := by
    have h := dist_le_pi_dist x (normalizeBase H u) i
    rw [Real.dist_eq] at h
    exact h.trans hd
  constructor
  · intro i
    change 0 ≤ x i
    have hm := normalizeBase_margin hH u hu i
    have hc := abs_le.mp (hcoord i)
    linarith
  · intro i
    change x i ≤ 1
    have hm := normalizeBase_margin hH u hu i
    have hc := abs_le.mp (hcoord i)
    linarith

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
