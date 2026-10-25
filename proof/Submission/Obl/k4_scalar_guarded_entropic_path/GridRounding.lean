import Submission.Obl.k4_scalar_guarded_entropic_path.NodeRounding

/-! Window-relative node depths have two-sided errors: subtracting two
nearby absolute path depths need not preserve their one-sided bounds. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

/-- The accepted one-sided node selector also handles the actual
window-relative depths, with their two-sided original-unit errors. -/
theorem exists_node_near_grid {m : ℕ} {Δ η sc : ℝ}
    (hΔ : 0 < Δ) (hη : 0 ≤ η) (hsc : 0 < sc)
    (depth : Fin (m + 1) → ℝ)
    (hdepth : ∀ a : Fin (m + 1), |depth a - ((a : ℕ) + 1 : ℝ) * Δ| ≤ η) :
    ∃ node : ℝ → Fin (m + 1), ∀ s : ℝ, Δ ≤ sc * s → sc * s ≤ ((m : ℝ) + 1) * Δ →
      |depth (node s) / sc - s| ≤ (Δ + 3 * η) / sc := by
  have hshift : ∀ a : Fin (m + 1),
      ((a : ℕ) + 1 : ℝ) * Δ - 2 * η ≤ depth a - η ∧
        depth a - η ≤ ((a : ℕ) + 1 : ℝ) * Δ := by
    intro a
    have ha := abs_le.mp (hdepth a)
    constructor <;> linarith
  obtain ⟨node, hn⟩ := exists_node hΔ (mul_nonneg (by norm_num) hη) hsc
    (fun a => depth a - η) hshift
  refine ⟨node, ?_⟩
  intro s hs₁ hs₂
  have ht := hn s hs₁ hs₂
  calc
    _ = |((depth (node s) - η) / sc - s) + η / sc| := by congr 1; ring
    _ ≤ |(depth (node s) - η) / sc - s| + |η / sc| := abs_add_le _ _
    _ ≤ (Δ + 2 * η) / sc + η / sc := by
      rw [abs_of_nonneg (div_nonneg hη hsc.le)]
      exact add_le_add ht le_rfl
    _ = _ := by ring

theorem exists_node_near_grid_count {count : ℕ} (hcount : 0 < count) {Δ η sc : ℝ}
    (hΔ : 0 < Δ) (hη : 0 ≤ η) (hsc : 0 < sc)
    (depth : Fin count → ℝ)
    (hdepth : ∀ a : Fin count, |depth a - ((a : ℕ) + 1 : ℝ) * Δ| ≤ η) :
    ∃ node : ℝ → Fin count, ∀ s : ℝ, Δ ≤ sc * s → sc * s ≤ (count : ℝ) * Δ →
      |depth (node s) / sc - s| ≤ (Δ + 3 * η) / sc := by
  cases count with
  | zero => omega
  | succ n =>
    simpa only [Nat.cast_add, Nat.cast_one] using exists_node_near_grid hΔ hη hsc depth hdepth

end Submission.Obl.k4_scalar_guarded_entropic_path
