import Submission.Obl.k4_oss_finite_energy_relation.Counting
import Submission.Obl.k4_oss_finite_energy_relation.Packing

namespace Submission.Obl.k4_oss_finite_energy_relation

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Separation of the second coordinate bounds every approximate projection degree. -/
theorem projection_degree_le {δ t : ℝ} (hδ : 0 < δ) (ht : (1 : ℝ) / 4 ≤ t)
    (A B : Finset ℝ)
    (hBsep : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b') (x : ℝ) :
    (((A.product B).filter (fun p : ℝ × ℝ => |x - (p.1 + t * p.2)| ≤ 16 * δ)).card : ℝ) ≤
      130 * (A.card : ℝ) := by
  classical
  rw [card_product_filter_eq_sum A B (fun a b => |x - (a + t * b)| ≤ 16 * δ)]
  calc
    (∑ a ∈ A, ((B.filter (fun b => |x - (a + t * b)| ≤ 16 * δ)).card : ℝ)) ≤
        ∑ _a ∈ A, (130 : ℝ) := by
      exact Finset.sum_le_sum (fun a _ => affine_window_card hδ ht B hBsep a x)
    _ = 130 * (A.card : ℝ) := by simp [mul_comm]

/-- A large energy has many points with degree at least half its average lower bound. -/
theorem exists_popular_projection_points {δ τ t : ℝ} (hδ : 0 < δ) (hτ : 0 < τ)
    (ht : (1 : ℝ) / 4 ≤ t) (A B : Finset ℝ) (hA : A.Nonempty)
    (hBsep : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b')
    (henergy : τ * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤
      ((((A.product B).product (A.product B)).filter
        (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
          |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ)) :
    ∃ H : Finset (ℝ × ℝ), H ⊆ A.product B ∧
      (τ / 260) * (A.card : ℝ) * (B.card : ℝ) ≤ (H.card : ℝ) ∧
      ∀ p ∈ H, τ * (A.card : ℝ) / 2 ≤
        (((A.product B).filter (fun q : ℝ × ℝ =>
          |p.1 + t * p.2 - (q.1 + t * q.2)| ≤ 16 * δ)).card : ℝ) := by
  classical
  let P := A.product B
  let d (p : ℝ × ℝ) : ℝ :=
    ((P.filter (fun q : ℝ × ℝ => |p.1 + t * p.2 - (q.1 + t * q.2)| ≤ 16 * δ)).card : ℝ)
  let H := P.filter (fun p => τ * (A.card : ℝ) / 2 ≤ d p)
  have hN : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hL : 0 ≤ τ * (A.card : ℝ) / 2 := by positivity
  have hbound := sum_le_threshold_add_popular P d hL
    (fun p _ => projection_degree_le hδ ht A B hBsep (p.1 + t * p.2))
  change (∑ p ∈ P, d p) ≤ τ * (A.card : ℝ) / 2 * (P.card : ℝ) +
    130 * (A.card : ℝ) * (H.card : ℝ) at hbound
  have hsum : τ * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤ ∑ p ∈ P, d p := by
    rw [card_product_filter_eq_sum (A.product B) (A.product B)
      (fun p q : ℝ × ℝ => |p.1 + t * p.2 - (q.1 + t * q.2)| ≤ 16 * δ)] at henergy
    exact henergy
  have hP : (P.card : ℝ) = (A.card : ℝ) * (B.card : ℝ) := by
    simp [P, Finset.product_eq_sprod]
  rw [hP] at hbound
  have hmass : (τ / 260) * (A.card : ℝ) * (B.card : ℝ) ≤ (H.card : ℝ) := by
    apply (mul_le_mul_iff_left₀ hN).mp
    nlinarith only [hsum, hbound]
  exact ⟨H, Finset.filter_subset _ _, hmass, fun p hp => (Finset.mem_filter.mp hp).2⟩

end Submission.Obl.k4_oss_finite_energy_relation
