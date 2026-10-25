import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.Collision
import Submission.Obl.k4_retained_edge_planar_rigidity.EdgeLaw

/-!
# The collision contradiction produces a bounded parallel line fit

This packages the geometric end of paper Lemma 7.5 with explicit numerical hypotheses. The
analytic and scalar-closure inputs are respectively the flat coefficient law and the support
bound `hM`; choosing their scale parameters is separate from this finite argument.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open scoped Pointwise

noncomputable section

variable {𝔈 α : Type*} [Fintype 𝔈] [Fintype α] [DecidableEq 𝔈] [DecidableEq α]

/-- When the collision lower bound exceeds the upper bound for strip-free data, some bounded
parallel line fit captures a positive fraction of the original edge law. -/
theorem fit_of_collision
    (u : 𝔈 → ℝ) (hu : ∀ e, 0 ≤ u e) (hu1 : ∑ e, u e = 1)
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) (val : α → ℝ)
    (a b : 𝔈 → ℝ × ℝ) {E F : Finset (ℝ × ℝ)}
    (haE : ∀ e, a e ∈ E) (hbF : ∀ e, b e ∈ F) {m : ℕ}
    {h C D p q Δ φ M : ℝ} (hh : 0 < h) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hMpos : 0 < M)
    (hflat : ∀ x, lawMass w val (Set.Icc (x - h) (x + h)) ≤ φ)
    (hcap : ∀ x r, 0 ≤ r →
      (∑ e, u e * (if |(a e).1 - x| ≤ r then 1 else 0)) ≤ C * (r + h))
    (ha : ∀ e, |(a e).1| ≤ D ∧ |(a e).2| ≤ D)
    (hb : ∀ e, |(b e).1| ≤ D ∧ |(b e).2| ≤ D)
    (hM : ∀ γ : Fin m × Bool → α,
      ((cells h (∑ i, (val (γ (i, true)) • E + val (γ (i, false)) • F))).card : ℝ) ≤ M)
    (hbudget : (C * (q + h)) ^ m + (m : ℝ) * p ^ (m - 1) +
      (10 + 8 * D) / Δ * φ ^ 2 < 1 / M)
    (hsmall : 4 * C * (Δ / q + h) ≤ p) :
    ∃ ℓ c₁ c₂ : ℝ,
      |ℓ| + |c₁| + |c₂| ≤ (1 + 2 * D) * (4 * C * D / p) + 2 * D ∧
      p < ∑ e, u e * (if |(a e).2 - ℓ * (a e).1 - c₁| +
        |(b e).2 - ℓ * (b e).1 - c₂| ≤ 16 * C * D * Δ / (p * q) then 1 else 0) := by
  classical
  obtain ⟨v, x₀, y₀, hv, hmass⟩ : ∃ v x₀ y₀ : ℝ × ℝ,
      q ≤ max |v.1| |v.2| ∧
      p < ∑ e, u e * (if |wedge (a e - x₀) v| ≤ Δ ∧ |wedge (b e - y₀) v| ≤ Δ then 1 else 0) := by
    by_contra! hn
    have hπ : ∀ v : ℝ × ℝ, q ≤ max |v.1| |v.2| → ∀ x₀ y₀ : ℝ × ℝ,
        (∑ e, u e * (if |wedge (a e - x₀) v| ≤ Δ ∧ |wedge (b e - y₀) v| ≤ Δ then 1 else 0)) ≤ p := by
      intro v hv x₀ y₀
      exact hn v x₀ y₀ hv
    have hθ : ∑ z, pairLaw u z * (if shortPair a q z then 1 else 0) ≤ C * (q + h) := by
      exact short_pair_mass_le hu hu1 a hcap q hq.le
    have hcollision := collision_inequality u hu hu1 w hw hw1 val a b haE hbF (m := m)
      hh hΔ hΔ1 hp.le hMpos hflat (fun e => max_le (ha e).1 (ha e).2)
      (fun e => max_le (hb e).1 (hb e).2) hM hθ hπ
    exact (not_le_of_gt hbudget) hcollision
  let P : 𝔈 → Prop := fun e =>
    |wedge (a e - x₀) v| ≤ Δ ∧ |wedge (b e - y₀) v| ≤ Δ
  have hstrip : ∀ e, P e →
      |((a e).1 - x₀.1) * v.2 - ((a e).2 - x₀.2) * v.1| ≤ Δ ∧
      |((b e).1 - y₀.1) * v.2 - ((b e).2 - y₀.2) * v.1| ≤ Δ := by
    intro e he
    simpa only [P, wedge, Prod.fst_sub, Prod.snd_sub] using he
  obtain ⟨ℓ, c₁, c₂, hcoeff, hfit⟩ := parallel_strip_fit hu a b P hh.le hC hD hp hp1 hq hΔ.le
    hcap ha hb hmass.le v x₀ y₀ hv hstrip hsmall
  refine ⟨ℓ, c₁, c₂, hcoeff, hmass.trans_le ?_⟩
  refine Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ?_ (hu e)
  by_cases he : P e
  · rw [ite_eq_left he, ite_eq_left (hfit e he)]
  · rw [ite_eq_right he]; split_ifs <;> norm_num

end

end Submission.Obl.k4_retained_edge_planar_rigidity
