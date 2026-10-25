-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.ChartGraph, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/ChartGraph.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/ChartGraph.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.ChartVelocity

/-!
# Chart velocity graphs for the frozen chart predicate

For a chart `ch Nk M D κ T j r Bv Ev c u Q R A F ex` of the frozen statement, every assigned
trajectory satisfies, throughout its block of length `2^-T`,

  `|∇R(x l t) · (1, l₃, l₄, l₅)| ≤ C κ δ(Nk,r) 2^T`,

with a universal constant `C`, and on every counted incidence the hidden velocity is the
graph value `-(∂ₜR + ∂₁R l₃ + ∂₂R l₄)/∂₃R` up to `C κ² δ(Nk,r) 2^T / Bv`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad

open MvPolynomial

lemma x_eq_trajPoint (l : Ln) (t : ℝ) :
    Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.x l t = trajPoint l t := rfl

lemma δ_pos (N r : ℝ) : 0 < Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.δ N r := by
  unfold Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.δ
  positivity

/-- The time block `[j/2^T, (j+1)/2^T]` as an interval of length `2^-T`. -/
lemma block_eq (j : ℝ) (T : ℕ) :
    Set.Icc (j / (2:ℝ) ^ T) ((j + 1) / (2:ℝ) ^ T) =
      Set.Icc (j / (2:ℝ) ^ T) (j / (2:ℝ) ^ T + ((2:ℝ) ^ T)⁻¹) := by
  congr 1
  field_simp

/-- **Chart velocity graph** for the frozen chart predicate. -/
theorem exists_chart_graph_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (Nk : ℝ) (M D : ℕ) (κ : ℝ) (T : ℕ) (j r Bv : ℝ) (Evs : Set Ev)
      (c u : P2) (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : Po) (A : Set Ln) (F : Set Ev)
      (ex : Prop), 0 ≤ κ → ch Nk M D κ T j r Bv Evs c u Q R A F ex →
      (∀ l ∈ A, ∀ t ∈ Set.Icc (j / (2:ℝ) ^ T) ((j + 1) / (2:ℝ) ^ T),
        |liftedDerivative R l t| ≤ C * (κ * δ Nk r) * (2:ℝ) ^ T) ∧
      (0 < Bv → 0 < κ → ∀ p ∈ F,
        |p.1.2 5 + baseDerivative R p.1 p.2 /
            MvPolynomial.eval (trajPoint p.1 p.2) (pderiv 3 R)| ≤
          C * (κ * δ Nk r) * (2:ℝ) ^ T / (Bv / κ)) := by
  obtain ⟨C, hC, hgraph⟩ := exists_chart_velocity_constant
  refine ⟨C, hC, ?_⟩
  intro Nk M D κ T j r Bv Evs c u Q R A F ex hκ hch
  obtain ⟨_, _, _, _, hdeg, _, _, _, _, hA, hF, _⟩ := hch
  have hh : (0 : ℝ) < ((2:ℝ) ^ T)⁻¹ := by positivity
  have hM : 0 ≤ κ * δ Nk r := mul_nonneg hκ (δ_pos Nk r).le
  have hline : ∀ l ∈ A, ∀ t ∈ Set.Icc (j / (2:ℝ) ^ T) ((j + 1) / (2:ℝ) ^ T),
      |liftedDerivative R l t| ≤ C * (κ * δ Nk r) * (2:ℝ) ^ T := by
    intro l hl t ht
    have hsmall : ∀ s ∈ Set.Icc (j / (2:ℝ) ^ T) (j / (2:ℝ) ^ T + ((2:ℝ) ^ T)⁻¹),
        |MvPolynomial.eval (trajPoint l s) R| ≤ κ * δ Nk r := by
      intro s hs
      rw [← block_eq] at hs
      exact ((hA l hl).2.2 s hs).2.1
    rw [block_eq] at ht
    have := hgraph R l (j / (2:ℝ) ^ T) ((2:ℝ) ^ T)⁻¹ (κ * δ Nk r) hdeg hh hM hsmall t ht
    rwa [div_inv_eq_mul] at this
  refine ⟨hline, ?_⟩
  intro hB hκpos p hp
  obtain ⟨_, hpA, hpt, hpder⟩ := hF p hp
  exact hidden_velocity_graph R p.1 p.2 _ (Bv / κ) (div_pos hB hκpos)
    (hline p.1 hpA p.2 hpt) hpder

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad
