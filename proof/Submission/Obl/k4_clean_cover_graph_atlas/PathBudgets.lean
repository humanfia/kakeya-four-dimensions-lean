import Submission.Obl.k4_clean_cover_graph_atlas.EntryBudgets
import Submission.Obl.k4_clean_cover_graph_atlas.ChartMass
import Submission.Obl.k4_clean_cover_graph_atlas.FiniteInterface

namespace Submission.Obl.k4_clean_cover_graph_atlas
open MeasureTheory Set

section
variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
  {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
  {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {κ : ℝ} {C : ℕ}
  {lev : Fin C → ℕ} {par : Fin C → Fin C} {γ : Fin C → Fin W} {j : Fin C → ℕ}
  {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
  {R : Fin C → MvPolynomial (Fin 4) ℝ} {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
  {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)}

/-- Saturated charts give their original prior floor at the selected level. -/
theorem path_packet_prior_floor (hNk : 0 < Nk)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    {i : ℕ} (b : Fin C) (hlev : lev b = i) :
    ENNReal.ofReal (Nk ^ (-f (r i)) * |(Q b).det| / κ) ≤ ν (γ b) (A b) := by
  have hchart := (hpath.2.2.2.2.2.2.2 b).2.2
  rw [hlev] at hchart
  have hκ : 0 < κ := by linarith [hpath.1]
  apply chart_prior_floor (ν (γ b)) hNk hκ hchart
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsat⟩ := hchart
  exact hsat.1

/-- A path spends at most one unit of weighted original prior times old block
length. This bound is independent of its number of old packets. -/
theorem path_level_prior_budget {Mpr Dpr : ℕ}
    (hscalar : ScalarData Nk Mpr Dpr W ω ν E B)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (i : ℕ) :
    (∑ b : {b : Fin C // lev b = i}, ENNReal.ofReal (ω (γ b.val)) *
      (ENNReal.ofReal (((2 : ℝ) ^ T i)⁻¹) * ν (γ b.val) (A b.val))) ≤ 1 := by
  apply normalized_level_assignment_budget lev j γ A ν ω
    (fun w => (hscalar.2.2.2 w).1) hscalar.2.1 hscalar.2.2.1
  · intro b hb
    have h := (hpath.2.2.2.2.2.2.2 b).2.1
    rwa [hb] at h
  · intro b _
    have hchart := (hpath.2.2.2.2.2.2.2 b).2.2
    obtain ⟨_, _, _, _, _, _, hA, _⟩ := hchart
    exact hA
  · intro b b' hb hb' hne hγ hj
    exact hpath.2.2.2.2.2.2.1 b b' hne (hb.trans hb'.symm) hγ hj

end
end Submission.Obl.k4_clean_cover_graph_atlas
