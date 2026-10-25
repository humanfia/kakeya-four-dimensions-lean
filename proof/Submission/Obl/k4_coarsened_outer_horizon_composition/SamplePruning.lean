import Submission.Obl.k4_coarsened_outer_horizon_composition.CrossingBudget
import Submission.Obl.k4_coarsened_outer_horizon_composition.ChartMultiplicity
import Submission.Obl.k4_profile_density_bounds.Common

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set
open scoped ENNReal

/-- The complete one-sample deletion estimate, in real powers of the ambient
scale. All geometry and overlap hypotheses are read directly from the true charts. -/
theorem sample_pruning_loss {N κ r fL τ θ c₀ : ℝ} {W C T M D : ℕ}
    (hN : 2 ≤ N) (hκ : 1 ≤ κ) (hθ : 0 < θ)
    (ω : Fin W → ℝ) (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1)
    (ν : Fin W → Measure Line) (hν : ∀ w, IsProbabilityMeasure (ν w))
    (E : Fin W → Set Inc) (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (B : Fin W → ℝ) (hB : ∀ w, 0 < B w)
    (g : Fin W → Obs → ENNReal) (hg : ∀ w, Measurable (g w))
    (hlaw : ∀ w, (selected (ν w) (E w)).map (obs (B w) (δ N r)) =
      (volume.prod Measure.count).withDensity (g w))
    (γ : Fin C → Fin W) (j : Fin C → Fin (2 ^ T)) (a u : Fin C → E2)
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C → MvPolynomial (Fin 4) ℝ)
    (A : Fin C → Set Line) (F : Fin C → Set Inc)
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hc : ∀ b, chart N M D κ T ((j b : ℕ) : ℝ) r (B (γ b)) (E (γ b))
      (a b) (u b) (Q b) (R b) (A b) (F b)
      (ENNReal.ofReal (N ^ (-fL) * |(Q b).det| / ((2 : ℝ) ^ T * κ)) ≤
        ((ν (γ b)).prod volume) (F b)))
    (htyp : ∑ w, ENNReal.ofReal (ω w) * selected (ν w) (E w)
      {p | ENNReal.ofReal (N ^ (-fL + τ)) < g w (obs (B w) (δ N r) p)} ≤
      ENNReal.ofReal (N ^ (-c₀))) :
    let Cr := fun b => crossing κ (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T)
      ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) (δ N r / B (γ b)) (B (γ b))
      (a b) (u b) (Q b) (R b)
    ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume)
      (F b ∩ {p | ENNReal.ofReal θ <
        crossCount (Finset.univ.filter (fun b' => γ b' = γ b)) Cr
          (obs (B (γ b)) (δ N r) p)}) ≤
      ENNReal.ofReal (2 * N ^ (-c₀) + 1024 * κ ^ 5 * N ^ τ / θ) := by
  dsimp only
  let Cr := fun b => crossing κ (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T)
    ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) (δ N r / B (γ b)) (B (γ b))
    (a b) (u b) (Q b) (R b)
  have hN0 : 0 < N := by linarith
  have hF (b) : MeasurableSet (F b) ∧ F b ⊆ E (γ b) ∧
      ∀ p ∈ F b, p.1 ∈ A b ∧ p.2 ∈
        Icc (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T)
          ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) := by
    rcases hc b with ⟨_, _, _, _, _, _, _, hFm, _, _, hsel, _⟩
    exact ⟨hFm, fun p hp => (hsel p hp).1, fun p hp =>
      ⟨(hsel p hp).2.1, (hsel p hp).2.2.1⟩⟩
  have hμ (w) : selected (ν w) (E w) univ ≤ 1 := by
    letI := hν w
    exact Submission.Obl.k4_profile_density_bounds.selected_mass_le_one (ν w) (E w) (hE w)
  have hbound := pruning_loss_le ω hω0 hω1 ν E hμ
    (fun w => obs (B w) (δ N r)) (fun w => measurable_obs _ _) g hg hlaw
    γ F (fun b => (hF b).1) (fun b => (hF b).2.1) Cr
    (fun b => measurableSet_crossing ..)
    (chart_selected_multiplicity γ j A F hdisj (fun b => (hF b).2.2))
    (ENNReal.ofReal (N ^ (-fL + τ))) (ENNReal.ofReal (256 * κ ^ 5 * N ^ τ))
    (ENNReal.ofReal θ) (ENNReal.ofReal (N ^ (-c₀)))
    (ENNReal.ofReal_pos.mpr hθ).ne' ENNReal.ofReal_ne_top
    (fun b => chart_crossing_budget hN0 hκ (hB (γ b)) (ν (γ b)) (E (γ b))
      (a b) (u b) (Q b) (R b) (A b) (F b) (hc b)) htyp
  apply hbound.trans_eq
  rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
    show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ← ENNReal.ofReal_div_of_pos hθ,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end Submission.Obl.k4_coarsened_outer_horizon_composition
