import Submission.Obl.k4_true_forest_own_depth_preparation.Model

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open MeasureTheory Set
open Submission.Obl.k4_coarsened_outer_horizon_composition

/-- The exact output of preparation at one sample. -/
def PreparedAt (N K : ℕ → ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc) (B : (k : ℕ) → Fin (W k) → ℝ)
    (f : ℝ → ℝ) (M D k m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ) (κ : ℝ)
    (C : ℕ) (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin (W k))
    (j : Fin C → ℕ) (c u : Fin C → E2) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set Line) (F : Fin C → Set Inc) : Prop :=
  ∃ (C' : ℕ) (emb : Fin C' ↪ Fin C) (par' : Fin C' → Fin C')
    (F' : Fin C' → Set Inc) (lst : ℕ → Fin (W k) → Obs → Finset (Fin C')),
  C' ≤ C ∧
  Core N K W ω ν E B f M D k m r T κ C'
    (fun b => lev (emb b)) par' (fun b => γ (emb b)) (fun b => j (emb b))
    (fun b => c (emb b)) (fun b => u (emb b)) (fun b => Q (emb b))
    (fun b => R (emb b)) (fun b => A (emb b)) F' ∧
  (∀ b, F' b ⊆ F (emb b) ∧ (0 < lev (emb b) → emb (par' b) = par (emb b))) ∧
  (∀ i γ₁ o, ((lst i γ₁ o).card : ℝ) ≤ κ) ∧
  (∀ b, ν k (γ (emb b)) (A (emb b)) ≤
    ENNReal.ofReal (κ * N k ^ (-f (r (lev (emb b)))) * |Matrix.det (Q (emb b))|) ∧
    ∀ p ∈ F' b, b ∈ lst (lev (emb b)) (γ (emb b))
      (obs (B k (γ (emb b))) (δ (N k) (r (lev (emb b)))) p)) ∧
  (∀ b, ENNReal.ofReal (ω k (γ (emb b))) *
    ((ν k (γ (emb b))).prod volume) (F' b) ≠ ⊤) ∧
  ∀ a, (∑ b, if 0 < lev (emb b) ∧ par' b = a then
    ENNReal.ofReal (ω k (γ (emb b))) *
      ((ν k (γ (emb b))).prod volume) (F' b) else 0) ≤
    ENNReal.ofReal (ω k (γ (emb a))) *
      ((ν k (γ (emb a))).prod volume) (F' a)

end Submission.Obl.k4_true_forest_own_depth_preparation
