-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file Basic.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory
open scoped ENNReal

abbrev Space := EuclideanSpace ℝ (Fin 3)

def Tube (δ : ℝ) (x v : Space) : Set Space :=
  Metric.thickening δ (segment ℝ x (x + v))

def Distinct {n : ℕ} (A : Fin n → Set Space) : Prop :=
  ∀ i j, i ≠ j → volume (A i ∩ A j) ≤ (1 / 2 : ENNReal) * volume (A i)

def Frostman {n : ℕ} (K : ℝ) (A : Fin n → Set Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (ncard {i | A i ⊆ W} : ℝ) ≤
      ENNReal.ofReal (K * n) * volume W

def KatzTao {n : ℕ} (δ K : ℝ) (A : Fin n → Set Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal ((ncard {i | A i ⊆ W} : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal K * volume W

def Sticky (ξ δ : ℝ) {n : ℕ} (A : Fin n → Set Space) : Prop :=
  ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 →
    ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-ξ) * ρ₀ ∧
      ∃ q : ℕ, 0 < q ∧ ∃ z w : Fin q → Space,
        (∀ j, ‖w j‖ = 1) ∧
        Distinct (fun j => Tube ρ (z j) (w j)) ∧
        (∀ i, ∃! j, A i ⊆ Tube ρ (z j) (w j)) ∧
        (∀ j, ∃ i, A i ⊆ Tube ρ (z j) (w j)) ∧
        (∀ j j', (ncard {i | A i ⊆ Tube ρ (z j) (w j)} : ℝ) ≤
          δ ^ (-ξ) * (ncard {i | A i ⊆ Tube ρ (z j') (w j')} : ℝ)) ∧
        (∀ j (W : Set Space), Convex ℝ W →
          ENNReal.ofReal ((ncard {i | A i ⊆ Tube ρ (z j) (w j) ∧ A i ⊆ W} : ℝ) * ρ ^ 2) ≤
            ENNReal.ofReal (δ ^ (-ξ) * (ncard {i | A i ⊆ Tube ρ (z j) (w j)} : ℝ)) * volume W)

def SeparatedScales (ζ₁ ζ₂ δ : ℝ) {n : ℕ} (A : Fin n → Set Space) : Prop :=
  ∃ τ ρ : ℝ, δ ≤ τ ∧ τ < ρ ∧ ρ ≤ 1 ∧ τ ≤ δ ^ ζ₁ * ρ ∧
    ∃ (p : ℕ) (y u : Fin p → Space) (q : ℕ) (z w : Fin q → Space),
      (∀ j, ‖u j‖ = 1) ∧ (∀ l, ‖w l‖ = 1) ∧
      Distinct (fun j => Tube τ (y j) (u j)) ∧
      Distinct (fun l => Tube ρ (z l) (w l)) ∧
      (∀ i, ∃! j, A i ⊆ Tube τ (y j) (u j)) ∧
      (∀ j, ∃ i, A i ⊆ Tube τ (y j) (u j)) ∧
      (∀ j, ∃! l, Tube τ (y j) (u j) ⊆ Tube ρ (z l) (w l)) ∧
      (∀ l, ∃ j, Tube τ (y j) (u j) ⊆ Tube ρ (z l) (w l)) ∧
      (∀ j j', (ncard {i | A i ⊆ Tube τ (y j) (u j)} : ℝ) ≤
        δ ^ (-ζ₂) * (ncard {i | A i ⊆ Tube τ (y j') (u j')} : ℝ)) ∧
      (∀ l l', (ncard {j | Tube τ (y j) (u j) ⊆ Tube ρ (z l) (w l)} : ℝ) ≤
        δ ^ (-ζ₂) * (ncard {j | Tube τ (y j) (u j) ⊆ Tube ρ (z l') (w l')} : ℝ)) ∧
      (∀ j (W : Set Space), Convex ℝ W →
        ENNReal.ofReal ((ncard {i | A i ⊆ Tube τ (y j) (u j) ∧ A i ⊆ W} : ℝ) * τ ^ 2) ≤
          ENNReal.ofReal (δ ^ (-ζ₂) * (ncard {i | A i ⊆ Tube τ (y j) (u j)} : ℝ)) * volume W) ∧
      (∀ l (W : Set Space), Convex ℝ W →
        ENNReal.ofReal ((ncard {j | Tube τ (y j) (u j) ⊆ Tube ρ (z l) (w l) ∧
          Tube τ (y j) (u j) ⊆ W} : ℝ) * τ ^ 2) ≤ ENNReal.ofReal (δ ^ (-ζ₂)) * volume W) ∧
      (∀ l, δ ^ ζ₂ * (ρ / τ) ^ 2 ≤ ncard {j | Tube τ (y j) (u j) ⊆ Tube ρ (z l) (w l)}) ∧
      Frostman (δ ^ (-ζ₂)) (fun l => Tube ρ (z l) (w l))

def Prism (a b : ℝ) (c e₁ e₂ e₃ : Space) : Set Space :=
  {y | |inner ℝ e₁ (y - c)| ≤ a ∧ |inner ℝ e₂ (y - c)| ≤ b ∧
    |inner ℝ e₃ (y - c)| ≤ 1}

def FlatPrisms (ζ₂ ζ₃ δ : ℝ) {n : ℕ} (A : Fin n → Set Space) : Prop :=
  ∃ a b : ℝ, δ ≤ a ∧ a ≤ δ ^ (ζ₂ / 200) * b ∧ b ≤ 1 ∧
    ∃ (p : ℕ) (c e₁ e₂ e₃ : Fin p → Space),
      (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧
      (∀ i, ∃ j, A i ⊆ Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ∧
      (∀ j j', (ncard {i | A i ⊆ Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)} : ℝ) ≤
        δ ^ (-ζ₃) * (ncard {i | A i ⊆ Prism a b (c j') (e₁ j') (e₂ j') (e₃ j')} : ℝ)) ∧
      Frostman (δ ^ (-ζ₃)) (fun j => Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ∧
      (∀ j (U : Set Space), Convex ℝ U →
        ENNReal.ofReal (ncard {i | A i ⊆ Prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∧ A i ⊆ U} : ℝ) *
          volume (Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ≤
        ENNReal.ofReal (δ ^ (-ζ₃) * (ncard {i | A i ⊆ Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)} : ℝ)) *
          volume U) ∧
      (∀ j (U : Set Space), Convex ℝ U →
        ENNReal.ofReal (ncard {j' | Prism a b (c j') (e₁ j') (e₂ j') (e₃ j') ⊆
          Metric.thickening b (Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ∧
          Prism a b (c j') (e₁ j') (e₂ j') (e₃ j') ⊆ U} : ℝ) *
          volume (Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ≤
        ENNReal.ofReal (δ ^ (-ζ₃)) * volume U)

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
