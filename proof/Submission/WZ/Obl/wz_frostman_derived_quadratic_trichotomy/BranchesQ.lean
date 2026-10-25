-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.BranchesQ.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Branches

/-!
# Branch statements with the quadratic count (for `TrichotomyDerivedQ`)

`StickyBranchStmtQ`, `NonStickyBranchStmtQ`: `Branches.lean`'s statements with the flat output
`X318.FlatPrisms` replaced by `FlatPrismsQ` (the same prisms also satisfy the global quadratic
count of x0264's `CountedGain`). Inputs (`Prepared`, grid, profile) are unchanged.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

open MeasureTheory

/-- Frozen `SC` (`X318.FlatPrisms`) together with the global quadratic count of the same prisms
(x0264's `CountedGain` hypothesis): `#{j | P j ⊆ U} (ab)² ≤ δ^(-ζ₃) |U|²` for convex `U`. -/
def FlatPrismsQ (ζ₂ ζ₃ δ : ℝ) {n : ℕ} (A : Fin n → Set Sp) : Prop :=
  ∃ a b : ℝ, δ ≤ a ∧ a ≤ δ ^ (ζ₂ / 200) * b ∧ b ≤ 1 ∧
    ∃ (p : ℕ) (c e₁ e₂ e₃ : Fin p → Sp),
      (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧
      (∀ i, ∃ j, A i ⊆ X318.Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ∧
      (∀ j j', (Set.ncard {i | A i ⊆ X318.Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)} : ℝ) ≤
        δ ^ (-ζ₃) * (Set.ncard {i | A i ⊆ X318.Prism a b (c j') (e₁ j') (e₂ j') (e₃ j')} : ℝ)) ∧
      X318.Frostman (δ ^ (-ζ₃)) (fun j => X318.Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ∧
      (∀ j (U : Set Sp), Convex ℝ U →
        ENNReal.ofReal (Set.ncard {i | A i ⊆ X318.Prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∧
            A i ⊆ U} : ℝ) * volume (X318.Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ≤
        ENNReal.ofReal (δ ^ (-ζ₃) *
            (Set.ncard {i | A i ⊆ X318.Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)} : ℝ)) * volume U) ∧
      (∀ j (U : Set Sp), Convex ℝ U →
        ENNReal.ofReal (Set.ncard {j' | X318.Prism a b (c j') (e₁ j') (e₂ j') (e₃ j') ⊆
          Metric.thickening b (X318.Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ∧
          X318.Prism a b (c j') (e₁ j') (e₂ j') (e₃ j') ⊆ U} : ℝ) *
          volume (X318.Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ≤
        ENNReal.ofReal (δ ^ (-ζ₃)) * volume U) ∧
      (∀ U : Set Sp, Convex ℝ U →
        ENNReal.ofReal (Set.ncard {j | X318.Prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ⊆ U} : ℝ) *
          ENNReal.ofReal ((a * b) ^ 2) ≤ ENNReal.ofReal (δ ^ (-ζ₃)) * volume U ^ 2)

/-- **Sticky branch, quadratic-count variant.** A sticky profile gives frozen `S` or `FlatPrismsQ` on a `δ^ω` share. -/
def StickyBranchStmtQ : Prop :=
  ∀ ξ ζ₂ ζ₃ ω : ℝ, 0 < ζ₃ → ζ₃ ≤ ζ₂ → ζ₂ ≤ ξ → 0 < ω → ∀ (Nmax : ℕ) (Cp : ℝ),
  ∃ ζF : ℝ, 0 < ζF ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
  ∀ L top : ℕ, 2 ≤ L → δ ^ (-(ζ₂ / 256)) ≤ (L : ℝ) → (L : ℝ) ≤ δ ^ (-(ζ₂ / 16)) →
    top + 1 ≤ Nmax → 2 * δ * (L : ℝ) ^ top ≤ 1 / 10000 → δ ^ (ξ / 2) ≤ 2 * δ * (L : ℝ) ^ top →
  ∀ (m : ℕ) (x v : Fin m → Sp) (S : Finset (Fin m)) (a : ℕ → ℕ),
    (m : ℝ) * δ ^ 4 ≤ Cp → Prepared δ L top x v S a (δ ^ (-ζF)) →
    (∀ i j, i ≤ j → j ≤ top →
      X318.cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top i - ξ / 2 ≤
        X318.cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top j) →
  ∃ (k : ℕ) (g : Fin k → Fin m), Function.Injective g ∧ (∀ j, g j ∈ S) ∧
    δ ^ ω * S.card ≤ k ∧
    (AllScales ξ δ (fun j => x (g j)) (fun j => v (g j)) ∨
      FlatPrismsQ ζ₂ ζ₃ δ
        (fun j => Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j)))))

/-- **Non-sticky branch, quadratic-count variant.** Separated levels `i₀ < j₂` of the profile give
frozen `SB` or `FlatPrismsQ` on a `δ^ω` share; `τ = ρ (top - j₂)` and `ρ = ρ (top - i₀)`, so `ρ / τ = L^(j₂ - i₀)`. -/
def NonStickyBranchStmtQ : Prop :=
  ∀ ζ₁ ζ₂ ζ₃ ω : ℝ, 0 < ζ₃ → ζ₃ ≤ ζ₂ → ζ₂ ≤ ζ₁ → 0 < ω → ∀ (Nmax : ℕ) (Cp : ℝ),
  ∃ ζF : ℝ, 0 < ζF ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
  ∀ L top : ℕ, 2 ≤ L → δ ^ (-(ζ₂ / 256)) ≤ (L : ℝ) → (L : ℝ) ≤ δ ^ (-(ζ₂ / 16)) →
    top + 1 ≤ Nmax → 2 * δ * (L : ℝ) ^ top ≤ 1 / 10000 →
  ∀ (m : ℕ) (x v : Fin m → Sp) (S : Finset (Fin m)) (a : ℕ → ℕ),
    (m : ℝ) * δ ^ 4 ≤ Cp → Prepared δ L top x v S a (δ ^ (-ζF)) →
  ∀ i₀ j₂ : ℕ, i₀ < j₂ → j₂ ≤ top →
    (∀ l, i₀ ≤ l → l ≤ top →
      X318.cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top j₂ ≤
        X318.cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top l) →
    X318.cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top i₀ - ζ₂ / 2 ≤
      X318.cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top j₂ →
    δ ^ (-ζ₁) ≤ (L : ℝ) ^ (j₂ - i₀) →
  ∃ (k : ℕ) (g : Fin k → Fin m), Function.Injective g ∧ (∀ j, g j ∈ S) ∧
    δ ^ ω * S.card ≤ k ∧
    (SBpred ζ₁ ζ₂ δ k (fun j => Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j)))) ∨
      FlatPrismsQ ζ₂ ζ₃ δ
        (fun j => Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j)))))

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
