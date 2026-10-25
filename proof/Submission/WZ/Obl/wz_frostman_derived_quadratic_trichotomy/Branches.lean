-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Branches.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CellProfile
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Basic
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.SBBranch
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.StickyBranch
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Regularize

/-!
# The two branch statements of the derived trichotomy

`TrichotomyDerivedSC` is composed from the canonicalization (`canonical_setup`), the grid
`ρ k = 2 δ L^k` (`k ≤ top`), the common classes and the dyadic regularization, the choice of
scales on the cell-count profile `G = X318.cellProfile δ a ρ top` (`profile_dichotomy_step`), and
two branch lemmas, stated here as propositions:

* `StickyBranchStmt`: a sticky profile (`G i - ξ/2 ≤ G j` for `i ≤ j`) gives a subfamily with
  frozen `S` (`AllScales ξ`) or frozen `SC` (`X318.FlatPrisms ζ₂ ζ₃`);
* `NonStickyBranchStmt`: levels `i₀ < j₂` with `G j₂ ≤ G l` on `[i₀, top]`,
  `G i₀ - ζ₂/2 ≤ G j₂` and `δ^(-ζ₁) ≤ L^(j₂ - i₀)` give a subfamily with frozen `SB`
  (`SBpred ζ₁ ζ₂`) or frozen `SC`.

Both take the same prepared family (`Prepared`): canonical tubes (`x = leftStart δ x v`), unit
directions without antipodal pairs, inside `B(0,1)`, pairwise half-overlapping, and a nonempty
index set `S` with one residue class (`classKey 200000`) and one dyadic population class `a k`
per level, and global Frostman with constant `K`. Both lose at most `δ^ω` of `S`, where `ω > 0`
is given; each may ask for a small Frostman exponent `ζF` and small scales `δ ≤ δ₁`, depending
only on the parameters, the level bound `Nmax` and the packing constant `Cp`.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

open MeasureTheory

open Classical in
/-- The prepared family at scale `δ` on the grid `ρ k = 2 δ L^k`, `k ≤ top`, with population
classes `a k` and global Frostman constant `K`. -/
def Prepared (δ : ℝ) (L top : ℕ) {m : ℕ} (x v : Fin m → Sp) (S : Finset (Fin m)) (a : ℕ → ℕ)
    (K : ℝ) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧
  (∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1) ∧
  (∀ i j, i ≠ j → volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩
      Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤
    (1 / 2 : ENNReal) * volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) ∧
  (∀ i, x i = leftStart δ (x i) (v i)) ∧ (∀ i j, 1 ≤ ‖v i + v j‖) ∧
  S.Nonempty ∧
  (∀ k ≤ top, ∀ i ∈ S, ∀ i' ∈ S, classKey 200000 (2 * δ * (L : ℝ) ^ k) (x i) (v i) =
      classKey 200000 (2 * δ * (L : ℝ) ^ k) (x i') (v i')) ∧
  (∀ k ≤ top, ∀ i ∈ S,
      2 ^ a k ≤ pop S (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i ∧
      pop S (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i < 2 ^ (a k + 1)) ∧
  (∀ W : Set Sp, Convex ℝ W →
    ENNReal.ofReal ((S.filter (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card : ℝ) ≤
      ENNReal.ofReal (K * S.card) * volume W)

/-- **Sticky branch.** A sticky profile gives frozen `S` or frozen `SC` on a `δ^ω` share. -/
def StickyBranchStmt : Prop :=
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
      X318.FlatPrisms ζ₂ ζ₃ δ
        (fun j => Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j)))))

/-- **Non-sticky branch.** Separated levels `i₀ < j₂` of the profile give frozen `SB` or frozen
`SC` on a `δ^ω` share; `τ = ρ (top - j₂)` and `ρ = ρ (top - i₀)`, so `ρ / τ = L^(j₂ - i₀)`. -/
def NonStickyBranchStmt : Prop :=
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
      X318.FlatPrisms ζ₂ ζ₃ δ
        (fun j => Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j)))))

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
