-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.MidDefs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Core

/-!
# Definitions for the middle offset range

* `safeCyl r e`: a thin vertical cylinder of radius `r` about the vertical axis, at heights
  `|z| < 1 - e`. Families in it can be translated horizontally by `r` and stay in the unit ball
  when `16 r² ≤ e ≤ 1/4`.
* `GBe`: the bounded offset estimate for one family of tubes counted with multiplicity, with a
  loss linear in the defect of its convex count. If the tubes inside every convex set `W`
  number at most `Kt |W + 2e (W - W)|`, then `ρ^ε m ≤ C Kt · area`. (For `Kt` comparable to
  `m` this is the bounded offset estimate itself; in general it follows from it by superposing
  horizontal translates of the family, which move `P_f` by measure-preserving maps; the
  enlargement `W + 2e (W - W)` has volume at most a constant times `|W|` for convex `W`.)
* `Z2`: the heights at which the twisted centres of two axes are close; both fibres of the
  projection over a point at height `z` can only meet the two tubes when `z ∈ Z2`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube SlopeN proj lineAt ctr)

/-- A thin vertical cylinder away from the poles. -/
def safeCyl (r e : ℝ) : Set Space := {p | p 0 ^ 2 + p 1 ^ 2 < r ^ 2 ∧ |p 2| < 1 - e}

/-- **Graceful B with multiplicity.** -/
def GBe : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∃ C : ℝ, 0 < C ∧
  ∀ ρ r e : ℝ, 0 < ρ → ρ ≤ d0 → ρ ^ η ≤ r → 16 * r ^ 2 ≤ e → e ≤ 1 / 4 →
  ∀ (m : ℕ) (x v : Fin m → Space) (Y : Fin m → Set Space) (Kt : ℝ), 0 < m →
    (∀ i, ‖v i‖ = 1) → (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
    (∀ i, tube ρ (x i) (v i) ⊆ safeCyl r e) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube ρ (x i) (v i)) →
    (∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | tube ρ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal Kt * volume (W + (2 * e) • (W - W))) →
    ENNReal.ofReal (ρ ^ η * (m : ℝ) * ρ ^ 2) ≤ ∑ i, volume (Y i) →
    ∀ f : ℝ → ℝ, SlopeN f → f 0 = 0 →
    ENNReal.ofReal (ρ ^ ε * (m : ℝ)) ≤ ENNReal.ofReal (C * Kt) * volume (proj f (⋃ i, Y i))

/-- Heights at which the twisted centres of two axes are within `6 δ (|f 0| + 3)`. -/
def Z2 (f : ℝ → ℝ) (δ : ℝ) (x v x' v' : Space) : Set ℝ :=
  {z | z ∈ Icc (-1 : ℝ) 1 ∧ |ctr f x v z - ctr f x' v' z| ≤ 6 * δ * (|f 0| + 3)}

end WangZahlLot.Obl.wz_intermediate_twist_normalization
