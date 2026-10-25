-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027.Definitions.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/- Adapted from the internal o015/x0589 assembly at effb3d2,
   WangZahlLot/Obl/wz_frostman_all_scales_volume/G027/Definitions.lean; original session credits below are retained. -/

namespace WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027

open Set Metric MeasureTheory
open scoped ENNReal

abbrev Space := LeanEval.Analysis.WangZahlKakeya.Space

abbrev Tube (δ : ℝ) (x v : Space) : Set Space :=
  thickening δ (segment ℝ x (x + v))

/-- The finite shaded family, with precisely the normalizations in the frozen type. -/
def DenseFamily (η δ : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧
  (∀ i, ‖v i‖ = 1) ∧
  (∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) ∧
  (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
    (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) ∧
  (∀ i, MeasurableSet (Y i)) ∧
  (∀ i, Y i ⊆ Tube δ (x i) (v i)) ∧
  ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)

/-- The given weak unique-containment covers, without an additional nesting condition. -/
def AllScales (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∃ ρ : ℝ,
    r ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * r ∧ ∃ k : ℕ, 0 < k ∧
    ∃ z w : Fin k → Space,
      (∀ j, ‖w j‖ = 1) ∧
      (∀ j j', j ≠ j' → volume (Tube ρ (z j) (w j) ∩ Tube ρ (z j') (w j')) ≤
        (1 / 2 : ENNReal) * volume (Tube ρ (z j) (w j))) ∧
      (∀ i, ∃! j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
      (∀ j, ∃ i, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
      (∀ j j', (ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ) ≤
        δ ^ (-η) * (ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j') (w j')} : ℝ)) ∧
      (∀ j, ∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal
          ((ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) ∧
            Tube δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal
          (δ ^ (-η) * (ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ)) *
          volume W)

/-- The output's single-scale convex nonconcentration bound. -/
def GlobalFrostman (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
      ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W

/-- The fixed exponent occurs before the arbitrarily small errors and scale cutoffs. -/
def VolumeExamples (s : ℝ) : Prop :=
  ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
    0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      DenseFamily η δ n x v Y ∧ AllScales η δ n x v ∧
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ s)

/-- The slope conditions in the output. -/
def RegularSlope (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Icc (-1) 1 →
    1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1 / 100 : ℝ)

abbrev TwistedProjection (f : ℝ → ℝ) (p : Space) : ℝ × ℝ :=
  (p 0 + f (p 2) * p 1, p 2)

def TwistedExamples (s : ℝ) : Prop :=
  ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
    0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      DenseFamily η δ n x v Y ∧
      (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) ∧ GlobalFrostman η δ n x v ∧
      ∃ f : ℝ → ℝ, RegularSlope f ∧
        volume (TwistedProjection f '' (⋃ i, Y i)) ≤ ENNReal.ofReal (δ ^ s)

end WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027
