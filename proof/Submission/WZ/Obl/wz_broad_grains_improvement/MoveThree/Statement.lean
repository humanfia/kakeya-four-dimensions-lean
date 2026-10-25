-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Statement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Statement.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core

/-!
# The conclusion of o153 in terms of the abbreviations

`Move3 σ ω ζ ε` is the frozen conclusion of `WangZahlLot.wz_broad_grains_move_three`
after its parameters and hypotheses have been introduced.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- The gain alternative shared by all moves. -/
abbrev Gain (σ ω κ α δ : ℝ) (n : ℕ) (Y : Fin n → Set V) : Prop :=
  O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ)) ≤ μ (⋃i,Y i)

/-- The three alternatives of Move 3 at a fixed scale and family. -/
abbrev Move3Alt (σ ω ζ ε κ α δ η ρ c : ℝ) (n : ℕ) (x v : Fin n → V)
    (Y : Fin n → Set V) : Prop :=
  O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i) ∨ J ω ζ δ ε ρ c n x v Y 3 ∨
    ∃ρ' c',J ω ζ δ ε ρ' c' n x v Y 0∧(c≤c'∧δ^(-ζ/2000)*ρ≤ρ')

/-- The frozen conclusion of o153, after introducing `σ ω ζ ε`. -/
abbrev Move3 (σ ω ζ ε : ℝ) : Prop :=
  ∃α κ η d₀:ℝ,0<α∧0<κ∧0<η∧η≤ε∧0<d₀∧d₀≤1/100∧∀δ:ℝ,0<δ→δ≤d₀→∀n x v Y,
    A δ η (δ^(-η)) (δ^(-η)) n x v Y→∀ρ c,J ω ζ δ η ρ c n x v Y 2→
    O (κ*δ^(ω-α)*(n*δ^2)*(n*δ)^(-σ))≤μ (⋃i,Y i)∨J ω ζ δ ε ρ c n x v Y 3∨
    ∃ρ' c',J ω ζ δ ε ρ' c' n x v Y 0∧(c≤c'∧δ^(-ζ/2000)*ρ≤ρ')

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
