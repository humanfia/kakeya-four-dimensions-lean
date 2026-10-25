-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Mono.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Mono.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Defs

/-!
# Error monotonicity of the frozen states, and the gain under smaller constants

For `0 < d ≤ 1` and `h ≤ h'`, every clause of `A`, `C`, `H`, `Broad` and `J` that depends on
the error gets weaker when `h` is replaced by `h'`: `d ^ h' ≤ d ^ h` and `d ^ (-h) ≤ d ^ (-h')`.
The stopping conditions of `J` do not depend on the error. (Adapted from x0433, commit 8315927, which in turn adapted
session x0417 on o151; shared monotonicity results are imported from Core.)
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- `d ^ h' ≤ d ^ h` and `d ^ (-h) ≤ d ^ (-h')` for `0 < d ≤ 1`, `h ≤ h'`. -/
theorem rpow_err_le {d h h' : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h') :
    d ^ h' ≤ d ^ h ∧ d ^ (-h) ≤ d ^ (-h') :=
  ⟨Real.rpow_le_rpow_of_exponent_ge hd hd1 hh,
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hh)⟩

theorem Broad_mono {ω ζ d h h' ρ : ℝ} {n N : ℕ} {v : Fin n → V} {S : Finset (Fin n)}
    {Z : Fin n → Set V} {f : Fin n → Fin N}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (hb : Broad ω ζ d h ρ n N v S Z f) : Broad ω ζ d h' ρ n N v S Z f := by
  obtain ⟨-, hi⟩ := rpow_err_le hd hd1 hh
  intro k p u r hu hdr hrρ
  have hr : 0 < r := hd.trans_le hdr
  have hρ : 0 < ρ := hr.trans_le hrρ
  refine (hb k p u r hu hdr hrρ).trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
  exact mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg (div_nonneg hr.le hρ.le) _)

/-- `J` with its witnesses made explicit. -/
theorem J_iff {ω ζ d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} {j : ℕ} :
    J ω ζ d h ρ c n x v Y j ↔
      ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N)
        (a g : ℝ), C d h n x v Y S Z ρ N y w f True ∧ d ^ (1 - ω / 100) ≤ ρ ∧ 0 < g ∧
        Broad ω ζ d h ρ n N v S Z f ∧ H d h n x v S Z ρ N y w f a c 0 g ∧
        ((1 ≤ j → d ^ ζ * (ρ / d) * N / n ≤ c) ∧ (2 ≤ j → ρ ≤ d ^ (ω / 100)) ∧
          (3 ≤ j → g ≤ d ^ (-ζ))) :=
  Iff.rfl

/-- The thin stage `Jt` with its witnesses made explicit. -/
theorem Jt_iff {ω ζ d h ρ c b : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} {j : ℕ} :
    Jt ω ζ d h ρ c b n x v Y j ↔
      ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N)
        (a g : ℝ), C d h n x v Y S Z ρ N y w f True ∧ d ^ (1 - ω / 100) ≤ ρ ∧ 0 < g ∧
        Broad ω ζ d h ρ n N v S Z f ∧ H d h n x v S Z ρ N y w f a c 0 g ∧ a < 2 * d ^ (1 - b) ∧
        ((1 ≤ j → d ^ ζ * (ρ / d) * N / n ≤ c) ∧ (2 ≤ j → ρ ≤ d ^ (ω / 100)) ∧
          (3 ≤ j → g ≤ d ^ (-ζ))) :=
  Iff.rfl

/-- Forgetting the thinness clause. -/
theorem J_of_Jt {ω ζ d h ρ c b : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} {j : ℕ}
    (hJ : Jt ω ζ d h ρ c b n x v Y j) : J ω ζ d h ρ c n x v Y j := by
  obtain ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hH, -, hstop⟩ := Jt_iff.1 hJ
  exact J_iff.2 ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hH, hstop⟩

/-- The volume gain survives smaller constants `κ ≤ κ'`, `α ≤ α'` (for `0 < d ≤ 1`). -/
theorem gain_bound_mono {σ ω α α' κ κ' d : ℝ} {n : ℕ} {Y : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 ≤ κ) (hκκ : κ ≤ κ') (hαα : α ≤ α')
    (hg : O (κ' * d ^ (ω - α') * (n * d ^ 2) * (n * d) ^ (-σ)) ≤ μ (⋃ i, Y i)) :
    O (κ * d ^ (ω - α) * (n * d ^ 2) * (n * d) ^ (-σ)) ≤ μ (⋃ i, Y i) :=
  (gain_mono hd hd1 hαα hκκ hκ).trans hg

/-- Shape check for `G`: its union clause reads `(⋃ j, H j) = ⋃ i ∈ S, Z i`. -/
theorem G_union {ω ζ d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} {b : Prop}
    (hG : G ω ζ d h ρ c n x v Y b) :
    ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (L : ℕ) (H : Fin L → Set V),
      (⋃ j, H j) = ⋃ i ∈ S, Z i := by
  obtain ⟨S, Z, a, L, z, e, H, -, -, -, -, -, -, -, hU, -⟩ := hG
  exact ⟨S, Z, L, H, hU⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
