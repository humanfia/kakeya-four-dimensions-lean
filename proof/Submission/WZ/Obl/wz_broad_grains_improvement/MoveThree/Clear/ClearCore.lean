-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear.ClearCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Clear/ClearCore.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Defs

/-!
Error-monotonicity lemmas for the endpoint-clearance chain, ported (namespace adjusted,
`J` with thinness parameter renamed to this desk's `Jt`) from the o169 file
`WangZahlLot/Obl/wz_move_three_wide_grains_core/Core.lean` (branch x0641), which adapted
x0450's `Core.lean` of o153. The frozen predicates come from `Core`/`Defs`.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear

/-- `d ^ h' ≤ d ^ h` and `d ^ (-h) ≤ d ^ (-h')` for `0 < d ≤ 1`, `h ≤ h'`. -/
theorem rpow_err_le {d h h' : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h') :
    d ^ h' ≤ d ^ h ∧ d ^ (-h) ≤ d ^ (-h') :=
  ⟨Real.rpow_le_rpow_of_exponent_ge hd hd1 hh,
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hh)⟩

/-- Increasing the error weakens the original-family admissibility assumptions. -/
theorem admissible_mono {d h h' : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (ha : A d h (d^(-h)) (d^(-h)) n x v Y) :
    A d h' (d^(-h')) (d^(-h')) n x v Y := by
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1 hh
  have hi := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hh)
  rcases ha with ⟨hn, ht, hx, hm, hk, hf⟩
  refine ⟨hn, ht, hx, le_trans ?_ hm, ?_, ?_⟩
  · apply ENNReal.ofReal_le_ofReal
    gcongr
  · intro W hW
    exact (hk W hW).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal hi) _)
  · intro u t r hu hr
    apply (hf u t r hu hr).trans
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg n)

/-- All cover and retained-mass clauses are monotone in the error. -/
theorem cover_mono {d h h' ρ : ℝ} {n N : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {S : Finset (Fin n)} {y w : Fin N → V}
    {f : Fin n → Fin N} {b : Prop} (hd : 0 < d) (hd1 : d ≤ 1)
    (hh : h ≤ h') (hc : C d h n x v Y S Z ρ N y w f b) :
    C d h' n x v Y S Z ρ N y w f b := by
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1 hh
  have hi := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hh)
  rcases hc with ⟨hz, hm, hw, ht, hf, hb, hbal, hx, hov⟩
  refine ⟨hz, le_trans ?_ hm, hw, ht, ?_, hb, ?_, hx, ?_⟩
  · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hp) _
  · intro u t r hu hr
    apply (hf u t r hu hr).trans
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg N)
  · intro k k'
    exact (hbal k k').trans
      (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _))
  · intro i hiS
    exact (hov i hiS).trans hi

/-- Only the grain-mass lower bound depends on the error. -/
theorem grains_mono {d h h' ρ a c b g : ℝ} {n N : ℕ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (hhg : H d h n x v S Z ρ N y w f a c b g) :
    H d h' n x v S Z ρ N y w f a c b g := by
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1 hh
  rcases hhg with ⟨L, z, e, G, γ, m, hda, hab, hbc, hc1,
    hgeom, hdisj, hunion, hmass, hmult, hcross, hb, hcount⟩
  have ha : 0 ≤ a := (hd.trans_le hda).le
  have hrc : 0 ≤ ρ*c := ha.trans hab
  have hc : 0 ≤ c := hrc.trans hbc
  refine ⟨L, z, e, G, γ, m, hda, hab, hbc, hc1,
    hgeom, hdisj, hunion, le_trans ?_ hmass, hmult, hcross, hb, hcount⟩
  apply ENNReal.ofReal_le_ofReal
  gcongr

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear
