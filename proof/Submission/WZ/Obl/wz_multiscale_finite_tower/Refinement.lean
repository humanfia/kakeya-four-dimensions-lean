-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Refinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Tower

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The geometric alternative, before imposing a cutoff on the bottom scale. -/
def RetainedTower (d ε g : ℝ) (B n : ℕ) (Y : Fin n → Set Space) : Prop :=
  ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (M L : ℝ),
    Admissible d ε M L m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧
    ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j) ∧
    Tower false d (d ^ (-ε)) g B m x' v'

/-- A larger error budget weakens both density and retained mass requirements. -/
theorem RetainedTower.mono {d ε ε' g g' : ℝ} {B B' n : ℕ} {Y : Fin n → Set Space}
    (h : RetainedTower d ε g B n Y) (hd : 0 < d) (hd1 : d ≤ 1)
    (hε : ε ≤ ε') (hg : g ≤ g') (hB : B ≤ B') : RetainedTower d ε' g' B' n Y := by
  obtain ⟨m, x, v, Z, M, L, hA, hsub, hmass, htower⟩ := h
  refine ⟨m, x, v, Z, M, L, hA.mono hd hd1 hε le_rfl le_rfl, hsub, ?_, ?_⟩
  · apply le_trans _ hmass
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 hε)) (by positivity)
  · exact htower.mono hd hd1
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hε)) hg hB

/-- Composing a mass-retaining refinement adds its exponent loss. -/
theorem RetainedTower.precompose {d ε ζ g : ℝ} {B n m : ℕ}
    {Y : Fin n → Set Space} {Z : Fin m → Set Space}
    (h : RetainedTower d ε g B m Z) (hd : 0 < d) (hd1 : d ≤ 1) (hζ : 0 ≤ ζ)
    (hsub : (⋃ j, Z j) ⊆ (⋃ i, Y i))
    (hmass : ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Z j)) :
    RetainedTower d (ε + ζ) g B n Y := by
  obtain ⟨k, x, v, W, M, L, hA, hWZ, hWmass, htower⟩ := h
  refine ⟨k, x, v, W, M, L, hA.mono hd hd1 (le_add_of_nonneg_right hζ) le_rfl le_rfl,
    hWZ.trans hsub, ?_, ?_⟩
  · calc
      ENNReal.ofReal (d ^ (ε + ζ)) * (∑ i, volume (Y i)) =
          ENNReal.ofReal (d ^ ε) * (ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i))) := by
        rw [Real.rpow_add hd, ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _), mul_assoc]
      _ ≤ ENNReal.ofReal (d ^ ε) * (∑ j, volume (Z j)) := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ ∑ j, volume (W j) := hWmass
  · exact htower.mono hd hd1
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)) le_rfl le_rfl

end WangZahlLot.Obl.wz_multiscale_finite_tower
