-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CellPrismRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CellPrismAssembly

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory Set

/-- Increase the permitted power loss without changing any geometric data. -/
def CellPrismFamily.weaken {δ r ρ c ε ζ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} {C : Fin N → Set V}
    {q : Fin N → V} {y w : V}
    (R : CellPrismFamily δ r ρ c ε x v Y C q y w)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 ≤ ρ) (hc : 0 ≤ c) (hεζ : ε ≤ ζ) :
    CellPrismFamily δ r ρ c ζ x v Y C q y w :=
  { R with
    retains := (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hεζ)) _).trans R.retains
    density := by
      apply le_trans _ R.density
      apply ENNReal.ofReal_le_ofReal
      have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hεζ
      gcongr
  }

/-- Transfer a prism family through a mass-retaining refinement of its input shading. -/
def CellPrismFamily.rebase {δ r ρ c ε τ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y W : Fin n → Set V} {C : Fin N → Set V}
    {q : Fin N → V} {y w : V}
    (R : CellPrismFamily δ r ρ c ε x v W C q y w)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 ≤ ρ) (hc : 0 ≤ c) (hτ : 0 ≤ τ)
    (hWY : ∀ i, W i ⊆ Y i)
    (hkeep : o (δ ^ τ) * (∑ i, μ (Y i)) ≤ ∑ i, μ (W i)) :
    CellPrismFamily δ r ρ c (ε + τ) x v Y C q y w :=
  { R with
    refines := fun i => ⟨(R.refines i).1, (R.refines i).2.trans (hWY i)⟩
    retains := by
      calc
        _ = o (δ ^ ε) * (o (δ ^ τ) * ∑ i, μ (Y i)) := by
          change ENNReal.ofReal _ * _ = ENNReal.ofReal _ * (ENNReal.ofReal _ * _)
          rw [Real.rpow_add hδ, ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), mul_assoc]
        _ ≤ o (δ ^ ε) * ∑ i, μ (W i) := mul_le_mul_right hkeep _
        _ ≤ _ := R.retains
    density := by
      apply le_trans _ R.density
      apply ENNReal.ofReal_le_ofReal
      have hp : δ ^ (ε + τ) ≤ δ ^ ε :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      gcongr
  }

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
