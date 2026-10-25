-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawNarrowMassBridge.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawPowerWeakInterface
import Submission.Obl.k4_isotropic_path_improvement.Repair.NarrowMassComparison
import Submission.Obl.k4_isotropic_path_improvement.Repair.PolynomialNarrowMass

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawNarrowMassBridge

open MeasureTheory RawWeakInterface

theorem atlas_floor_mono
    {Nk L : ℝ} {W Mi Di T : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {α r : ℝ} {extra : Matrix (Fin 2) (Fin 2) ℝ → Prop}
    {aux : Fin W → Fin (2 ^ T) → Set Ln → Set Ev → Prop → Prop}
    {mass : Fin W → Set Ev → ENNReal} {a b : ENNReal}
    (hab : a ≤ b) (ha : atlas Nk L W ω ν E B Mi Di α r T extra aux b mass) :
    atlas Nk L W ω ν E B Mi Di α r T extra aux a mass := by
  obtain ⟨C, γ, j, c, u, Q, R, A, F, lst, hcard, hdisj, hlist, hchart, hmass⟩ := ha
  exact ⟨C, γ, j, c, u, Q, R, A, F, lst, hcard, hdisj, hlist, hchart, hab.trans hmass⟩

/-- A constant-fraction original atlas gives exactly the power-mass raw
narrow alternative. Every chart, old ancestor, event, and list is retained. -/
theorem narrow_of_constant_fraction
    {Nk L : ℝ} {W m Mw Dw C : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {s r nw : ℕ → ℝ} {T : ℕ → ℕ} {gain u₀ κ α fraction : ℝ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {A : Fin C → Set Ln} {F : Fin C → Set Ev} {H : Fin W → Set Ev}
    {i : ℕ} {β : ℝ}
    (hi : i < m) (hsi : 1 / 4 ≤ s i) (hsi' : s i ≤ 1 / 2)
    (hβ : u₀ ≤ β) (hβ' : β ≤ 4 * gain)
    (hκ : 0 ≤ κ) (hfraction : 0 < fraction) (hlarge : 8 / fraction ≤ Nk ^ α)
    (ha : atlas Nk L W ω ν E B Mw Dw α (r i) (T i)
      (fun Q => |Q.det| * (4 : ℝ) ^ T i ≤ Nk ^ (-(nw i + β * L)))
      (fun w jt At Ft known => known ∧ ∃ b : Fin C,
        lev b = i ∧ γ b = w ∧ j b = (jt : ℕ) ∧ At ⊆ A b ∧ Ft ⊆ F b)
      (ENNReal.ofReal (κ⁻¹ * fraction / 64))
      (fun w Ft => ((ν w).prod volume) (Ft ∩ H w))) :
    RawPowerWeakInterface.narrow Nk L W ω ν E B m s r T nw gain u₀ κ
      Mw Dw α C lev γ j A F H := by
  refine ⟨i, β, hi, hsi, hsi', hβ, hβ', ?_⟩
  exact atlas_floor_mono (ENNReal.ofReal_le_ofReal
    (NarrowMassComparison.kappa_power_mass_le_fraction hκ hfraction hlarge)) ha

/-- A fixed polynomial loss in the path factor is sufficient as well. -/
theorem narrow_of_polynomial_fraction
    {Nk L : ℝ} {W m Mw Dw C : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {s r nw : ℕ → ℝ} {T : ℕ → ℕ} {gain u₀ κ α fraction : ℝ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {A : Fin C → Set Ln} {F : Fin C → Set Ev} {H : Fin W → Set Ev}
    {i : ℕ} {β : ℝ} (p : ℕ)
    (hi : i < m) (hsi : 1 / 4 ≤ s i) (hsi' : s i ≤ 1 / 2)
    (hβ : u₀ ≤ β) (hβ' : β ≤ 4 * gain)
    (hκ : 0 < κ) (hfraction : 0 < fraction)
    (hlarge : 8 * κ ^ p / fraction ≤ Nk ^ α)
    (ha : atlas Nk L W ω ν E B Mw Dw α (r i) (T i)
      (fun Q => |Q.det| * (4 : ℝ) ^ T i ≤ Nk ^ (-(nw i + β * L)))
      (fun w jt At Ft known => known ∧ ∃ b : Fin C,
        lev b = i ∧ γ b = w ∧ j b = (jt : ℕ) ∧ At ⊆ A b ∧ Ft ⊆ F b)
      (ENNReal.ofReal ((κ ^ (p + 1))⁻¹ * fraction / 64))
      (fun w Ft => ((ν w).prod volume) (Ft ∩ H w))) :
    RawPowerWeakInterface.narrow Nk L W ω ν E B m s r T nw gain u₀ κ
      Mw Dw α C lev γ j A F H := by
  refine ⟨i, β, hi, hsi, hsi', hβ, hβ', ?_⟩
  exact atlas_floor_mono (ENNReal.ofReal_le_ofReal
    (PolynomialNarrowMass.kappa_power_mass_le_polynomial_fraction p hκ hfraction hlarge)) ha

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawNarrowMassBridge
