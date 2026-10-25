-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawStagedWeakInterface.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawWeakInterface
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawNarrowMassBridge

/-! The staged weak-discovery interface of this LOT tree's frozen o265.
Its relation degree is chosen before the jet order and requested gain bound.
No unaccepted obligation is imported or asserted here. -/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawStagedWeakInterface

open RawWeakInterface

def JetBound (D J : ℕ) : Prop :=
  ∀ A : ℝ, 2 ≤ A → ∀ f : P3 → ℝ, exf D f →
    (∀ (E : Set P3) (v : ℝ), MeasurableSet E →
      E ⊆ Metric.closedBall (0 : P3) 1 → ENNReal.ofReal A⁻¹ ≤ MeasureTheory.volume E →
      0 ≤ v → (∀ x ∈ E, |f x| ≤ v) → ∀ j : ℕ, j ≤ 6 →
      ∀ x ∈ Metric.closedBall (0 : P3) 2, ‖iteratedFDeriv ℝ j f x‖ ≤ A ^ J * v) ∧
    (∀ (c : ℝ) (L : P3 →L[ℝ] ℝ) (ε : ℝ), 0 < ε →
      (∀ x ∈ Metric.closedBall (0 : P3) 1, |f x - c - L x| ≤ ε) →
      ∀ j : ℕ, 2 ≤ j → j ≤ 6 → ∀ x ∈ Metric.closedBall (0 : P3) 2,
        ‖iteratedFDeriv ℝ j f x‖ ≤ A ^ J * ε)

def StagedWeakAssertion : Prop :=
  mk → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < S → 0 < η →
    0 < ρ → d₁ + ρ < 1 → ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧
    ∀ J : ℕ, 1 ≤ J → JetBound D J → ∀ e₀ : ℝ, 0 < e₀ →
    ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u₀ : ℝ),
      grid κ₁ ρ m s gain δ₀ u₀ ∧ gain ≤ e₀ ∧
        weakds cc J D d₁ κ₁ S η ρ m s gain δ₀ u₀

/-- Frozen staged discovery alone supplies the weak interface used by the
width-margin repair. Its narrow branch need not be converted to a potential. -/
theorem weak_of_staged (h : StagedWeakAssertion) : RawWeakInterface.WeakAssertion := by
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ e₀ he₀
  obtain ⟨D, _, hD⟩ := h hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ 0
  exact ⟨D, fun J hJ hjets => hD J hJ hjets e₀ he₀⟩

/-- The same staged theorem also supplies the weaker power-mass interface. -/
theorem power_weak_of_staged (h : StagedWeakAssertion) :
    RawPowerWeakInterface.WeakAssertion := by
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ e₀ he₀
  obtain ⟨D, hD⟩ := weak_of_staged h hmk cc hcc d₁ κ₁ S η ρ
    hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ e₀ he₀
  refine ⟨D, ?_⟩
  intro J hJ hjets
  obtain ⟨m, s, gain, δ₀, u₀, hgrid, hgain, hdiscovery⟩ := hD J hJ hjets
  refine ⟨m, s, gain, δ₀, u₀, hgrid, hgain, ?_⟩
  intro N K L d W ω ν E P B f g G hproblem hprofile Mp Dp
  obtain ⟨M₀, D₀, hstage⟩ := hdiscovery N K L d W ω ν E P B f g G
    hproblem hprofile Mp Dp
  refine ⟨M₀, D₀, ?_⟩
  intro Mi Di hMi hDi τ hτ α hα hα1
  obtain ⟨σ, hσ, k₀, hlate⟩ := hstage Mi Di hMi hDi τ hτ α hα hα1
  refine ⟨σ, hσ, k₀, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass
  rcases hlate k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass with
    hgood | hnarrow
  · exact Or.inl hgood
  · apply Or.inr
    obtain ⟨i, β, hi, hsi, hsi', hβ, hβ', hatlas⟩ := hnarrow
    refine ⟨i, β, hi, hsi, hsi', hβ, hβ', ?_⟩
    have hN : 1 ≤ N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hproblem.1 k)
    have hκ : 0 < κ := lt_of_lt_of_le zero_lt_one hpath.1
    have hpower : 1 ≤ N k ^ α := Real.one_le_rpow hN hα.le
    have hprod : κ ≤ κ * N k ^ α := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower hκ.le
    have hcompare : (κ * N k ^ α)⁻¹ / 8 ≤ κ⁻¹ / 8 :=
      div_le_div_of_nonneg_right (inv_anti₀ hκ hprod) (by norm_num)
    exact RawNarrowMassBridge.atlas_floor_mono (ENNReal.ofReal_le_ofReal hcompare) hatlas

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawStagedWeakInterface
