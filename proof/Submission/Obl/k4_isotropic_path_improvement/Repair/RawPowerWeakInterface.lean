-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawPowerWeakInterface.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawWeakInterface

/-! The raw weak interface of o204/x0733 ba2d6042 with one relaxation:
narrow atlas mass may lose a power equal to the requested narrow-atlas slack.
All raw candidate, path, uniform-grid and format requirements are unchanged.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawPowerWeakInterface
open RawWeakInterface
set_option linter.unusedVariables false

def narrow : ℝ → ℝ → (W:ℕ) → (Fin W → ℝ) → (Fin W → MeasureTheory.Measure Ln) →
      (Fin W→Set Ev)→(Fin W→ℝ)→ℕ→(ℕ→ℝ)→(ℕ→ℝ)→(ℕ→ℕ)→
      (ℕ→ℝ)→ℝ→ℝ→ℝ→ℕ→ℕ→ℝ→(C:ℕ)→(Fin C→ℕ)→(Fin C→Fin W)→
      (Fin C→ℕ)→(Fin C→Set Ln)→(Fin C→Set Ev)→(Fin W→Set Ev)→Prop := (fun Nk L W ω ν E B m s r T nw gain u0 κ Mw Dw α C lev γ j A F H =>
      ∃ (i:ℕ) (β:ℝ), i < m ∧ 1/4 ≤ s i ∧ s i ≤ 1/2 ∧
      u0 ≤ β ∧ β ≤ 4*gain ∧
      atlas Nk L W ω ν E B Mw Dw α (r i) (T i)
        (fun Q=> |Matrix.det Q| *(4:ℝ)^T i≤Nk^(-(nw i+β*L)))
        (fun w jt At Ft known=>known ∧ ∃b:Fin C,
          lev b=i ∧ γ b=w ∧ j b=(jt:ℕ) ∧ At⊆A b ∧ Ft⊆F b)
        (ENNReal.ofReal ((κ*Nk^α)⁻¹/8))
        (fun w F=>((ν w).prod MeasureTheory.volume) (F∩H w)))

def weakds : ℕ→ ℕ→ ℕ→ ℝ→ ℝ→ ℝ→ ℝ→ ℝ→ ℕ→ (ℕ→ ℝ)→ ℝ→ ℝ→ ℝ→Prop := (fun cc J D d₁ κ₁ S η ρ m s gain δ₀ u0=>∀N K L d W ω ν E P B f g G,pb N K L d S η W ω ν E P B f g G→ (∀r:ℝ,0≤ r→ r≤ L→ |f r - f 0 - d₁*r|≤ δ₀*L)→ ∀Mp Dp:ℕ,∃M₀ D₀:ℕ,∀Mi Di:ℕ,M₀≤Mi→D₀≤Di→∀τ:ℝ,0 < τ→∀α:ℝ,0<α→α≤1→ ∃σ:ℝ,0 < σ∧∃k₀:ℕ,∀k,k₀≤ k→ ∀r T nw κ C lev par γ j c u Q R A F lst,path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst→ ∀H:Fin (W k)→ Set Ev,(∀w,MeasurableSet (H w)∧H w ⊆ {p |∃b:Fin C,lev b=m - 1∧γ b=w∧p∈F b})→ ENNReal.ofReal (κ⁻¹/2)≤ ∑ w,ENNReal.ofReal (ω k w)*((ν k w).prod MeasureTheory.volume) (H w)→ (wi (N k) L (W k) (ω k) (ν k) (E k) (B k) m r T nw gain Mi Di τ∨cd cc J D (N k) L (W k) (ν k) (B k) Mi d₁ ρ gain τ r T C lev γ j A H)∨narrow (N k) L (W k) (ω k) (ν k) (E k) (B k) m s r T nw gain u0 κ M₀ D₀ α C lev γ j A F H)

def WeakAssertion : Prop := mk→ ∀cc:ℕ,1≤ cc→ ∀d₁ κ₁ S η ρ:ℝ,0≤ d₁→ d₁ < 1→ 0 < κ₁→ κ₁≤ 1→ 0 < S→ 0 < η→ 0 < ρ→ d₁+ρ < 1→∀e0:ℝ,0<e0→∃D:ℕ,∀J:ℕ,1≤ J→ (fun (D J:ℕ)=>∀(A:ℝ),2≤ A→ ∀(f:P3→ ℝ),exf D f→ (∀(E:Set P3) (v:ℝ),MeasurableSet E→ E ⊆ Metric.closedBall (0:P3) 1→ ENNReal.ofReal A⁻¹≤ MeasureTheory.volume E→ 0≤ v→ (∀x∈E,|f x|≤ v)→ ∀j:ℕ,j≤ 6→ ∀x∈Metric.closedBall (0:P3) 2,‖iteratedFDeriv ℝ j f x‖≤ A^J*v)∧(∀(c:ℝ) (L:P3→L[ℝ] ℝ) (ε:ℝ),0 < ε→ (∀x∈Metric.closedBall (0:P3) 1,|f x - c - L x|≤ ε)→ ∀j:ℕ,2≤ j→ j≤ 6→ ∀x∈Metric.closedBall (0:P3) 2,‖iteratedFDeriv ℝ j f x‖≤ A^J*ε)) D J→ ∃(m:ℕ) (s:ℕ→ℝ) (gain δ₀ u0:ℝ),grid κ₁ ρ m s gain δ₀ u0 ∧ gain≤e0 ∧ weakds cc J D d₁ κ₁ S η ρ m s gain δ₀ u0

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawPowerWeakInterface
