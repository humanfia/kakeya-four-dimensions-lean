/-
Adapted from this LOT tree, obligation o168, session x0569, branch x0569,
Submission/Obl/k4_scalar_guarded_tangent_preparation/RawGeometry.lean.
The original source is work of this tree; its provenance comments are retained.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.ReferenceLaws

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

/-- The common original measured path before likelihood and duration
pruning. It retains full original layers and earlier true witnesses. It does
not assert the full-prior upper bounds, current duration floors or whole-tube
graph bounds of `TangentInput`. The reserve permits two later deletions. -/
def RawGeometry
    (p : ℕ → Code) (sample : ℕ → ℕ) (scale H buffer B : ℕ → ℝ)
    (M count : ℕ → ℕ) (node : (k : ℕ) → ℝ → Fin (count k))
    (depth time : (k : ℕ) → Fin (count k) → ℝ)
    (layers : (k : ℕ) → Fin (count k) → Layer ((p k).W (sample k)))
    (σ : (k : ℕ) → Fin ((p k).W (sample k)) → MeasureTheory.Measure Incidence)
    (d κ S : ℝ) : Prop :=
  let N₀ : ℕ → ℝ := fun k => (p k).N (sample k)
  let N : ℕ → ℝ := fun k => N₀ k ^ scale k
  let actual : ℕ → ℝ := fun k => (H k * Real.log (N₀ k)) ^ (k + 1)
  let loss : ℕ → ℝ := fun k => Real.log (actual k) / Real.log (N₀ k)
  let guard : ℕ → ℕ := fun k => 2 ^ ((M k + k + 1) ^ 2)
  (∀ k, Split.Exact (p k)) ∧
  (∀ k, 0 < scale k ∧ scale k ≤ 1 ∧ 2 ≤ H k ∧ 0 < buffer k ∧
    1 ≤ M k ∧ (p k).M ≤ M k ∧ (p k).D ≤ M k ∧ (p k).L ≤ (M k : ℝ) ∧
    (p k).K (sample k) ≤ H k ∧ (count k : ℝ) ≤ H k ∧
    H k ≤ N₀ k ^ (M k : ℝ) ∧ H k ≤ B k) ∧
  Filter.Tendsto scale Filter.atTop (nhds 0) ∧
  Filter.Tendsto buffer Filter.atTop (nhds 0) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, actual k ≤ N k ^ ε) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, scale k * R < (p k).L) ∧
  (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧
  (∀ k, 1 ≤ B k) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, B k ≤ N k ^ ε) ∧
  0 ≤ d ∧ d < 1 ∧ 0 < κ ∧ κ ≤ 1 ∧ 0 < S ∧
  (∀ k g, σ k g ≤ Split.mu (p k) (sample k) g) ∧
  (∀ k, ENNReal.ofReal (2 * (H k)⁻¹) ≤ ENNReal.ofReal (1 / 2 : ℝ) *
    ∑ g, ENNReal.ofReal ((p k).weight (sample k) g) * σ k g Set.univ) ∧
  (∀ k ℓ, let f := layers k ℓ
    0 ≤ depth k ℓ ∧ scale k * depth k ℓ < (p k).L ∧
    Split.ChartData (p k) (M k) (scale k * depth k ℓ) (p k).L
      (scale k * time k ℓ) (Real.log (H k) / Real.log (N₀ k)) true (sample k)
      f.T f.n f.world f.block f.assignment f.witness f.u f.v f.width f.graph f.list ∧
    (∀ i, (H k * (2 : ℝ) ^ f.T)⁻¹ ≤ f.width i) ∧
    (∀ g, σ k g {z | ∃ i, f.world i = g ∧ z ∈ f.witness i}ᶜ = 0) ∧
    N₀ k ^ |(p k).profile (scale k * depth k ℓ) - d * (scale k * depth k ℓ)| ≤ B k ∧
    N k ^ (κ * depth k ℓ) / B k ≤ (2 : ℝ) ^ f.T ∧
    (2 : ℝ) ^ f.T ≤ B k * N k ^ (κ * depth k ℓ) ∧
    (∀ g, MeasureTheory.Measure.map
        (pureObservation (N₀ k) (scale k * depth k ℓ)) (σ k g) ≤
      ENNReal.ofReal (B k * N₀ k ^ (-(p k).profile (scale k * depth k ℓ))) •
        (MeasureTheory.volume.prod MeasureTheory.Measure.count))) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R →
    N k ^ |depth k (node k s) - s| ≤ B k) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ r h : ℝ,
    R⁻¹ ≤ r → r ≤ R → h ≤ κ * r - buffer k →
    ¬Split.Chart (p k) (guard k) (scale k * r) (p k).L (scale k * h)
      (loss k) false (sample k))

end

end Submission.Obl.k4_scalar_guarded_entropic_path
