import Submission.Obl.k4_scalar_candidate_original_return.Scales

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_candidate_original_return.PreparedData

open MeasureTheory Filter
open scoped Topology

variable {a : PreparedData} (ha : a.Valid)
include ha

lemma Valid.exact (k : ℕ) : Exact (a.p k) := ha.1 k

lemma Valid.bounds (k : ℕ) :
    0 < a.sc k ∧ a.sc k ≤ 1 ∧ 2 ≤ a.H k ∧ 0 < a.bf k ∧ 1 ≤ a.rM k ∧
    M (a.p k) ≤ a.rM k ∧ D (a.p k) ≤ a.rM k ∧ L (a.p k) ≤ (a.rM k : ℝ) ∧
    K (a.p k) (a.sm k) ≤ a.H k ∧ (a.ct k : ℝ) ≤ a.H k ∧
    a.H k ≤ a.original k ^ (a.rM k : ℝ) := ha.2.1 k

lemma Valid.unit_tends : Tendsto a.sc atTop (𝓝 0) := ha.2.2.1
lemma Valid.buffer_tends : Tendsto a.bf atTop (𝓝 0) := ha.2.2.2.1
lemma Valid.allowance_subpower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, a.allowance k ≤ a.tangent k ^ ε := ha.2.2.2.2.1 ε hε

lemma Valid.range (R : ℝ) (hR : 1 < R) :
    ∀ᶠ k in atTop, a.sc k * R < L (a.p k) := ha.2.2.2.2.2.1 R hR

lemma Valid.rho_le (k : ℕ) (g : Fin (W (a.p k) (a.sm k))) :
    a.ρ k g ≤ mu (a.p k) (a.sm k) g := ha.2.2.2.2.2.2.1 k g

lemma Valid.weighted_mass (k : ℕ) : ENNReal.ofReal ((a.H k)⁻¹) ≤
    ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) * a.ρ k g Set.univ :=
  ha.2.2.2.2.2.2.2.1 k

lemma Valid.layer (k : ℕ) (ℓ : Fin (a.ct k)) :
    let q := a.ls k ℓ
    0 ≤ a.dp k ℓ ∧ a.sc k * a.dp k ℓ < L (a.p k) ∧
    ChartData (a.p k) (a.rM k) (a.sc k * a.dp k ℓ) (L (a.p k))
      (a.sc k * a.tm k ℓ) (Real.log (a.H k) / Real.log (a.original k)) true (a.sm k)
      q.T q.n q.world q.time q.prior q.selected q.u q.v q.width q.poly q.lists ∧
    (∀ i, (a.H k * (2 : ℝ) ^ q.T)⁻¹ ≤ q.width i) ∧
    (∀ g, a.ρ k g {z | ∃ i, q.world i = g ∧ z ∈ q.selected i}ᶜ = 0) :=
  ha.2.2.2.2.2.2.2.2.1 k ℓ

lemma Valid.tangent_input :
    TangentInput a.tangent a.rK a.rd a.κ a.rS (fun k => W (a.p k) (a.sm k))
      (fun k => ω (a.p k) (a.sm k)) (fun k => ν (a.p k) (a.sm k)) a.ρ a.π
      (fun k s => (a.ls k (a.nd k s)).T) (fun k s => (a.ls k (a.nd k s)).n)
      (fun k s => (a.ls k (a.nd k s)).world) (fun k s => (a.ls k (a.nd k s)).time)
      (fun k s => (a.ls k (a.nd k s)).prior) (fun k s => (a.ls k (a.nd k s)).u)
      (fun k s => (a.ls k (a.nd k s)).v) (fun k s => (a.ls k (a.nd k s)).poly) :=
  ha.2.2.2.2.2.2.2.2.2.1

lemma Valid.excluded (R : ℝ) (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ r h : ℝ,
      R⁻¹ ≤ r → r ≤ R → h ≤ a.κ * r - a.bf k →
      ¬Chart (a.p k) (a.guard k) (a.sc k * r) (L (a.p k))
        (a.sc k * h) (a.loss k) false (a.sm k) :=
  ha.2.2.2.2.2.2.2.2.2.2 R hR

/-- Extract exactly the numerical control carried by the prepared witness. -/
noncomputable def Valid.scales : ScaleControl where
  original := a.original
  unit := a.sc
  factor := a.H
  original_ge_two k := (ha.exact k).1.1 (a.sm k)
  unit_pos k := (ha.bounds k).1
  unit_le_one k := (ha.bounds k).2.1
  factor_ge_two k := (ha.bounds k).2.2.1
  tangent_tends := ha.tangent_input.2.1
  allowance_subpower := ha.allowance_subpower

end Submission.Obl.k4_scalar_candidate_original_return.PreparedData
