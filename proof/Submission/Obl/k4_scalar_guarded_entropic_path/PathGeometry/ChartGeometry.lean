/-
Adapted from this LOT tree, obligation o093, session x0535, commit 62576536,
Submission/Obl/k4_scalar_critical_path_terminal/ChartGeometry.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootTrueCharts

/-! The actual chart fields, independent of the tolerance, lists and proof.
The composition below records the geometry of ACCEPTED o167 RefStep lifting;
its ChartData proof is reused by IntermediateTrueLift, not rederived here. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartGeometry

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting
open IntermediateTrueLift TrueLiftChains

noncomputable section

structure Geometry (p : Code) (k : ℕ) where
  generation : ℕ
  count : ℕ
  world : Fin count → Fin (W p k)
  block : Fin count → Fin (2 ^ generation)
  assignment : Fin count → Set (ℕ × (Fin 5 → ℝ))
  selected : Fin count → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)
  center : Fin count → ℝ
  speed : Fin count → ℝ
  width : Fin count → ℝ
  polynomial : Fin count → MvPolynomial (Fin 2) ℝ

def ofChart {p : Code} {B k : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag k) : Geometry p k :=
  ⟨Q.T, Q.n, Q.γ, Q.j, Q.A, Q.C, Q.u, Q.v, Q.J, Q.P⟩

/-- Deterministic original geometry: full assigned-prior intersections
and positive width products use the SAME entire scalar coordinate maps. -/
def lift {p q : Code} {r b h : ℝ} (w : RefinementWitness p q r b h) (k : ℕ)
    (child : Geometry q k) : Geometry p (w.sample k) :=
  let S := w.refBody.step k
  { generation := w.T k + child.generation
    count := child.count
    world d := w.world k (child.world d)
    block d := jcomp (w.block k (child.world d)) (child.block d)
    assignment d := w.assignment k (child.world d) ∩
      w.trajectory k (child.world d) ⁻¹' child.assignment d
    selected d := w.selected k (child.world d) ∩ S.Φ (child.world d) ⁻¹' child.selected d
    center d := w.center k (child.world d) + w.width k (child.world d) * child.center d -
      w.width k (child.world d) * child.speed d * (S.t₀ (child.world d) / S.dt)
    speed d := w.speed k (child.world d) + w.width k (child.world d) * child.speed d / S.dt
    width d := w.width k (child.world d) * child.width d
    polynomial d := w.polynomial k (child.world d) + C (N p (w.sample k) ^ (-r)) *
      bind₁ (S.G (child.world d)) (child.polynomial d) }

theorem of_relaxChart {p : Code} {B B' k : ℕ} {r b h h' ε ε' : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag k) (hN : 1 ≤ N p k) (hB : B ≤ B')
    (hh : h ≤ h') (hε : ε ≤ ε') :
    ofChart (relaxChart Q hN hB hh hε) = ofChart Q := rfl

variable {p q : Code} {r b h : ℝ} (w : RefinementWitness p q r b h)
    (hp : Exact p) (hq : Exact q) {B₂ k : ℕ} {s h₂ ε₂ : ℝ}
    (Q : ChartW q B₂ s s h₂ ε₂ true k)
    (σ : ℕ → ℝ) (hsat : w.toRefinementData.Saturated r σ)
    (hrelative : f q s - f q 0 = f p (r + s) - f p r)
    (hr : 0 ≤ r) (hbs : b ≤ r + s) (hloss₁ : w.loss k ≤ 1)
    (hε₂ : 0 ≤ ε₂) {δ ε₃ : ℝ} (hσ : σ k ≤ δ)
    (hδ : 0 ≤ δ) (hε₃ : w.loss k + ε₂ + δ ≤ ε₃)
    (hε₃' : 4 * N p (w.sample k) ^ (w.loss k + ε₂) ≤ N p (w.sample k) ^ ε₃)

/-- Accepted TRUE lifting has EXACTLY this deterministic geometry. Only
its proof and lists depend on the declared tolerance. -/
theorem of_liftChartW :
    ofChart (liftChartW w hp hq Q σ hsat hrelative hr hbs hloss₁ hε₂ hσ hδ hε₃ hε₃') =
      lift w k (ofChart Q) := rfl

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartGeometry
