/- Adapted from same-tree o168/x0569-o196port, commit c22aeb8a. -/
/-
Adapted from: here:o168 (session x0569, branch x0569,
Submission/Obl/k4_scalar_guarded_tangent_preparation/Accepted.lean), renamed into the o196
namespace. Its own provenance comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.Guard
import Submission.Obl.k4_scalar_initial_true_horizon
import Submission.Obl.k4_scalar_chart_normalization
import Submission.Obl.k4_scalar_true_terminal_lifting

/-!
# The accepted chart calculus, and horizon gaps of refined parents

Initial (o130), Calculus (o131) and true terminal lifting (o167) are accepted. Through any
literal `Refinement p q r b h`, every true terminal cost of `q` lifts to a cost of `p`, so
`Horizon p ≤ h + Horizon q`. For a parent `q` normalized at a critical-path node of cost
`h ≈ κ r`, this is the horizon gap that the finite guard of the stage needs.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Submission.Obl.k4_scalar_linear_critical_extremizers

theorem accepted_initial : Split.Initial :=
  Submission.k4_scalar_initial_true_horizon

theorem accepted_calculus : Split.Calculus :=
  Submission.k4_scalar_chart_normalization accepted_initial

theorem accepted_lift : Submission.Obl.k4_scalar_true_terminal_lifting.LiftStatement :=
  Submission.k4_scalar_true_terminal_lifting

theorem horizon_nonneg' {p : Code} (hp : Split.Exact p) : 0 ≤ Split.Horizon p :=
  le_csInf ⟨p.L, accepted_initial p hp⟩ (fun _ hh => hh.1)

theorem horizon_le_cost' {p : Code} {h : ℝ} (hh : Split.Cost p h) : Split.Horizon p ≤ h :=
  csInf_le ⟨0, fun _ ha => ha.1⟩ hh

/-- **Horizon composition through a literal refinement.** -/
theorem horizon_le_add_of_refinement {p q : Code} {r b h : ℝ} (hp : Split.Exact p)
    (hq : Split.Exact q) (hr : 0 ≤ r) (hrL : r < p.L) (hrb : r ≤ b) (hbL : b ≤ p.L)
    (hh : 0 ≤ h) (hLq : q.L = p.L - r) (href : Split.Refinement p q r b h) :
    Split.Horizon p ≤ h + Split.Horizon q := by
  have hne : {a : ℝ | Split.Cost q a}.Nonempty := ⟨q.L, accepted_initial q hq⟩
  -- every cost of q lifts
  have hlift : ∀ a, Split.Cost q a → Split.Horizon p ≤ h + a := fun a ha =>
    horizon_le_cost' (accepted_lift p q r b h a hp hq hr hrL hrb hbL hh hLq href ha)
  by_contra hlt
  push Not at hlt
  have : Split.Horizon q < Split.Horizon p - h := by linarith
  obtain ⟨a, ha, hlt'⟩ := exists_lt_of_csInf_lt hne this
  have := hlift a ha
  linarith

/-- The horizon gap of a parent refined at a node of cost close to `κ r`. -/
theorem horizon_gap_of_refinement {p q : Code} {r b h κ ε₁ ε₂ : ℝ} (hp : Split.Exact p)
    (hq : Split.Exact q) (hr : 0 ≤ r) (hrL : r < p.L) (hrb : r ≤ b) (hbL : b ≤ p.L)
    (hh : 0 ≤ h) (hLq : q.L = p.L - r) (href : Split.Refinement p q r b h)
    (hHp : κ * p.L - ε₁ ≤ Split.Horizon p) (hcost : h ≤ κ * r + ε₂) :
    κ * q.L - (ε₁ + ε₂) ≤ Split.Horizon q := by
  have := horizon_le_add_of_refinement hp hq hr hrL hrb hbL hh hLq href
  rw [hLq]
  nlinarith

end Submission.Obl.k4_scalar_guarded_entropic_path

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Submission.Obl.k4_scalar_linear_critical_extremizers
open Filter

/-- **The stage guard of a refined window parent.** A parent `q` refined from an exact
problem `p` in the extremal class at a node of cost at most `κ r + ε₂`, where `p` has
horizon at least `κ L - ε₁`, inherits the class and a horizon gap; hence the scaled guard
holds at all late samples of `q` for every fixed complexity. -/
theorem refined_parent_guard {D S₀ η b : ℝ} (hclass : ClassBound D S₀ η b)
    {p q : Code} {r b' h κ ε₁ ε₂ : ℝ} (hp : Split.Exact p) (hq : Split.Exact q)
    (hr : 0 ≤ r) (hrL : r < p.L) (hrb : r ≤ b') (hbL : b' ≤ p.L) (hh : 0 ≤ h)
    (hLq : q.L = p.L - r) (href : Split.Refinement p q r b' h)
    (hqd : q.d ≤ D) (hqS : q.S = S₀) (hqU : q.U = η * q.L)
    (hHp : κ * p.L - ε₁ ≤ Split.Horizon p) (hcost : h ≤ κ * r + ε₂)
    {R scale buffer : ℝ} (hb : 0 < b) (hscale : 0 < scale) (hR : 1 ≤ R)
    (hbuffer : 0 < buffer) (hRL : scale * R < q.L)
    (hκb : |κ - b| * R ≤ buffer / 4)
    (hgap : |κ - b| * q.L + (ε₁ + ε₂) < scale * buffer / 8) (B : ℕ) (hB : 1 ≤ B)
    (loss : ℕ → ℝ) (hloss : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, loss m ≤ ε) :
    ∀ᶠ m in atTop, ∀ r h : ℝ, R⁻¹ ≤ r → r ≤ R → h ≤ κ * r - buffer →
      ¬Split.Chart q B (scale * r) q.L (scale * h) (loss m) false m := by
  have hgapq := horizon_gap_of_refinement hp hq hr hrL hrb hbL hh hLq href hHp hcost
  have hqL0 : 0 ≤ q.L := (exact_length_pos hq).le
  have hgap' : b * q.L - scale * buffer / 8 < Split.Horizon q := by
    have h1 : b * q.L ≤ κ * q.L + |κ - b| * q.L := by
      have : (b - κ) * q.L ≤ |κ - b| * q.L :=
        mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; exact le_abs_self _) hqL0
      nlinarith
    linarith
  exact eventually_scaled_guard accepted_calculus hclass hq hqd hqS hqU hb hscale hR
    hbuffer hRL hκb hgap' B hB loss hloss

end Submission.Obl.k4_scalar_guarded_entropic_path
