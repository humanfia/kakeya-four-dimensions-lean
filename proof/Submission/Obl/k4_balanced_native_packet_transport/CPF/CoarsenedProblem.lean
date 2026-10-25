/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/CoarsenedProblem.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.AngularInheritance

/-! Truncate an exact Problem to a smaller depth. The old data and relative
profile are retained; only the joint density and the asserted cap change. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

noncomputable def Data.coarsen (p : Data) (r d : ℝ) : Data :=
  {p with L := r, d := d, G := coarsenedAngularDensity p r}

/-- Every clause of Problem, including the same angular parameters, holds at a
smaller depth whenever the retained profile satisfies the new endpoint cap. -/
theorem Data.Valid.coarsen {p : Data} (hp : p.Valid) {r d : ℝ}
    (hr : 0 < r) (hrL : r ≤ p.L) (hd : 0 < d) (hd1 : d < 1)
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ r → p.f r - p.f s ≤ d * (r - s)) :
    (p.coarsen r d).Valid := by
  have hp₀ := hp
  rcases hp with ⟨hN, hNt, hK, _, _, _, hS, hη, htemp, hg, _, hprofile, htyp, _, _⟩
  refine ⟨hN, hNt, hK, hr, hd, hd1, hS, hη, htemp, ?_, ?_, ?_, ?_, hcap, ?_⟩
  · intro k γ s hs hsr
    exact hg k γ s hs (hsr.trans hrL)
  · intro k γ u hu huη
    exact ⟨measurable_coarsenedAngularDensity p r k γ u,
      hp₀.coarsened_angular_law hr.le hrL k γ u⟩
  · intro s t hs hst htr
    exact hprofile s t hs hst (htr.trans hrL)
  · intro s τ hs hsr hτ
    exact htyp s τ hs (hsr.trans hrL) hτ
  · intro u τ hu huη hτ
    exact hp₀.angular_typical_at_depth hr.le hrL hu
      (huη.trans (mul_le_mul_of_nonneg_left hrL hη.le)) hτ

/-- A coarsened chart system already uses the original native trajectories,
assignments, events, and polynomials. Only its record parameter changes. -/
def Atlas.fromCoarsened (p : Data) (r d : ℝ) {k : ℕ}
    (a : Atlas (p.coarsen r d) k) : Atlas p k where
  κ := a.κ
  T := a.T
  C := a.C
  γ := a.γ
  j := a.j
  c := a.c
  u := a.u
  Q := a.Q
  R := a.R
  A := a.A
  F := a.F

theorem Atlas.fromCoarsened_true (p : Data) (r d : ℝ) {k M D : ℕ}
    (a : Atlas (p.coarsen r d) k) (s : ℝ) :
    (Atlas.fromCoarsened p r d a).TrueAt M D s ↔ a.TrueAt M D s := Iff.rfl

/-- Terminal systems of the coarsened problem give genuine systems of the
original problem at the retained depth, with the identical format and slack. -/
theorem true_systems_of_coarsened_terminal {p : Data} {r d h : ℝ}
    (ht : Terminal (p.coarsen r d) h) :
    ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
      ∃ a : Atlas p k, 1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
        (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.TrueAt M D r := by
  obtain ⟨M, D, ht⟩ := ht
  refine ⟨M, D, fun ε hε => (ht ε hε).mono fun k hk => ?_⟩
  obtain ⟨a, hκ, hK, hε, hT, htrue⟩ := hk
  exact ⟨Atlas.fromCoarsened p r d a, hκ, hK, hε, hT, htrue⟩

end Submission.Obl.k4_balanced_native_packet_transport.CPF
