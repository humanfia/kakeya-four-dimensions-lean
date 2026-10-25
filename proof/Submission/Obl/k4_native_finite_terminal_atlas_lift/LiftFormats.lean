/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/LiftFormats.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftAtlas

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

namespace Remainder

variable {p q : Data} {r h w : ℝ} (rem : Remainder p q r h w)

theorem liftAtlas_A_measurable {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (b : Fin a.C) : MeasurableSet ((rem.liftAtlas k a).A b) := by
  have hp := (rem.parent_valid k).2.2 (rem.parentIndex k (a.γ b))
  rcases hp with ⟨_, _, _, _, _, _, hA₀, _⟩
  have hc := ha.2.2.1 b
  rcases hc with ⟨_, _, _, _, _, _, hA₁, _⟩
  exact hA₀.inter ((rem.coefficient_map k (a.γ b)).measurable hA₁)

/-- Full-assignment pullback adds only the parent and child sign tables. -/
theorem liftAtlas_assignment_format {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (b : Fin a.C) (i : ℕ) :
    fmt 6 (p.N (rem.φ k) ^ rem.M + q.N k ^ M) (max rem.D D)
      {z | (i, z) ∈ (rem.liftAtlas k a).A b} := by
  have hp := (rem.parent_valid k).2.2 (rem.parentIndex k (a.γ b))
  rcases hp with ⟨_, _, _, _, _, _, _, _, hfmt₀, _⟩
  have hc := ha.2.2.1 b
  rcases hc with ⟨_, _, _, _, _, _, _, _, hfmt₁, _⟩
  have hpre : fmt 6 (q.N k ^ M) D
      {z | rem.coefficient_map k (a.γ b) (i, z) ∈ a.A b} := by
    rw [rem.coefficient_map_formula k (a.γ b)]
    exact normalizedTrajectory_format (fun i => (hfmt₁ i).1) _ _ _ _ _ i
  have hparent : Submission.Obl.k4_dyadic_crop_worlds.BoolFormat
      (p.N (rem.φ k) ^ rem.M) rem.D
      {z | (i, z) ∈ (rem.parent k).A (rem.parentIndex k (a.γ b))} := (hfmt₀ i).1
  exact hparent.inter hpre

/-- Incidence pullback itself keeps exactly the child sign-table size and
degree. The selected pullback property already puts it in the old parent F. -/
theorem liftAtlas_incidence_format {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (b : Fin a.C) (i : ℕ) :
    fmt 7 (q.N k ^ M) D
      {z : Fin 7 → ℝ | ((i, fun j : Fin 6 => z j.castSucc), z 6) ∈ (rem.liftAtlas k a).F b} := by
  have hc := ha.2.2.1 b
  rcases hc with ⟨_, _, _, _, _, _, _, _, hfmt, _⟩
  change fmt 7 (q.N k ^ M) D
    {z : Fin 7 → ℝ | normalizedIncidenceEquiv (rem.coefficient_map k (a.γ b))
      (rem.initialTime k (a.γ b)) (rem.timeLength k) (rem.timeLength_pos k).ne'
        ((i, fun j : Fin 6 => z j.castSucc), z 6) ∈ a.F b}
  simp only [normalizedIncidenceEquiv_apply]
  rw [rem.coefficient_map_formula k (a.γ b)]
  exact normalizedIncidence_format (fun i => (hfmt i).2) _ _ _ _ _ i

end Remainder

end Submission.Obl.k4_native_finite_terminal_atlas_lift
