import Submission.Obl.k4_critical_path_framework.SplitInterfaces
import Submission.Obl.k4_extremal_profile_setup
import Submission.Obl.k4_finite_width_critical_contradiction
import Submission.Obl.k4_unbounded_width_exclusion

/-! Combine the extremal setup and its two complementary narrowness conclusions. -/
namespace Submission.Obl.k4_critical_path_framework

/-- All format bounds remain inside the genuine-terminal horizon predicate. -/
theorem horizon_zero (hs : ScalarProjection) (hm : Matching)
    (hi : InitialHorizonExpanded) (he : TerminalExtension) (hx : ImprovementPrinciple)
    (p : Data) (hp : p.Valid) : horizon p = 0 := by
  have hi' : InitialHorizon := initialHorizon_iff.mp hi
  have hS : 0 < p.S := hp.2.2.2.2.2.2.1
  have hη : 0 < p.η := hp.2.2.2.2.2.2.2.1
  apply le_antisymm _ (horizon_nonneg hi' hp)
  apply le_of_not_gt
  intro hpos
  have hb : ∃ N K L d W ω ν E P B f g G,
      Problem N K L d p.S p.η W ω ν E P B f g G ∧
        0 < HorizonExpanded N K L W ω ν E B f := by
    refine ⟨p.N, p.K, p.L, p.d, p.W, p.ω, p.ν, p.E, p.P, p.B, p.f, p.g, p.G, hp, ?_⟩
    simpa only [horizonExpanded_eq] using hpos
  have hsetup : ∃ ds kr : ℝ, ExtremalSetup ds kr p.S p.η :=
    Submission.k4_extremal_profile_setup hi he p.S p.η hS hη hb
  obtain ⟨ds, kr, hsetup⟩ := hsetup
  have hbounded : BoundedWidth ds kr p.S p.η :=
    Submission.k4_unbounded_width_exclusion hs hm hi ds kr p.S p.η hS hη hsetup
  exact Submission.k4_finite_width_critical_contradiction hi hx
    ds kr p.S p.η hS hη hsetup hbounded

end Submission.Obl.k4_critical_path_framework
