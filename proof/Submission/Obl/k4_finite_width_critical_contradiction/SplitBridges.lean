import Submission.Obl.k4_finite_width_critical_contradiction.SplitStatements

/-! Transport the checked width optimization through the exact frozen predicates. -/
namespace Submission.Obl.k4_finite_width_critical_contradiction

/-- Uniform availability concerns the complete exact problem, not a single resolution. -/
theorem uniformWidth_of_named {ds kr S η w : ℝ}
    (h : UniformNarrowness (NearMaximizer ds kr S η)
      (fun p h w => NarrowTerminal p.1 h w) kr w) :
    UniformWidthExpanded ds kr S η w := by
  intro a ha
  obtain ⟨t, ht, hall⟩ := h a ha
  refine ⟨t, ht, ?_⟩
  intro N K d W ω ν E P B f g G hp hd hH
  let p : Data := ⟨N, K, 1, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
  have hnear : NearMaximizer ds kr S η t ⟨p, hp⟩ := by
    refine ⟨rfl, rfl, rfl, hd, ?_⟩
    change kr - t < horizon p
    rw [horizon_eq_expanded]
    exact hH
  exact (expandedNarrowTerminal_iff p (kr + a) w).mpr (hall ⟨p, hp⟩ hnear)

/-- Nonavailability above the cutoff has one margin fixed before all outer tolerances. -/
theorem badFamily_of_named {ds kr S η w : ℝ}
    (h : BoundedNarrowness (NearMaximizer ds kr S η)
      (fun p h w => NarrowTerminal p.1 h w) kr w) :
    ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, 0 < t →
      ∃ N K d W ω ν E P B f g G,
        Problem N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧
        kr - t < ExpandedHorizon N K 1 W ω ν E B f ∧
        ¬ ExpandedNarrowTerminal N K 1 W ω ν E B f (kr + a) w := by
  obtain ⟨a, ha, hbad⟩ := h
  refine ⟨a, ha, fun t ht => ?_⟩
  obtain ⟨⟨p, hp⟩, ⟨hL, hS, hη, hd, hH⟩, hnot⟩ := hbad t ht
  change p.L = 1 at hL
  change p.S = S at hS
  change p.η = η at hη
  have hvalid : Problem p.N p.K 1 p.d S η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G := by
    simpa only [Data.Valid, hL, hS, hη] using hp
  have heq : horizon p = ExpandedHorizon p.N p.K 1 p.W p.ω p.ν p.E p.B p.f := by
    simpa only [hL] using horizon_eq_expanded p
  refine ⟨p.N, p.K, p.d, p.W, p.ω, p.ν, p.E, p.P, p.B, p.f, p.g, p.G,
    hvalid, hd, ?_, ?_⟩
  · rw [← heq]
    exact hH
  · intro hn
    apply hnot
    apply (expandedNarrowTerminal_iff p (kr + a) w).mp
    simpa only [hL] using hn

end Submission.Obl.k4_finite_width_critical_contradiction
