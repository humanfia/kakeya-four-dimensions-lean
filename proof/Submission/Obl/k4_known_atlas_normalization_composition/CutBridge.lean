import Submission.Obl.k4_known_atlas_normalization_composition.CutTypes

namespace Submission.Obl.k4_known_atlas_normalization_composition

open MeasureTheory Filter

/-- Raw native normalization followed by homogeneous selection constructs
one concrete calibrated remainder for all later finite lifts. -/
theorem remainderConstruction_of_cuts (hc : RawConstructionCut)
    (hh : HomogenizationCut) : RemainderConstruction := by
  intro p hp r h w hr hrL hk
  have hk' := (expandedKnown_iff p r h w).mpr hk
  obtain ⟨N₀, K₀, L₀, d₀, S₀, η₀, W₀, ω₀, ν₀, E₀, P₀, B₀, hraw⟩ :=
    hc p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      hp r h w hr hrL hk'
  obtain ⟨N', K', L', d', S', η', W', ω', ν', E', P', B', f', g', G', hcert⟩ :=
    hh p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      N₀ K₀ L₀ d₀ S₀ η₀ W₀ ω₀ ν₀ E₀ P₀ B₀ hp r h w hr hrL hraw
  let q : Data := ⟨N', K', L', d', S', η', W', ω', ν', E', P', B', f', g', G'⟩
  exact ⟨q, (cutCertificate_iff p q r h w).mp hcert⟩

/-- The finite-lifting frozen child gives the named finite transfer used by the
asymptotic glue, without changing the true-floor requirements. -/
theorem finiteLifting_of_cut (hl : FiniteLiftingCut) : FiniteLifting := by
  intro p q r h w hp hr hrL rem
  have hcert := (cutCertificate_iff p q r h w).mpr ⟨rem⟩
  obtain ⟨φ, hφ, ht⟩ :=
    hl p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      q.N q.K q.L q.d q.S q.η q.W q.ω q.ν q.E q.P q.B q.f q.g q.G
      hp r h w hr hrL hcert
  refine ⟨φ, hφ, ?_⟩
  intro M D
  obtain ⟨M', D', ht⟩ := ht M D
  refine ⟨M', D', fun ε hε => ?_⟩
  obtain ⟨ε', hε', hs⟩ := ht ε hε
  refine ⟨ε', hε', hs.mono ?_⟩
  intro k hs
  constructor
  · intro h' ha
    apply (terminalAt_iff_expanded p M' D' (h + h' + ε) ε (φ k)).mpr
    exact hs.1 h' ((terminalAt_iff_expanded q M D h' ε' k).mp ha)
  · intro h' w' ha
    apply (narrowTerminalAt_iff_expanded p M' D' (h + h') (w + w') ε (φ k)).mpr
    exact hs.2 h' w' ((narrowTerminalAt_iff_expanded q M D h' w' ε' k).mp ha)

end Submission.Obl.k4_known_atlas_normalization_composition
