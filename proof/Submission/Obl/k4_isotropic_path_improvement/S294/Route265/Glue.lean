-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Route265.Glue, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The o265-direct route, glue (session x1088): o265's staged statement (the accepted o288's
`StagedAssertion`, its readable form) from o295's statement, the accepted o288 statement and
the relative-scale source.  The virtual row packet goes through o295 to a virtual physical
potential packet, through o288 to a virtual candidate, and the instance returns that candidate
to the actual old packet. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Route265.Interface
import Submission.Obl.k4_physical_parent_potential_candidates

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294

noncomputable section

namespace Route265

open Submission.Obl.k4_physical_parent_potential_candidates
  (StagedAssertion StagedAt CompletionAssertion weakds cd)

/-- **o265 from o295, o288 and the relative source.** -/
theorem staged_of_relative_source (hrows : RowPotentialAssertion)
    (hcompl : CompletionAssertion) (hsrc : RelativeSourceAssertion) : StagedAssertion := by
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁one hκ₁ hκ₁one hS hη hρ hgap
  obtain ⟨M, hM, hsrc⟩ := hsrc cc hcc d₁ κ₁ S η ρ hd₁ hd₁one hκ₁ hκ₁one hS hη hρ hgap
  obtain ⟨Ep, hrowsM⟩ := hrows M d₁ hd₁ hd₁one
  obtain ⟨precision, hprec, hcomplP⟩ :=
    hcompl hmk (3 * M + 1) (by omega) cc hcc d₁ ρ hd₁ hd₁one hρ hgap
  intro D₀
  obtain ⟨D, hD, hsrcD⟩ :=
    hsrc Ep precision hprec (max D₀ (max 5186 (864 * (2 * ((3 * M + 1) + 2)) + 2)))
  refine ⟨D, le_trans (le_max_left _ _) hD, ?_⟩
  intro J hJ hjet e0 he0
  obtain ⟨loss, hloss, hlossone, hcomplL⟩ :=
    hcomplP D (le_trans (le_max_right _ _) hD) J hJ hjet
  obtain ⟨m, s, gain, δ₀, u0, hgrid, hgaine0, hsrcT⟩ :=
    hsrcD J hJ hjet loss hloss hlossone e0 he0
  refine ⟨m, s, gain, δ₀, u0, hgrid, hgaine0, ?_⟩
  intro N K L d W ω ν E P B f g G hpb hlin Mp Dp
  obtain ⟨Mp', Dp', Mr', hsrcM⟩ := hsrcT N K L d W ω ν E P B f g G hpb hlin Mp Dp
  have hL : 0 < L := hpb.2.2.2.1
  have hNtend : Filter.Tendsto N Filter.atTop Filter.atTop := hpb.2.1
  have hgain0 : 0 < gain := hgrid.2.1
  have hgain8 : gain ≤ 1 / 8 := hgrid.2.2.1
  obtain ⟨Mc', hcomplMc⟩ := hcomplL L gain hL hgain0 hgain8 Mp' Dp' Mr'
  obtain ⟨M₀, D₀', hsrcMi⟩ := hsrcM Mc'
  refine ⟨M₀, D₀', ?_⟩
  intro Mi Di hMi hDi τ hτ α hα hαone
  obtain ⟨Mi', hMi', σ, hσ, k₀, hsrcK⟩ := hsrcMi Mi Di hMi hDi τ hτ α hα hαone
  obtain ⟨Nk₀, hNk₀, hcomplNk⟩ := hcomplMc Mi' hMi' τ hτ
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.1 (hNtend.eventually_ge_atTop Nk₀)
  refine ⟨σ, hσ, max k₀ k₁, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass
  rcases hsrcK k (le_trans (le_max_left _ _) hk) r T nw κ C lev par γ j c u Q R A F lst hpath
      H hH hmass with hexit | hinst
  · rcases hexit with hwi | hnarrow
    · exact Or.inl (Or.inl hwi)
    · exact Or.inr hnarrow
  · obtain ⟨κ', ν', B', r', T', j', c', u', Q', R', P0', A', F', H', ex', hrow, hκ', hT',
      hprob, hB', hBup, hBinv, hP0deg, hP0coeff, hch, hj', hr', hroom, hret⟩ := hinst
    have hPPP := hrowsM (3 * M + 1) le_rfl precision loss (N k) L gain κ' ν' B' r' T' j' c' u'
      P0' A' F' H' hrow
    have hNk : Nk₀ ≤ N k := hk₁ k (le_trans (le_max_right _ _) hk)
    have hcd := hcomplNk (N k) hNk 1 (fun _ => ν') (fun _ => B') κ' (fun _ => r') (fun _ => T') 1
      (fun _ => 0) (fun _ => 0) (fun _ => j') (fun _ => c') (fun _ => u') (fun _ => Q')
      (fun _ => R') (fun _ => A') (fun _ => F') (fun _ => H') ex' 0 P0' hκ' hT' hprob hB' hBup
      hBinv hP0deg hP0coeff hch hj' hr' hroom hPPP
    exact Or.inl (Or.inr (hret hcd))


/-- The same with the accepted o288 plugged in: o265 follows from o295's statement and the
relative-scale source. (Checked separately: `StagedAssertion` is definitionally o265's frozen
statement and `RowPotentialAssertion` is definitionally o295's.) -/
theorem staged_of_rows_and_relative_source (hrows : RowPotentialAssertion)
    (hsrc : RelativeSourceAssertion) : StagedAssertion :=
  staged_of_relative_source hrows Submission.k4_physical_parent_potential_candidates hsrc

end Route265

end

end Submission.Obl.k4_isotropic_path_improvement.S294
