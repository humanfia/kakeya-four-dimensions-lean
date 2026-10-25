-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/NormalizeSequence.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.NormalizeSample

namespace Submission.Obl.k4_paired_test_normalization.NormalizationStep

open Filter

/-- The exact normalization child of x0575's split, with the universal loss
constant `100` and one complexity budget fixed before the slack tolerance. -/
theorem normalization_statement : SplitStatements.normalizationStatement := by
  apply SplitStatements.tested_statement_iff.mpr
  refine ⟨100, by norm_num, ?_⟩
  intro N W ω ν E B L dc a h ha htested
  have hraw := (tested_sequence_iff False 4 N W ω ν E B L dc a h).mp htested
  rcases hraw with ⟨hN, hNt, hL, hω, hωsum, hν, hB, hE, M, D, hsamples⟩
  obtain ⟨C, hC, hnormalize⟩ := normalize_sample
  obtain ⟨M', hMM', hb⟩ := eventually_normalization_bounds hN hNt ha hL C
    normalizationBaseVolume.toReal M
  apply (tested_sequence_iff True 2 N W ω ν E B L dc (100 * a) h).mpr
  refine ⟨hN, hNt, hL, hω, hωsum, hν, hB, hE, M', D, ?_⟩
  intro ε hε
  have hfreq := hsamples (min ε a) (lt_min hε ha)
  apply (hfreq.and_eventually hb).mono
  rintro k ⟨⟨d⟩, hbound⟩
  exact hnormalize (N k) (W k) (ω k) (ν k) (E k) (B k) L dc a h M D M'
    (min ε a) ε d (hω k) (hωsum k) hbound (min_le_right ε a) (min_le_left ε a)

end Submission.Obl.k4_paired_test_normalization.NormalizationStep
