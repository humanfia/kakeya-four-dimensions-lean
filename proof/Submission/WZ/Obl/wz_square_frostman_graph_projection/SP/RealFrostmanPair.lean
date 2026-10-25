-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RealFrostmanPair.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.CartesianFrostman

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

theorem RealFiniteFrostman.exists_separated_pair {δ C σ q : ℝ} {A : Finset ℝ}
    (hA : RealFiniteFrostman δ C σ A) (hAne : A.Nonempty) (hδq : δ ≤ q)
    (hsmall : C * q ^ σ < 1) :
    ∃ c ∈ A, ∃ d ∈ A, q ≤ |c - d| := by
  classical
  obtain ⟨c, hc⟩ := hAne
  by_contra h
  push Not at h
  have hfilter : A.filter (fun d => dist d c ≤ q) = A := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    simpa only [Real.dist_eq, abs_sub_comm] using (h c hc d hd).le
  have hh := hA c q hδq
  rw [hfilter] at hh
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr ⟨c, hc⟩
  nlinarith

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
