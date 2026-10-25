import ChallengeDeps
import Submission.Helpers
import Submission.Seed.K4.Basic
import Submission.Obl.k4_lower_of_discrete
import Submission.Obl.k4_plank_estimate
import Submission.Obl.k4_multilinear_kakeya
import Submission.Obl.k4_oss_decay
import Submission.Obl.k4_graph_bsg
import Submission.Obl.k4_core

/-!
# Root glue for `oai_074_kakeya_four_dimensions` (a drop-in replacement for `Submission.lean`)

The only `sorry`s it depends on are the six children of `Submission.Split.Children`:
`k4_lower_of_discrete` (R2), `k4_plank_estimate` (T1), `k4_multilinear_kakeya` (T3),
`k4_oss_decay` (T4), `k4_graph_bsg` (T5) and `k4_core` (R3core). (T2, the planar dot-product
input, is the prebuilt `WangZahlLot.wz_ad_projection_dichotomy`, used inside R3core's subtree.)
The upper bound comes from the seed (`Submission.Seed.K4.dimH_le_four`, proved).
-/

namespace Submission

theorem kakeya_four_dimensions (K : Set (EuclideanSpace ℝ (Fin 4)))
    (hK : ∀ e ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      ∃ a : EuclideanSpace ℝ (Fin 4), segment ℝ a (a + e) ⊆ K) :
    dimH K = 4 :=
  le_antisymm (Submission.Seed.K4.dimH_le_four K)
    (k4_lower_of_discrete
      (k4_core k4_plank_estimate k4_multilinear_kakeya k4_oss_decay k4_graph_bsg)
      K hK)

end Submission
