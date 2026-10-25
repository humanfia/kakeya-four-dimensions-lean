-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.FrozenUnionAdapter.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.GlobalUnion
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.UnionReduction
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ElementaryRanges

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set MeasureTheory
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- The hereditary union estimate specializes to the exact frozen slope
threshold and richness exponent, with density power one. -/
theorem restricted_area_of_union_estimate {τ C : ℝ} (hτ : 0 ≤ τ) (hC : 0 ≤ C)
    (hunion : NarrowUnionEstimate τ C) {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hq : ∀ i, ‖q i‖ ≤ 10) (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (A B : Finset (Fin n)) {δ D μ K : ℝ}
    (hδ : 0 < δ) (hδ100 : δ ≤ (1/100:ℝ))
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (q i) (q j))
    (hδD : δ ≤ D) (hD20 : D ≤ 20) (hμ : 0 < μ) (hK : 1 ≤ K)
    (hA : ∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D/100)
    (hB : ∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ D/100)
    (hcross : ∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2*D)
    (hcount : ∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ D →
      (Set.ncard {i : Fin n | i ∈ A ∪ B ∧ q i ∈ Metric.ball q0 r} : ℝ) ≤ K*(r/δ))
    (hscale : δ*μ*δ^(-8*τ) ≤ D) :
    volume {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
      ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p ∧
      transverseMultiplicity A B δ (δ^(4*τ)*μ^(-(1/2:ℝ))) q g p <
        ENNReal.ofReal (μ^2/100)} ≤
      ENNReal.ofReal (576*C*δ^(-τ)*K^(1:ℝ)*δ*
        ((A.card:ℝ)+(B.card:ℝ))*μ^(-(3/2:ℝ))) := by
  apply restricted_area_of_frozen_union_bound A B hg hδ (by linarith) hδD hμ hK hC hτ
    hA hB hcross hcount
  intro F G hFA hGB
  have hnatural := natural_length_le_slope_threshold hδ (hδ.trans_le hδD) hμ hscale
  have hκ : 0 < δ^(4*τ)*μ^(-(1/2:ℝ)) := by positivity
  exact hunion hq hg hjet δ hδ hδ100 hsep F G D (9*(δ^(4*τ)*μ^(-(1/2:ℝ))))
    hδD hD20 (by positivity) (by linarith)
    (fun i hi j hj => hA i (hFA hi) j (hFA hj))
    (fun i hi j hj => hB i (hGB hi) j (hGB hj))
    (fun i hi j hj => hcross i (hFA hi) j (hGB hj))

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
