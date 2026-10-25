-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear.FibreEnds.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Clear/FibreEnds.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.FibreHalf
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.EndTrimming
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

/-!
Ported (namespace and imports adjusted) from the o169 file
`WangZahlLot/Obl/wz_move_three_wide_grains_core/FibreEnds.lean`, branch x0641 of the o169
repository (sessions x0551/x0556/x0587/x0641/x0661/x0670; workspace code, not accepted).
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear

open MeasureTheory Set
open WangZahlLot.Obl.wz_coarse_tube_grains.RIS
  (tubeEnds measurableSet_tubeEnds tubeEnds_volume_upper)

/-- Trimming tube ends and then retaining half the incidences within each fibre
costs at most half the fine mass under the explicit short-length budget. -/
theorem trim_fibre_endpoints {δ c lam : ℝ} {n N : ℕ}
    (x v : Fin n → V) (Z : Fin n → Set V) (f : Fin n → Fin N)
    (hδ : 0 < δ) (hδc : δ ≤ c) (hc : c ≤ 1 / 2)
    (hv : ∀ i, ‖v i‖ = 1) (hZm : ∀ i, MeasurableSet (Z i))
    (hfin : (∑ i, μ (Z i)) ≠ ⊤)
    (hdense : O (lam * n * δ ^ 2) ≤ ∑ i, μ (Z i))
    (hbudget : 5120 * c ≤ lam) :
    ∃ U : Fin n → Set V,
      (∀ i, MeasurableSet (U i) ∧ U i ⊆ Z i ∧
        Disjoint (U i) (tubeEnds δ c (x i) (v i))) ∧
      O (1 / 2) * ∑ i, μ (Z i) ≤ ∑ i, μ (U i) ∧
      ∀ k p, (∃ i, f i = k ∧ p ∈ U i) →
        q n {i | f i = k ∧ p ∈ Z i} ≤ 2 * q n {i | f i = k ∧ p ∈ U i} := by
  let Z₀ i := Z i \ tubeEnds δ c (x i) (v i)
  have hZ₀m i : MeasurableSet (Z₀ i) :=
    (hZm i).diff (measurableSet_tubeEnds _ _ _ _)
  obtain ⟨D, hD, hloss, hfrac⟩ := fibrewise_half_refinement f Z Z₀ hZm hZ₀m
    (fun _ => sdiff_subset)
  have hdiff i : μ (Z i \ Z₀ i) ≤ O (1280 * c * δ ^ 2) := by
    apply (measure_mono (show Z i \ Z₀ i ⊆ tubeEnds δ c (x i) (v i) from ?_)).trans
      (tubeEnds_volume_upper hδ hδc hc (x i) (v i) (hv i))
    intro p hp
    by_contra hn
    exact hp.2 ⟨hp.1, hn⟩
  have hcost : 2 * ∑ i, μ (Z i \ Z₀ i) ≤ O (2560 * c * n * δ ^ 2) := by
    calc _ ≤ 2 * ∑ _i : Fin n, O (1280 * c * δ ^ 2) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hdiff i)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
  have hcost' : O (2560 * c * n * δ ^ 2) ≤ O (1 / 2) * ∑ i, μ (Z i) := by
    calc
      O (2560 * c * n * δ ^ 2) ≤ O ((1 / 2 : ℝ) * (lam * n * δ ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_le_mul_of_nonneg_right hbudget
          (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg δ))
        nlinarith
      _ = O (1 / 2) * O (lam * n * δ ^ 2) := ENNReal.ofReal_mul (by norm_num)
      _ ≤ _ := mul_le_mul' le_rfl hdense
  have hhalf : (1 / 2 : ENNReal) = O (1 / 2) := by
    norm_num [O, ENNReal.ofReal_div_of_pos]
  refine ⟨fun i => Z₀ i ∩ D (f i), ?_, ?_, hfrac⟩
  · intro i
    exact ⟨(hZ₀m i).inter (hD (f i)), inter_subset_left.trans sdiff_subset,
      disjoint_sdiff_left.mono_left inter_subset_left⟩
  · rw [← hhalf]
    apply WangZahlLot.Obl.wz_clustered_cover_volume_gain.half_mass_after_loss hfin hloss
    rw [hhalf]
    exact hcost.trans hcost'

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear
