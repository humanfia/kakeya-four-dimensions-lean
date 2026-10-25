-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.CoefficientPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_essentially_distinct_tube_count.Packing

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

/-- A polynomial bound on the total coefficient family. Six-dimensional
packing suffices here because it is used only to absorb logarithmic losses. -/
theorem coefficient_family_card_mul_scale_six_le {n : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (q : Fin n → EuclideanSpace ℝ (Fin 3)) (hq : ∀ i, ‖q i‖ ≤ 10)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) :
    (n:ℝ)*δ^6 ≤ 4096000000 := by
  let p : Fin n → (EuclideanSpace ℝ (Fin 3)) × (EuclideanSpace ℝ (Fin 3)) :=
    fun i => ((1/10:ℝ) • q i, 0)
  have hp : ∀ i, ‖p i‖ ≤ 1 := by
    intro i
    simp only [p, Prod.norm_def, norm_zero, max_le_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (1/10:ℝ) by norm_num)]
    constructor
    · linarith [hq i]
    · norm_num
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (p i) (δ/20))
      (Metric.ball (p j) (δ/20))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have heq : dist (p i) (p j)=(1/10:ℝ)*dist (q i) (q j) := by
      simp only [p, Prod.dist_eq, dist_self, dist_smul₀,
        Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (1/10:ℝ) by norm_num)]
      exact max_eq_left (by positivity)
    rw [heq]
    linarith [hsep i j hij]
  have hpack := WangZahlLot.Obl.wz_essentially_distinct_tube_count.parameter_ball_packing
    (by positivity : 0 < δ/20) (by linarith : δ/20 ≤ 1) p hp hd
  norm_num at hpack
  nlinarith only [hpack]

/-- The local curve mass inherits the same polynomial scale bound. -/
theorem coefficient_subfamilies_mass_mul_scale_six_le {n : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (q : Fin n → EuclideanSpace ℝ (Fin 3)) (hq : ∀ i, ‖q i‖ ≤ 10)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) (A B : Finset (Fin n)) :
    ((A.card:ℝ)+(B.card:ℝ))*δ^6 ≤ 8192000000 := by
  have ha : (A.card:ℝ) ≤ n := by exact_mod_cast (by simpa using A.card_le_univ : A.card ≤ n)
  have hb : (B.card:ℝ) ≤ n := by exact_mod_cast (by simpa using B.card_le_univ : B.card ≤ n)
  have hmass : (A.card:ℝ)+(B.card:ℝ) ≤ 2*n := by linarith
  have hmul := mul_le_mul_of_nonneg_right hmass (show 0 ≤ δ^6 by positivity)
  have hp := coefficient_family_card_mul_scale_six_le hδ hδ1 q hq hsep
  nlinarith only [hmul, hp]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
