-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.Localization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoarseCover
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Separation

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem exists_large_cover_piece {X I : Type*} [Fintype I] [Nonempty I]
    (H : Finset X) (U : I → Set X) (hcover : ∀ x ∈ H, ∃ i, x ∈ U i) :
    ∃ i : I, (H.card : ℝ) ≤ (Fintype.card I : ℝ) *
      ((H.filter (fun x => x ∈ U i)).card : ℝ) := by
  classical
  let P (i : I) := H.filter (fun x => x ∈ U i)
  have hH : H ⊆ Finset.univ.biUnion P := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hx, hi⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.univ.exists_max_image (fun i => (P i).card)
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  have hc : H.card ≤ Fintype.card I * (P i).card := by
    calc H.card ≤ (Finset.univ.biUnion P).card := Finset.card_le_card hH
      _ ≤ ∑ j, (P j).card := Finset.card_biUnion_le
      _ ≤ ∑ _ : I, (P i).card := Finset.sum_le_sum (fun j hj => hmax j hj)
      _ = _ := by simp
  exact_mod_cast hc

/-- Quantitative localization of a dense set of triples to three small balls.
The retained triples stay away from both degeneracy loci. -/
theorem exists_localized_separated_triples {δ C r q : ℝ} {S T : Finset Plane}
    (hSsq : InUnitSquare (↑S : Set Plane)) (hTsq : InUnitSquare (↑T : Set Plane))
    (hS : FiniteFrostman δ C S) (hT : FiniteFrostman δ C T) (hδr : δ ≤ r)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (H : Finset Triple) (hH : H ⊆ S ×ˢ (T ×ˢ T)) (hHne : H.Nonempty)
    (hsmall : 4 * C * r * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤ (H.card : ℝ)) :
    ∃ (a b c : Plane) (K : Finset Triple), a ∈ S ∧ b ∈ T ∧ c ∈ T ∧ K ⊆ H ∧
      (H.card : ℝ) / (2 * (25 / q ^ 2) ^ 3) ≤ (K.card : ℝ) ∧
      ∀ p ∈ K, dist p.1 a ≤ q ∧ dist p.2.1 b ≤ q ∧ dist p.2.2 c ≤ q ∧
        r ≤ ‖p.1‖ ∧ r ≤ dist p.2.1 p.2.2 := by
  classical
  have hHpos : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hHne
  obtain ⟨H₀, hH₀H, hhalf, hsep⟩ := half_separated_triple_refinement hS hT hδr H hH hsmall
  have hH₀pos : (0 : ℝ) < H₀.card := lt_of_lt_of_le (by positivity) hhalf
  have hH₀ne : H₀.Nonempty := Finset.card_pos.mp (by exact_mod_cast hH₀pos)
  obtain ⟨m, f, hfS, hf, hm⟩ := hSsq.exists_coarse_cover hq hq1
  obtain ⟨n, g, hgT, hg, hn⟩ := hTsq.exists_coarse_cover hq hq1
  let I := Fin m × Fin n × Fin n
  let U (i : I) : Set Triple := Metric.closedBall (f i.1, g i.2.1, g i.2.2) q
  have hcover : ∀ p ∈ H₀, ∃ i, p ∈ U i := by
    intro p hp
    have hpST := Finset.mem_product.mp (hH (hH₀H hp))
    have hpTT := Finset.mem_product.mp hpST.2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hf hpST.1)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hg hpTT.1)
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hg hpTT.2)
    exact ⟨(i, j, k), by
      simpa only [U, Metric.mem_closedBall, Prod.dist_eq, max_le_iff] using ⟨hi, hj, hk⟩⟩
  obtain ⟨p₀, hp₀⟩ := hH₀ne
  obtain ⟨i₀, hi₀⟩ := hcover p₀ hp₀
  letI : Nonempty I := ⟨i₀⟩
  obtain ⟨i, hcard⟩ := exists_large_cover_piece H₀ U hcover
  let K := H₀.filter (fun p => p ∈ U i)
  have hM : (Fintype.card I : ℝ) ≤ (25 / q ^ 2) ^ 3 := by
    simp only [I, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc (m : ℝ) * ((n : ℝ) * n) ≤ (25 / q ^ 2) * ((25 / q ^ 2) * (25 / q ^ 2)) := by
          gcongr
      _ = _ := by ring
  have hcard' : (H₀.card : ℝ) ≤ (25 / q ^ 2) ^ 3 * (K.card : ℝ) :=
    hcard.trans (mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _))
  refine ⟨f i.1, g i.2.1, g i.2.2, K, hfS _, hgT _, hgT _,
    (Finset.filter_subset _ _).trans hH₀H, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (25 / q ^ 2) ^ 3)).mpr
    nlinarith
  · intro p hp
    obtain ⟨hpH₀, hpi⟩ := Finset.mem_filter.mp hp
    have hdist : dist p.1 (f i.1) ≤ q ∧ dist p.2.1 (g i.2.1) ≤ q ∧
        dist p.2.2 (g i.2.2) ≤ q := by
      simpa only [U, Metric.mem_closedBall, Prod.dist_eq, max_le_iff] using hpi
    exact ⟨hdist.1, hdist.2.1, hdist.2.2, hsep p hpH₀⟩

theorem localized_centers_separated {r q : ℝ} {p : Triple} {a b c : Plane}
    (ha : dist p.1 a ≤ q) (hb : dist p.2.1 b ≤ q) (hc : dist p.2.2 c ≤ q)
    (hpa : r ≤ ‖p.1‖) (hpb : r ≤ dist p.2.1 p.2.2) :
    r - q ≤ ‖a‖ ∧ r - 2 * q ≤ dist b c := by
  have hnorm := dist_triangle p.1 a 0
  simp only [dist_zero_right] at hnorm
  have htri := dist_triangle4 p.2.1 b c p.2.2
  rw [dist_comm c p.2.2] at htri
  constructor <;> linarith

end WangZahlLot.Obl.wz_separated_projection_dichotomy
