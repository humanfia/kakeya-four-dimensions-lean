-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.CoefficientCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.IntervalPacking
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.TranslationAverage

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set Metric

/-- A coefficient cluster admits a quantitative finite cover by smaller
coefficient balls. The cubic loss comes only from ambient dimension three. -/
theorem exists_coefficient_cluster_cover {n : ℕ}
    (F : Finset (Fin n)) (q : Fin n → EuclideanSpace ℝ (Fin 3)) {ρ D : ℝ}
    (hρ : 0 < ρ) (hρD : ρ ≤ D)
    (hdiam : ∀ i ∈ F, ∀ j ∈ F, dist (q i) (q j) ≤ D) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin 3)), C ⊆ F.image q ∧
      (C.card : ℝ) * ρ ^ 3 ≤ 3456 * D ^ 3 ∧
      ∀ i ∈ F, ∃ c ∈ C, dist (q i) c ≤ ρ := by
  classical
  have hD : 0 < D := hρ.trans_le hρD
  obtain ⟨C, hCF, hsep, hcover⟩ :=
    WangZahlLot.Obl.wz_slab_local_linearity.finite_separated_cover (F.image q) ρ hρ.le
  refine ⟨C, hCF, ?_, fun i hi => hcover (q i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)⟩
  rcases F.eq_empty_or_nonempty with hF | hF
  · have hC : C = ∅ := by simpa [hF] using hCF
    simp only [hC, Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  obtain ⟨a, ha⟩ := hF
  let e := (Finset.equivFin C).symm
  let t : Fin C.card → EuclideanSpace ℝ (Fin 3) := fun i => (e i : EuclideanSpace ℝ (Fin 3))
  have htsep : ∀ i j, i ≠ j → ρ ≤ dist (t i) (t j) := by
    intro i j hij
    exact (hsep _ (e i).property _ (e j).property (by
      intro he
      exact hij (e.injective (Subtype.ext he)))).le
  have htmem : ∀ i, t i ∈ ball (q a) (2 * D) := by
    intro i
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp (hCF (e i).property)
    change dist (t i) (q a) < 2 * D
    have ht : t i = q b := hbe.symm
    rw [ht]
    exact (hdiam b hb a ha).trans_lt (by linarith)
  have hc := WangZahlLot.Obl.wz_normalized_projection_coarse_fine.separated_point_ball_count
    hρ (show ρ ≤ 2 * D by linarith) t htsep (q a)
  have hall : {i : Fin C.card | t i ∈ ball (q a) (2 * D)} = univ :=
    Set.eq_univ_of_forall htmem
  rw [hall] at hc
  simp only [Set.ncard_univ, Nat.card_fin] at hc
  nlinarith

/-- A uniform bound on each small coefficient ball gives a global bound on
a bounded coefficient cluster, with its covering loss made explicit. -/
theorem card_le_of_local_coefficient_count {n : ℕ}
    (F : Finset (Fin n)) (q : Fin n → EuclideanSpace ℝ (Fin 3)) {ρ D M : ℝ}
    (hρ : 0 < ρ) (hρD : ρ ≤ D) (hM : 0 ≤ M)
    (hdiam : ∀ i ∈ F, ∀ j ∈ F, dist (q i) (q j) ≤ D)
    (hlocal : ∀ c : EuclideanSpace ℝ (Fin 3),
      ((F.filter (fun i => dist (q i) c ≤ ρ)).card : ℝ) ≤ M) :
    (F.card : ℝ) * ρ ^ 3 ≤ 3456 * D ^ 3 * M := by
  classical
  obtain ⟨C, hCF, hcard, hcover⟩ := exists_coefficient_cluster_cover F q hρ hρD hdiam
  let F' (c : EuclideanSpace ℝ (Fin 3)) := F.filter (fun i => dist (q i) c ≤ ρ)
  have hsub : F ⊆ C.biUnion F' := by
    intro i hi
    obtain ⟨c, hc, hci⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  have hF : (F.card : ℝ) ≤ (C.card : ℝ) * M := by
    calc
      (F.card : ℝ) ≤ ((C.biUnion F').card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ ((∑ c ∈ C, (F' c).card : ℕ) : ℝ) := Nat.cast_le.mpr (Finset.card_biUnion_le)
      _ = ∑ c ∈ C, ((F' c).card : ℝ) := by simp
      _ ≤ ∑ _c ∈ C, M := Finset.sum_le_sum fun c _ => hlocal c
      _ = (C.card : ℝ) * M := by simp
  have hF' := mul_le_mul_of_nonneg_right hF (pow_nonneg hρ.le 3)
  have hcard' := mul_le_mul_of_nonneg_right hcard hM
  nlinarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
