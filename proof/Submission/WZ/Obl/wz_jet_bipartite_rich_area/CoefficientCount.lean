-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.CoefficientCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

/-- The coefficient count controls the cardinality of any small-diameter
subfamily. The center is chosen inside that subfamily. -/
theorem card_cluster_le_of_count {n : ℕ} (A U : Finset (Fin n))
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {δ D K : ℝ}
    (hδ : 0 < δ) (hδD : δ ≤ D) (hK : 0 ≤ K) (hAU : A ⊆ U)
    (hdiam : ∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D / 100)
    (hcount : ∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ D →
      (Set.ncard {i : Fin n | i ∈ U ∧ q i ∈ Metric.ball q0 r} : ℝ) ≤ K * (r / δ)) :
    (A.card : ℝ) ≤ K * (D / δ) := by
  classical
  have hD : 0 < D := hδ.trans_le hδD
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · obtain ⟨a, ha⟩ := hA
    have hsub : (↑A : Set (Fin n)) ⊆
        {i : Fin n | i ∈ U ∧ q i ∈ Metric.ball (q a) D} := by
      intro i hi
      refine ⟨hAU hi, ?_⟩
      exact (hdiam i hi a ha).trans_lt (by linarith)
    have hc : A.card ≤ Set.ncard {i : Fin n | i ∈ U ∧ q i ∈ Metric.ball (q a) D} := by
      rw [← Set.ncard_coe_finset A]
      exact Set.ncard_le_ncard hsub
    exact (Nat.cast_le.mpr hc).trans (hcount (q a) D hδD le_rfl)

/-- The two cluster hypotheses preserve a bound on the actual local curve mass. -/
theorem total_card_le_of_bipartite_count {n : ℕ} (A B : Finset (Fin n))
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {δ D K : ℝ}
    (hδ : 0 < δ) (hδD : δ ≤ D) (hK : 0 ≤ K)
    (hA : ∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D / 100)
    (hB : ∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ D / 100)
    (hcount : ∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ D →
      (Set.ncard {i : Fin n | i ∈ A ∪ B ∧ q i ∈ Metric.ball q0 r} : ℝ) ≤ K * (r / δ)) :
    (A.card : ℝ) + (B.card : ℝ) ≤ 2 * K * (D / δ) := by
  classical
  have ha := card_cluster_le_of_count A (A ∪ B) hδ hδD hK Finset.subset_union_left hA hcount
  have hb := card_cluster_le_of_count B (A ∪ B) hδ hδD hK Finset.subset_union_right hB hcount
  linarith

/-- The numerical passage from a `N^(3/2)` tangency count to linear local
curve mass. The two scale conditions are precisely the mass cap and the
far-richness condition. No incidence estimate is assumed to hold by this lemma. -/
theorem tangency_expression_le_linear_mass {δ D K N μ : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hK : 1 ≤ K) (hN : 0 ≤ N) (hμ : 0 < μ)
    (hpack : δ * N ≤ 2 * K * D) (hscale : δ * μ ≤ D) :
    Real.sqrt (δ / D) *
        (N * Real.sqrt N * μ ^ (-(3 / 2 : ℝ)) + N / μ) ≤
      3 * K * N * μ ^ (-(3 / 2 : ℝ)) := by
  have hrootδ : (Real.sqrt (δ / D)) ^ 2 = δ / D :=
    Real.sq_sqrt (div_nonneg hδ.le hD.le)
  have hrootN : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN
  have hrootμ : (Real.sqrt μ) ^ 2 = μ := Real.sq_sqrt hμ.le
  have hcapN : (Real.sqrt (δ / D) * Real.sqrt N) ^ 2 ≤ 2 * K := by
    rw [mul_pow, hrootδ, hrootN]
    have he : δ / D * N = (δ * N) / D := by ring
    rw [he]
    exact (div_le_iff₀ hD).mpr hpack
  have hcapμ : (Real.sqrt (δ / D) * Real.sqrt μ) ^ 2 ≤ 1 := by
    rw [mul_pow, hrootδ, hrootμ]
    have he : δ / D * μ = (δ * μ) / D := by ring
    rw [he]
    exact (div_le_one hD).mpr hscale
  have hbN : Real.sqrt (δ / D) * Real.sqrt N ≤ 2 * K := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (δ / D)) (Real.sqrt_nonneg N)]
  have hbμ : Real.sqrt (δ / D) * Real.sqrt μ ≤ 1 := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (δ / D)) (Real.sqrt_nonneg μ)]
  have hpow : Real.sqrt μ * μ ^ (-(3 / 2 : ℝ)) = μ⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hμ]
    norm_num [Real.rpow_neg_one]
  have hrepr : N / μ = N * Real.sqrt μ * μ ^ (-(3 / 2 : ℝ)) := by
    rw [mul_assoc, hpow, div_eq_mul_inv]
  rw [hrepr]
  calc
    _ = (Real.sqrt (δ / D) * Real.sqrt N + Real.sqrt (δ / D) * Real.sqrt μ) *
        N * μ ^ (-(3 / 2 : ℝ)) := by ring
    _ ≤ (2 * K + 1) * N * μ ^ (-(3 / 2 : ℝ)) := by
      gcongr
    _ ≤ _ := by
      gcongr
      linarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
