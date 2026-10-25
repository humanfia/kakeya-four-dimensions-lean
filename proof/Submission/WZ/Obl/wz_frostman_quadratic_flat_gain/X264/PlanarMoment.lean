-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.PlanarMoment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.PlanarRow
import Submission.WZ.Obl.wz_finite_shading_second_moment
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file PlanarMoment.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

/-- A planar second-moment estimate for arbitrary dense shadings of the expanded tubes.
The original tubes need only satisfy the relative Frostman count inside their common prism. -/
lemma planar_shading_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b δ r D lam : ℝ), 0 < a → a ≤ b → b ≤ 1 →
      δ ≤ r → 0 < r → r ≤ 1 → 0 < D → 0 ≤ lam →
      ∀ (n : ℕ) (x v : Fin n → Space) (c e₁ e₂ e₃ : Space), 0 < n →
      Orthonormal ℝ ![e₁, e₂, e₃] → (∀ i, ‖v i‖ = 1) →
      (∀ i, tube δ (x i) (v i) ⊆ prism a b c e₁ e₂ e₃) →
      (∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) *
          volume (prism a b c e₁ e₂ e₃) ≤ ENNReal.ofReal (D * n) * volume U) →
      ∀ (Z : Fin n → Set Space) (E : Set Space), MeasurableSet E → volume E ≠ ⊤ →
      (∀ i, MeasurableSet (Z i)) → (∀ i, Z i ⊆ tube r (x i) (v i)) →
      (∀ i, Z i ⊆ E) → (∀ i, ENNReal.ofReal (lam * r ^ 2) ≤ volume (Z i)) →
      lam ^ 2 * b * r ≤ C * r ^ (-ε) * D * (volume E).toReal := by
  obtain ⟨C, hC, hrow⟩ := planar_overlap_row ε hε
  refine ⟨C, hC, ?_⟩
  intro a b δ r D lam ha hab hb hδr hr hr1 hD hlam n x v c e₁ e₂ e₃ hn
    he hv hP hcount Z E hEm hEfin hZm hZT hZE hdense
  have hb0 : 0 < b := ha.trans_le hab
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hrpow : 0 < r ^ (-ε) := Real.rpow_pos_of_pos hr _
  have hZfin : ∀ i, volume (Z i) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top hEfin (measure_mono (hZE i))
  have hmoment := WangZahlLot.wz_finite_shading_second_moment n Finset.univ Z E
    (lam * r ^ 2) (C * r ^ (-ε) * (D * n * r ^ 3 / b)) hEm hEfin
    (fun i _ => hZm i) (fun i _ => hZE i) (by positivity) (by positivity)
    (by
      intro i _
      have h := ENNReal.toReal_mono (hZfin i) (hdense i)
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ lam * r ^ 2)] using h)
    (by
      intro i _
      apply le_trans _ (hrow a b δ r D ha hab hb hδr hr hr1 hD.le n x v c e₁ e₂ e₃
        he hv hP hcount i)
      apply Finset.sum_le_sum
      intro j _
      apply ENNReal.toReal_mono
      · exact ne_top_of_le_ne_top
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
            (WangZahlLot.Obl.wz_off_stem_brush_overlap.tube_volume_upper hr hr1 (x i) (v i) (hv i)))
          (measure_mono Set.inter_subset_left)
      · exact measure_mono (Set.inter_subset_inter (hZT i) (hZT j)))
  simp only [Finset.card_univ, Fintype.card_fin] at hmoment
  have hmul := mul_le_mul_of_nonneg_right hmoment hb0.le
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < (n : ℝ) * r ^ 3)).mp
  convert hmul using 1 <;> field_simp <;> ring

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
