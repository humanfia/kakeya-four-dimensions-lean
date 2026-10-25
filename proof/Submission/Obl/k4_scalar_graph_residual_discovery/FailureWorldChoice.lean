/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file FailureWorldChoice.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Table
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalWorldChoice

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal

namespace QualificationTable

/-- The original mixture-world index may be selected BEFORE geometric
pruning by averaging against its original probability weights. The later
coefficient-world selection still waits until after globally charged cuts. -/
theorem exists_dense_original_failure_world {α : Type*} [MeasurableSpace α]
    (D : QualificationTable α) (M : ℕ) (ε : ℝ) (k : ℕ) {δ H : ℝ}
    (hδ : 0 < δ) (hH : 0 < H)
    (hω : ∀ g, 0 ≤ D.ω k g) (hωsum : ∑ g, D.ω k g = 1)
    (hfinite : ∀ g, D.law k g univ ≠ ∞)
    (hmass : ENNReal.ofReal (1 / H) ≤ D.totalMass k)
    (hratio : δ ≤ D.rationalFailureRatio M ε k) :
    ∃ g : Fin (D.W k), 0 < D.ω k g ∧ ENNReal.ofReal (δ / (2 * H)) ≤
      D.law k g (D.rationalFailure M ε k g) := by
  classical
  let bad : ℝ≥0∞ := ∑ g, ENNReal.ofReal (D.ω k g) * D.law k g (D.rationalFailure M ε k g)
  have htotalFinite : D.totalMass k ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro g _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite g)
  have hbadFinite : bad ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro g _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top (hfinite g) (measure_mono (subset_univ _)))
  have htotalPositive : 0 < D.totalMass k :=
    (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hH)).trans_le hmass
  have htotalReal : 0 < (D.totalMass k).toReal :=
    ENNReal.toReal_pos (ne_of_gt htotalPositive) htotalFinite
  have htotalFloor := ENNReal.toReal_mono htotalFinite hmass
  rw [ENNReal.toReal_ofReal (one_div_pos.mpr hH).le] at htotalFloor
  change δ ≤ bad.toReal / (D.totalMass k).toReal at hratio
  have hscaled := (le_div_iff₀ htotalReal).mp hratio
  have hbadReal : δ / H ≤ bad.toReal := by
    calc
      δ / H = δ * (1 / H) := by ring
      _ ≤ δ * (D.totalMass k).toReal := mul_le_mul_of_nonneg_left htotalFloor hδ.le
      _ ≤ _ := hscaled
  have hbadFloor : ENNReal.ofReal (δ / H) ≤ bad :=
    (ENNReal.ofReal_le_ofReal hbadReal).trans_eq (ENNReal.ofReal_toReal hbadFinite)
  have hweights : (∑' g, ENNReal.ofReal (D.ω k g) * (1 : ℝ≥0∞)) ≤ 1 := by
    simp only [mul_one, tsum_fintype]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => hω g), hωsum]
    norm_num
  obtain ⟨g, hg, _, hfound⟩ := exists_original_weighted_dense_component
    (fun g => ENNReal.ofReal (D.ω k g)) (fun _ => 1)
    (fun g => D.law k g (D.rationalFailure M ε k g)) (div_pos hδ hH) hweights
    (by simpa only [tsum_fintype] using hbadFloor)
    (by intro g hz; norm_num at hz)
  refine ⟨g, lt_of_not_ge (fun hle => hg (ENNReal.ofReal_eq_zero.mpr hle)), ?_⟩
  have heq : (δ / H) / 2 = δ / (2 * H) := by ring
  simpa only [mul_one, heq] using hfound

end QualificationTable

end Submission.Obl.k4_scalar_graph_residual_discovery
