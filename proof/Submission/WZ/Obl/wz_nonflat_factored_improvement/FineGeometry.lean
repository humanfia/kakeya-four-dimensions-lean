-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.FineGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.AffineNet

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit norm_smul_unit)

/-- A sufficiently short affine image of a tube lies in a prism about its image midpoint. -/
theorem affine_tube_prism (f : AffineEquiv ℝ Space Space) {δ A : ℝ} (hA : 0 < A)
    (hρ : A * δ ≤ 1 / 1000000)
    (hLip : ∀ p q, dist (f p) (f q) ≤ A * dist p q)
    (x v : Space) (hv : ‖v‖ = 1) (hlen : ‖f.linear v‖ ≤ 1 / 1000000) :
    ∃ u : Fin 3 → Space, Orthonormal ℝ u ∧
      f '' tube δ x v ⊆ WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
        (A * δ) (A * δ) (f (x + (1 / 2 : ℝ) • v)) u := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hV : f.linear v ≠ 0 := (map_ne_zero_iff f.linear f.linear.injective).mpr hv0
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first
    (norm_unit hV)
  let u : Fin 3 → Space := fun i => b (Equiv.swap (0 : Fin 3) 2 i)
  have hu : Orthonormal ℝ u := b.orthonormal.comp (Equiv.swap (0 : Fin 3) 2)
    (Equiv.swap (0 : Fin 3) 2).injective
  have hu2 : u 2 = unit (f.linear v) := by simp [u, hb]
  have hVeq : f.linear v = ‖f.linear v‖ • u 2 := by
    rw [hu2]
    exact (norm_smul_unit hV).symm
  have hcoord (i : Fin 3) : inner ℝ (u i) (f.linear v) =
      if i = 2 then ‖f.linear v‖ else 0 := by
    conv_lhs => rw [hVeq, inner_smul_right, orthonormal_iff_ite.mp hu]
    split_ifs <;> simp
  have hmap (t : ℝ) : f (x + t • v) - f (x + (1 / 2 : ℝ) • v) =
      (t - 1 / 2) • f.linear v := by
    have he (s : ℝ) : f (x + s • v) = s • f.linear v + f x := by
      rw [add_comm]
      simpa using f.map_vadd x (s • v)
    rw [he, he]
    module
  refine ⟨u, hu, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have hd : ‖f p - f (x + t • v)‖ < A * δ := by
    rw [← dist_eq_norm]
    exact (hLip _ _).trans_lt (mul_lt_mul_of_pos_left hpq hA)
  have ht' : |t - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have he : f p - f (x + (1 / 2 : ℝ) • v) =
      (f p - f (x + t • v)) + (t - 1 / 2) • f.linear v := by
    rw [← hmap]
    abel
  have hi (i : Fin 3) : |inner ℝ (u i) (f p - f (x + t • v))| < A * δ := by
    apply (abs_real_inner_le_norm _ _).trans_lt
    simpa [hu.1 i] using hd
  change _ ∧ _ ∧ _
  simp only [he, inner_add_right, inner_smul_right, hcoord, Fin.isValue]
  norm_num only at *
  refine ⟨?_, ?_, ?_⟩
  · simpa using (hi 0).le
  · simpa using (hi 1).le
  · have hn : |(t - 1 / 2) * ‖f.linear v‖| ≤ (1 / 2) * ‖f.linear v‖ := by
      rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right ht' (norm_nonneg _)
    have ht := abs_add_le (inner ℝ (u 2) (f p - f (x + t • v)))
      ((t - 1 / 2) * ‖f.linear v‖)
    simp only [ite_true]
    linarith [hi 2]

end WangZahlLot.Obl.wz_nonflat_factored_improvement
