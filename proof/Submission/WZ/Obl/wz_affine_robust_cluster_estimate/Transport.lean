-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_robust_cluster_estimate.Transport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Affine

namespace WangZahlLot.Obl.wz_affine_robust_cluster_estimate
open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section

/-- Transport average shading density under the affine change of variables. -/
theorem density_transport (F : E ≃ᴬ[ℝ] E) {κ t δ lam : ℝ} (hκ : 0 < κ)
    (hvol : ∀ W : Set E, volume (F '' W) = ENNReal.ofReal (κ ^ 3 * t ^ 2) * volume W)
    {n : ℕ} (Y : Fin n → Set E)
    (hden : ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)) :
    ENNReal.ofReal ((κ * lam) * (n : ℝ) * (κ * t * δ) ^ 2) ≤
      ∑ i, volume (F '' Y i) := by
  calc
    _ = ENNReal.ofReal (κ ^ 3 * t ^ 2) * ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (κ ^ 3 * t ^ 2) * ∑ i, volume (Y i) := mul_le_mul_right hden _
    _ = _ := by simp only [Finset.mul_sum, hvol]

/-- Enlarging affine image tubes preserves the convex count with constant `m / κ`. -/
theorem convex_count_transport (F : E ≃ᴬ[ℝ] E) {κ t δ m : ℝ} (hκ : 0 < κ)
    (hvol : ∀ W : Set E, volume (F '' W) = ENNReal.ofReal (κ ^ 3 * t ^ 2) * volume W)
    {n : ℕ} (x v x' v' : Fin n → E)
    (hcontain : ∀ i, F '' tube δ (x i) (v i) ⊆ tube (κ * t * δ) (x' i) (v' i))
    (hc : ∀ W : Set E, Convex ℝ W →
      ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal m * volume W) :
    ∀ W : Set E, Convex ℝ W →
      ENNReal.ofReal (({i | tube (κ * t * δ) (x' i) (v' i) ⊆ W}.ncard : ℝ) *
        (κ * t * δ) ^ 2) ≤ ENNReal.ofReal (m / κ) * volume W := by
  intro W hW
  have hpre : ENNReal.ofReal (κ ^ 3 * t ^ 2) * volume (F ⁻¹' W) = volume W := by
    rw [← hvol, Set.image_preimage_eq _ (EquivLike.surjective F)]
  have hcount : {i | tube (κ * t * δ) (x' i) (v' i) ⊆ W} ⊆
      {i | tube δ (x i) (v i) ⊆ F ⁻¹' W} := by
    intro i hi p hp
    exact hi (hcontain i ⟨p, hp, rfl⟩)
  have hc' := hc (F ⁻¹' W) (Convex.affine_preimage F.toAffineEquiv.toAffineMap hW)
  apply (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_ne_zero_iff.mpr hκ) ENNReal.ofReal_ne_top).mp
  calc
    _ = ENNReal.ofReal (κ ^ 3 * t ^ 2) *
        ENNReal.ofReal (({i | tube (κ * t * δ) (x' i) (v' i) ⊆ W}.ncard : ℝ) * δ ^ 2) := by
      rw [← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (κ ^ 3 * t ^ 2) *
        ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ F ⁻¹' W}.ncard : ℝ) * δ ^ 2) := by
      apply mul_le_mul_right _ _
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (ncard_mono hcount)) (sq_nonneg δ)
    _ ≤ ENNReal.ofReal (κ ^ 3 * t ^ 2) * (ENNReal.ofReal m * volume (F ⁻¹' W)) :=
      mul_le_mul_right hc' _
    _ = ENNReal.ofReal m * volume W := by rw [mul_left_comm, hpre]
    _ = ENNReal.ofReal κ * (ENNReal.ofReal (m / κ) * volume W) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hκ.le]
      congr 2
      field_simp

end
end WangZahlLot.Obl.wz_affine_robust_cluster_estimate
