-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.ForwardCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Normalization

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

lemma normalized_convex_count (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space)
    {r s L : ℝ} (hr : 0 < r) (hs : 0 < s) (hL : 0 ≤ L)
    {n M : ℕ} (x v : Fin n → Space) (z u : Fin M → Space)
    (j : Fin M → Fin n) (hj : Function.Injective j)
    (hcover : ∀ i, normalize e y w r hr '' tube s (x (j i)) (v (j i)) ⊆
      tube (normalizedRadius r s) (z i) (u i))
    (hK : ConvexCount s L (fun _ => True) (fun i => tube s (x i) (v i))) :
    ConvexCount (normalizedRadius r s) (16 * L / contraction) (fun _ => True)
      (fun i => tube (normalizedRadius r s) (z i) (u i)) := by
  have hc := WangZahlLot.Obl.wz_nonflat_factored_improvement.affine_count_transport
    (normalize e y w r hr).toAffineEquiv (by positivity : 0 < jacobian r)
    (sq_pos_of_pos hs) hL (normalize_volume e y w hr) x v z u j hj hcover
    (by simpa only [ConvexCount, true_and] using hK)
  have hk := WangZahlLot.Obl.wz_nonflat_factored_improvement.convexCount_of_raw_count
    (by positivity : 0 ≤ L / (s ^ 2 * jacobian r)) z u hc
  have he : L / (s ^ 2 * jacobian r) * (normalizedRadius r s) ^ 2 =
      16 * L / contraction := by
    dsimp [jacobian, normalizedRadius]
    field_simp
    ring
  simpa only [ConvexCount, true_and, he] using hk

lemma normalized_slab_count (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) (hw : ‖w‖ = 1) {r s L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {n M : ℕ} (hM : 0 < M) (x v : Fin n → Space) (z u : Fin M → Space)
    (j : Fin M → Fin n) (hj : Function.Injective j)
    (hT : ∀ i, tube s (x i) (v i) ⊆ tube r y w)
    (hcover : ∀ i, normalize e y w r hr '' tube s (x (j i)) (v (j i)) ⊆
      tube (normalizedRadius r s) (z i) (u i))
    (hS : SlabBound (doubled r y w) L (fun _ => True) (fun i => tube s (x i) (v i))) :
    ∀ a t ρ, ‖a‖ = 1 → 0 < ρ →
      ENNReal.ofReal ({i | tube (normalizedRadius r s) (z i) (u i) ⊆
        ball 0 1 ∩ slab a t ρ}.ncard : ℝ) ≤
      ENNReal.ofReal ((L * n / (contraction ^ 3 * M)) * M) *
        volume (ball (0 : Space) 1 ∩ slab a t ρ) := by
  have hs := slabBound_affine_image (normalize e y w r hr).toAffineEquiv (jacobian r)
    (normalize_volume e y w hr) hS
  have hh := slab_count_of_bound (by norm_num : 0 < contraction ^ 3)
    (normalize_doubled_volume_lower e hw hr) (normalize_doubled_subset_ball e hew hr hr1)
    j hj (fun i => Set.image_mono ((hT i).trans (tube_subset_doubled hr.le y w))) hcover hs
  have hMc : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  have he : L * n / (contraction ^ 3 * M) * M = L * n / contraction ^ 3 := by field_simp
  simpa only [he] using hh

lemma normalized_density (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space)
    {r s lam θ : ℝ} (hr : 0 < r) (hs : 0 < s) (hlam : 0 ≤ lam)
    {M : ℕ} (Y : Fin M → Set Space)
    (hY : ∀ i, ENNReal.ofReal (lam * s ^ 2) ≤ volume (Y i))
    (hθ : (normalizedRadius r s) ^ θ ≤ contraction * lam / 16) :
    ENNReal.ofReal ((normalizedRadius r s) ^ θ * M * (normalizedRadius r s) ^ 2) ≤
      ∑ i, volume (normalize e y w r hr '' Y i) := by
  have hi (i : Fin M) :
      ENNReal.ofReal ((normalizedRadius r s) ^ θ * (normalizedRadius r s) ^ 2) ≤
        volume (normalize e y w r hr '' Y i) := by
    rw [normalize_volume]
    calc
      _ ≤ ENNReal.ofReal ((contraction * lam / 16) * (normalizedRadius r s) ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hθ (sq_nonneg _))
      _ = ENNReal.ofReal (jacobian r) * ENNReal.ofReal (lam * s ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [jacobian, normalizedRadius]
        ring
      _ ≤ _ := mul_le_mul_right (hY i) _
  calc
    _ = ∑ _i : Fin M, ENNReal.ofReal ((normalizedRadius r s) ^ θ * (normalizedRadius r s) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg M)]
      congr 1
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hi i

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
