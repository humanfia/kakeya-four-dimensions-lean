-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoarseNormalize.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseGeometry

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Pointwise

noncomputable section

def uniformMap {c : ℝ} (hc : 0 < c) : Space ≃ᴬ[ℝ] Space :=
  (LinearEquiv.smulOfNeZero ℝ Space c hc.ne').toContinuousLinearEquiv.toContinuousAffineEquiv

@[simp] theorem uniformMap_apply {c : ℝ} (hc : 0 < c) (p : Space) :
    uniformMap hc p = c • p := rfl

theorem uniformMap_volume {c : ℝ} (hc : 0 < c) (W : Set Space) :
    volume (uniformMap hc '' W) = ENNReal.ofReal (c ^ 3) * volume W := by
  change volume ((fun p : Space => c • p) '' W) = _
  change volume (c • W) = _
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_pos (by positivity)]

theorem uniformMap_mem_slab_iff {c : ℝ} (hc : 0 < c) (u p : Space) (t r : ℝ) :
    |inner ℝ u (uniformMap hc p) - t| ≤ r ↔ |inner ℝ u p - t / c| ≤ r / c := by
  have he : inner ℝ u (uniformMap hc p) - t = c * (inner ℝ u p - t / c) := by
    rw [uniformMap_apply, inner_smul_right]
    field_simp
  rw [he, abs_mul, abs_of_pos hc, le_div_iff₀ hc, mul_comm]

theorem uniformMap_ball_subset {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    uniformMap hc '' ball (0 : Space) 1 ⊆ ball 0 1 := by
  rintro _ ⟨p, hp, rfl⟩
  rw [mem_ball, dist_zero_right] at hp ⊢
  rw [uniformMap_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  exact (mul_lt_mul_of_pos_left hp hc).trans_le (by simpa using hc1)

theorem uniformMap_carrier_subset {c L ρ : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hcL : c * L ≤ 1) (z w : Space) :
    uniformMap hc '' Carrier L ρ (z - (1 / 2 : ℝ) • w) w ⊆
      Tube (c * ρ) (c • z - (1 / 2 : ℝ) • w) w := by
  have h := wz_affine_robust_cluster_estimate.image_tube_extend (uniformMap hc)
    (z - (1 / 2 : ℝ) • w + ((1 - L) / 2) • w) (L • w) w
    (δ := ρ) (l := c * L) (A := c) hc (mul_nonneg hc.le hL) hcL
    (by change c • (L • w) = (c * L) • w; rw [smul_smul])
    (by intro p q; simp only [uniformMap_apply, dist_smul₀, Real.norm_eq_abs, abs_of_pos hc]; rfl)
  have hmid : z - (1 / 2 : ℝ) • w + ((1 - L) / 2) • w + (1 / 2 : ℝ) • (L • w) = z := by module
  simpa only [Carrier, Tube, wz_affine_robust_cluster_estimate.tube, uniformMap_apply, hmid] using h

/-- A fixed contraction turns every factoring carrier into a unit tube in the unit ball. -/
theorem normalized_factoring_carrier {b : ℝ} (hb : b ≤ 1 / 3)
    {z : Space} (hz : ‖z‖ < 13) (e : Space ≃ₗᵢ[ℝ] Space) :
    let w := e.symm (EuclideanSpace.single 2 (1 : ℝ))
    let x := (1 / 100 : ℝ) • z - (1 / 2 : ℝ) • w
    ‖w‖ = 1 ∧ uniformMap (by norm_num : (0 : ℝ) < 1 / 100) '' factoringCarrier b z e ⊆
      Tube ((3 / 100 : ℝ) * b) x w ∧
      Tube ((3 / 100 : ℝ) * b) x w ⊆ ball 0 1 := by
  dsimp only
  have hw : ‖e.symm (EuclideanSpace.single 2 (1 : ℝ))‖ = 1 := by simp
  refine ⟨hw, ?_, ?_⟩
  · have hh := uniformMap_carrier_subset (by norm_num : (0 : ℝ) < 1 / 100)
      (by norm_num : (0 : ℝ) ≤ 8) (by norm_num : (1 / 100 : ℝ) * 8 ≤ 1) z
      (e.symm (EuclideanSpace.single 2 1)) (ρ := 3 * b)
    simpa only [factoringCarrier, show (1 / 100 : ℝ) * (3 * b) = (3 / 100 : ℝ) * b by ring] using hh
  · apply wz_affine_robust_cluster_estimate.centered_tube_subset_ball hw
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 100)]
      linarith
    · linarith

namespace Interfaces

/-- Convex counts pass through a uniform contraction and enlargement to unit tubes. -/
theorem normalized_carrier_katz {c ρ M : ℝ} (hc : 0 < c) {N : ℕ}
    (Q : Fin N → Set V) (x v : Fin N → V)
    (hcover : ∀ j, uniformMap hc '' Q j ⊆ T (c * ρ) (x j) (v j))
    (hK : ∀ W, Convex ℝ W → o (q {j | Q j ⊆ W} * ρ ^ 2) ≤ o M * μ W) :
    K (c * ρ) (M / c) N x v := by
  intro W hW
  let W' := uniformMap hc ⁻¹' W
  have hW' : Convex ℝ W' := hW.affine_preimage (uniformMap hc).toAffineEquiv.toAffineMap
  have hq : q {j | T (c * ρ) (x j) (v j) ⊆ W} ≤ q {j | Q j ⊆ W'} := by
    apply Nat.cast_le.mpr
    apply Set.ncard_mono
    intro j hj p hp
    exact hj (hcover j (mem_image_of_mem _ hp))
  have hk : o (q {j | T (c * ρ) (x j) (v j) ⊆ W} * ρ ^ 2) ≤ o M * μ W' :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hq (sq_nonneg _))).trans (hK W' hW')
  have hvol : o (c ^ 3) * μ W' = μ W := by
    rw [o, μ, ← uniformMap_volume hc]
    congr 1
    exact (uniformMap hc).surjective.image_preimage W
  calc
    _ = o (c ^ 2) * o (q {j | T (c * ρ) (x j) (v j) ⊆ W} * ρ ^ 2) := by
      rw [o, ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      ring
    _ ≤ o (c ^ 2) * (o M * μ W') := mul_le_mul_right hk _
    _ = o (M / c) * (o (c ^ 3) * μ W') := by
      rw [← mul_assoc, ← mul_assoc, o, ← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_mul' (by positivity : (0 : ℝ) ≤ c ^ 3)]
      congr 2
      field_simp
    _ = _ := by rw [hvol]

/-- The slab reference ball contracts into the unit ball, so the coarse slab count
survives normalization and extension with only its volume scaling loss. -/
theorem normalized_carrier_frostman {c d l : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) {N : ℕ}
    (Q : Fin N → Set V) (x v : Fin N → V)
    (hcover : ∀ j, uniformMap hc '' Q j ⊆ T d (x j) (v j))
    (hF : ∀ (u : V) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      o (q {j | Q j ⊆ {p | |inner ℝ u p - t| ≤ r}}) ≤
        o (l * N) * μ (I ∩ {p | |inner ℝ u p - t| ≤ r})) :
    F d (l / c ^ 3) N x v := by
  intro u t r hu hr
  let Wold := I ∩ {p : V | |inner ℝ u p - t / c| ≤ r / c}
  let Wnew := I ∩ {p : V | |inner ℝ u p - t| ≤ r}
  have hcnt : q {j | T d (x j) (v j) ⊆ Wnew} ≤
      q {j | Q j ⊆ {p | |inner ℝ u p - t / c| ≤ r / c}} := by
    apply Nat.cast_le.mpr
    apply Set.ncard_mono
    intro j hj p hp
    apply (uniformMap_mem_slab_iff hc u p t r).mp
    exact (hj (hcover j (mem_image_of_mem _ hp))).2
  have hvol : o (c ^ 3) * μ Wold ≤ μ Wnew := by
    rw [o, μ, ← uniformMap_volume hc]
    apply measure_mono
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨uniformMap_ball_subset hc hc1 (mem_image_of_mem _ hp.1),
      (uniformMap_mem_slab_iff hc u p t r).mpr hp.2⟩
  have hh := (ENNReal.ofReal_le_ofReal hcnt).trans (hF u (t / c) (r / c) hu (div_pos hr hc))
  change o (q {j | T d (x j) (v j) ⊆ Wnew}) ≤ o (l / c ^ 3 * N) * μ Wnew
  calc
    _ ≤ o (l * N) * μ Wold := hh
    _ = o (l / c ^ 3 * N) * (o (c ^ 3) * μ Wold) := by
      rw [← mul_assoc, o, ← ENNReal.ofReal_mul' (by positivity : (0 : ℝ) ≤ c ^ 3)]
      congr 2
      field_simp
    _ ≤ _ := mul_le_mul_right hvol _

end Interfaces

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
