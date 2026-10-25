-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.AffineCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineMap

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

theorem slab_convex (u : Space) (t r : ℝ) :
    Convex ℝ (unitBall ∩ {p | |inner ℝ u p - t| ≤ r}) := by
  apply (convex_ball (0 : Space) 1).inter
  have he : {p : Space | |inner ℝ u p - t| ≤ r} =
      (innerₛₗ ℝ u) ⁻¹' Set.Icc (t - r) (t + r) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, abs_le]
    change (-r ≤ inner ℝ u p - t ∧ inner ℝ u p - t ≤ r) ↔
      (t - r ≤ inner ℝ u p ∧ inner ℝ u p ≤ t + r)
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [he]
  exact (convex_Icc (t - r) (t + r)).linear_preimage (innerₛₗ ℝ u)

/-- Unnormalized containment counts through an affine cover. -/
theorem affine_count_transport (f : AffineEquiv ℝ Space Space)
    {δ r J s K : ℝ} (hJ : 0 < J) (hs : 0 < s) (hK : 0 ≤ K)
    (hvol : ∀ U : Set Space, volume (f '' U) = ENNReal.ofReal J * volume U)
    {n M : ℕ} (x v : Fin n → Space) (z w : Fin M → Space)
    (j : Fin M → Fin n) (hj : Function.Injective j)
    (hcover : ∀ i, f '' tube δ (x (j i)) (v (j i)) ⊆ tube r (z i) (w i))
    (hcount : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) * s) ≤
        ENNReal.ofReal K * volume U) :
    ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {i | tube r (z i) (w i) ⊆ U} : ℝ) ≤
        ENNReal.ofReal (K / (s * J)) * volume U := by
  intro U hU
  have hc := hcount (f ⁻¹' U) (hU.affine_preimage f.toAffineMap)
  have hn : Set.ncard {i | tube r (z i) (w i) ⊆ U} ≤
      Set.ncard {i | tube δ (x i) (v i) ⊆ f ⁻¹' U} := by
    apply le_trans (b := Set.ncard {i | tube δ (x (j i)) (v (j i)) ⊆ f ⁻¹' U})
    · apply Set.ncard_mono
      intro i hi p hp
      exact hi (hcover i ⟨p, hp, rfl⟩)
    · exact subfamily_count j hj (fun i => tube δ (x i) (v i) ⊆ f ⁻¹' U)
  calc
    _ = ENNReal.ofReal s⁻¹ *
        ENNReal.ofReal ((Set.ncard {i | tube r (z i) (w i) ⊆ U} : ℝ) * s) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal s⁻¹ * (ENNReal.ofReal K * volume (f ⁻¹' U)) := by
      apply mul_le_mul' le_rfl
      exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hs.le)).trans hc
    _ = _ := by
      rw [affine_volume_preimage f hJ hvol, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp

theorem convexCount_of_raw_count {r K : ℝ} (_hK : 0 ≤ K)
    {M : ℕ} (z w : Fin M → Space)
    (hcount : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {i | tube r (z i) (w i) ⊆ U} : ℝ) ≤
        ENNReal.ofReal K * volume U) : ConvexCount r (K * r ^ 2) z w := by
  intro U hU
  calc
    _ = ENNReal.ofReal (r ^ 2) *
        ENNReal.ofReal (Set.ncard {i | tube r (z i) (w i) ⊆ U} : ℝ) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg r)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal K * volume U) :=
      mul_le_mul' le_rfl (hcount U hU)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg r)]
      congr 2
      ring

theorem slabCount_of_raw_count {r K : ℝ} {M : ℕ} (hM : 0 < M)
    (z w : Fin M → Space)
    (hcount : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {i | tube r (z i) (w i) ⊆ U} : ℝ) ≤
        ENNReal.ofReal K * volume U) : SlabCount r (K / M) z w := by
  intro u t s hu hs
  have hMc : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  simpa [hMc] using hcount _ (slab_convex u t s)

end WangZahlLot.Obl.wz_nonflat_factored_improvement
