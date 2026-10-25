-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.SlopeProjection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CartesianProjection
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.SlopeDirections

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- Normalizing `(1,t)` does not enlarge the radius of a cover. -/
theorem Covers.unitSlope_linear {δ t : ℝ} (hδ : 0 ≤ δ)
    {P : Set (ℝ × ℝ)} {m : ℕ} {cc : Fin m → ℝ}
    (hcov : Covers δ ((fun p : ℝ × ℝ => p.1 + t * p.2) '' P) cc) :
    Covers δ ((fun p : ℝ × ℝ => unitSlope t 0 * p.1 + unitSlope t 1 * p.2) '' P)
      (fun j => ‖cartesianPoint (1, t)‖⁻¹ * cc j) := by
  have hn : 0 < ‖cartesianPoint (1, t)‖ := zero_lt_one.trans_le (slope_vector_norm t)
  have hni : ‖cartesianPoint (1, t)‖⁻¹ ≤ 1 := (inv_le_one₀ hn).mpr (slope_vector_norm t)
  rintro z ⟨p, hp, rfl⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov ⟨p, hp, rfl⟩)
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  change dist (unitSlope t 0 * p.1 + unitSlope t 1 * p.2)
    (‖cartesianPoint (1, t)‖⁻¹ * cc j) ≤ δ
  rw [Real.dist_eq, unitSlope_zero, unitSlope_one,
    show ‖cartesianPoint (1, t)‖⁻¹ * p.1 + ‖cartesianPoint (1, t)‖⁻¹ * t * p.2 -
      ‖cartesianPoint (1, t)‖⁻¹ * cc j =
      ‖cartesianPoint (1, t)‖⁻¹ * (p.1 + t * p.2 - cc j) by ring,
    abs_mul, abs_of_pos (inv_pos.mpr hn)]
  have hj' : |p.1 + t * p.2 - cc j| ≤ δ := by simpa only [Metric.mem_closedBall, Real.dist_eq] using hj
  exact (mul_le_mul_of_nonneg_left hj' (inv_nonneg.mpr hn.le)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hni hδ)

theorem slope_projection_count (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ C D E σ τ : ℝ,
      0 < δ → δ ≤ δ₀ → 1 ≤ C → 1 ≤ D → 1 ≤ E → 1 ≤ σ + τ →
      ∀ (A B : Finset ℝ), A.Nonempty → B.Nonempty →
        RealFiniteFrostman δ C σ A → RealFiniteFrostman δ D τ B →
        ∀ (I : Type) [Fintype I] [Nonempty I] (t : I → ℝ),
          IndexedRealFrostman δ E t → (∀ i, |t i| ≤ 1) →
          ∃ i, ∀ (m : ℕ) (cc : Fin m → ℝ),
            Covers δ ((fun p : ℝ × ℝ => p.1 + t i * p.2) ''
              (↑(A ×ˢ B) : Set (ℝ × ℝ))) cc →
            δ ^ (ε - 1) ≤ (max (C * D) (8 * E)) ^ 2 * (m : ℝ) := by
  obtain ⟨δ₀, hδ₀, hcount⟩ := cartesian_projection_count ε hε
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ C D E σ τ hδ hsmall hC hD hE hs A B hA hB hAF hBF I _ _ t ht htrange
  obtain ⟨i, hi⟩ := hcount δ C D (8 * E) σ τ hδ hsmall hC hD (by linarith) hs
    A B hA hB hAF hBF I (fun i => unitSlope (t i))
    (indexedFrostman_unitSlope hδ (by linarith) htrange ht) (fun i => unitSlope_norm (t i))
  exact ⟨i, fun m cc hcov => hi m _ (hcov.unitSlope_linear hδ.le)⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
