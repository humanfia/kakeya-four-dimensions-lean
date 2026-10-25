-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.CoarseFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseNet
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseSlabs
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Packets

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

noncomputable abbrev coarseFraction : ℝ :=
  WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst * coarseContraction / 8064

noncomputable abbrev coarseConvexCoefficient (a b D : ℝ) : ℝ :=
  (144 / coarseContraction) * D * b / a

noncomputable abbrev coarseMassFraction (a b D : ℝ) : ℝ := coarseFraction * (a / b) / D ^ 2

noncomputable abbrev coarseSlabCoefficient (a b D l : ℝ) : ℝ :=
  D * l * coarseContraction⁻¹ ^ 3 / coarseMassFraction a b D

theorem coarseFraction_pos : 0 < coarseFraction := by
  exact div_pos (mul_pos WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst_pos
    (by norm_num)) (by norm_num)

theorem coarseFraction_le_one : coarseFraction ≤ 1 := by
  norm_num [coarseFraction, coarseContraction, WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst]

theorem coarse_coefficient_identity {a b D : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (coarseRadius b) ^ 2 / (a * b) * D * coarseContraction⁻¹ ^ 3 =
      coarseConvexCoefficient a b D := by
  dsimp [coarseRadius, coarseConvexCoefficient]
  field_simp
  ring

theorem coarse_cardinality_lower {a b D M q : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (h : WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst * q ≤
      M * (56 * coarseConvexCoefficient a b D)) :
    coarseFraction * (a / b) / D * q ≤ M := by
  have hc : 0 < 56 * coarseConvexCoefficient a b D := by dsimp [coarseConvexCoefficient]; positivity
  have he : (56 * coarseConvexCoefficient a b D) * (coarseFraction * (a / b) / D * q) =
      WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst * q := by
    dsimp [coarseConvexCoefficient, coarseFraction]
    field_simp
    ring
  apply (mul_le_mul_iff_right₀ hc).mp
  rw [he]
  simpa only [mul_comm] using h

/-- The separated coarse net inherits convex and slab counts with explicit constants. -/
theorem coarse_factored_family {a b δ D l : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hδ : 0 < δ) (hD : 0 < D) (hl : 0 ≤ l)
    {n q N : ℕ} (hq : 0 < q) (hN : 0 < N)
    (x v : Fin n → Space) (e : Fin q → AffineIsometryEquiv ℝ Space Space)
    (hB : ∀ i, tube δ (x i) (v i) ⊆ unitBall)
    (hlower : ∀ j, N ≤ Set.ncard {i | tube δ (x i) (v i) ⊆ e j '' standardPrism a b})
    (hcover : (n : ℝ) ≤ q * D * N)
    (hdegree : ∀ i, (Set.ncard {j | tube δ (x i) (v i) ⊆ e j '' standardPrism a b} : ℝ) ≤ D)
    (hcount : PrismCount a b D (fun j => e j '' standardPrism a b))
    (hslab : SlabCount δ l x v) :
    ∃ (M : ℕ) (j : Fin M → Fin q) (z w : Fin M → Space),
      0 < M ∧ Function.Injective j ∧ (∀ i, ‖w i‖ = 1) ∧
      (∀ i, tube (coarseRadius b) (z i) (w i) ⊆ unitBall) ∧
      (∀ i k, i ≠ k → volume (tube (coarseRadius b) (z i) (w i) ∩
        tube (coarseRadius b) (z k) (w k)) ≤
          (1 / 2 : ENNReal) * volume (tube (coarseRadius b) (z i) (w i))) ∧
      (∀ i, (fun p : Space => coarseContraction • p) ''
        thickening (2 * b) (e (j i) '' standardPrism a b) ⊆ tube (coarseRadius b) (z i) (w i)) ∧
      ConvexCount (coarseRadius b) (coarseConvexCoefficient a b D) z w ∧
      SlabCount (coarseRadius b) (coarseSlabCoefficient a b D l) z w ∧
      coarseMassFraction a b D * n ≤ (M : ℝ) * N := by
  have hb : 0 < b := ha.trans_le hab
  have hN0 : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hκ : 0 < coarseContraction := by norm_num
  have hmeet (j : Fin q) : (e j '' standardPrism a b ∩ unitBall).Nonempty := by
    apply packet_meets_ball hδ x v hB
    rw [packetSize_eq]
    exact hN.trans_le (hlower j)
  obtain ⟨M, j, z, w, hM, hj, hw, hball, hsep, hbig, hconv, hmass⟩ :=
    coarse_prism_net ha hab hb1 hD.le hq e hmeet hcount
  rw [coarse_coefficient_identity ha hb] at hconv hmass
  have hM0 : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hMlower := coarse_cardinality_lower ha hb hD hmass
  have hF : 0 < coarseMassFraction a b D := by
    dsimp [coarseMassFraction]
    exact div_pos (mul_pos coarseFraction_pos (div_pos ha hb)) (sq_pos_of_pos hD)
  have hMN : coarseMassFraction a b D * n ≤ (M : ℝ) * N := by
    calc
      _ ≤ coarseMassFraction a b D * ((q : ℝ) * D * N) :=
        mul_le_mul_of_nonneg_left hcover hF.le
      _ = (coarseFraction * (a / b) / D * q) * N := by
        dsimp [coarseMassFraction]
        field_simp
      _ ≤ (M : ℝ) * N := mul_le_mul_of_nonneg_right hMlower hN0.le
  have hinc : ∀ i k, tube δ (x i) (v i) ⊆ e (j k) '' standardPrism a b →
      (fun p : Space => coarseContraction • p) '' tube δ (x i) (v i) ⊆
        tube (coarseRadius b) (z k) (w k) := by
    intro i k hik
    exact (Set.image_mono (hik.trans (self_subset_thickening (by positivity) _))).trans (hbig k)
  have hslab' := slabCount_to_coarse hκ (by norm_num : coarseContraction ≤ 1)
    hl hN0 hD.le hM x v z w (fun i k => tube δ (x i) (v i) ⊆ e (j k) '' standardPrism a b)
    hB hslab
    (fun k => Nat.cast_le.mpr (hlower (j k)))
    (fun i => (Nat.cast_le.mpr (subfamily_count j hj
      (fun k => tube δ (x i) (v i) ⊆ e k '' standardPrism a b))).trans (hdegree i))
    hinc
  refine ⟨M, j, z, w, hM, hj, hw, hball, hsep, hbig, hconv,
    slabCount_mono ?_ hslab', hMN⟩
  dsimp [coarseSlabCoefficient]
  apply (div_le_div_iff₀ (mul_pos hN0 hM0) hF).mpr
  have hh := mul_le_mul_of_nonneg_left hMN
    (by positivity : 0 ≤ D * l * coarseContraction⁻¹ ^ 3)
  nlinarith only [hh]

end WangZahlLot.Obl.wz_nonflat_factored_improvement
