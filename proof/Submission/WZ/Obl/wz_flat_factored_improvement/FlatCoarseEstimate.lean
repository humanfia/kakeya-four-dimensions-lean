-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.FlatCoarseEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.CoarseCounts
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyEstimate

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric

noncomputable def coarseBodyConstant (σ u A : ℝ) : ℝ :=
  A * (64 : ℝ) ^ (-u) * (256 : ℝ) ^ (-σ) * (32768 : ℝ) ^ (σ / 2)

theorem coarseBodyConstant_pos {σ u A : ℝ} (hA : 0 < A) : 0 < coarseBodyConstant σ u A := by
  unfold coarseBodyConstant
  positivity

theorem coarse_body_factorization {σ u ε A δ a b D l q : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b)
    (hD : 0 < D) (hl : 0 < l) (hq : 0 < q) :
    A * (δ ^ (2 : ℕ)) ^ (ε / 2) * (b / 64) ^ u *
        bodyWeight σ ((1 / 32768 : ℝ) * (432 * a * b)) (432 * D) (256 * D ^ 2 * l) (432 * D) q =
      (1 / 32768 : ℝ) * (coarseBodyConstant σ u A * δ ^ ε * b ^ u * D ^ (-1 - 3 / 2 * σ) *
        l ^ (-σ) * q ^ (1 - σ) * (a * b) ^ (1 - σ / 2)) := by
  unfold bodyWeight coarseBodyConstant
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_inv,
    Real.log_rpow, Real.log_pow, Real.log_one]
  ring

set_option maxHeartbeats 600000 in
/-- The second use of the body estimate, on the enlarged coarse prisms. -/
theorem flat_coarse_estimate {σ u : ℝ} (hσhalf : σ ≤ 1 / 2) (hF : BodyEstimate σ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A η d : ℝ, 0 < A ∧ 0 < η ∧ 0 < d ∧ d ≤ 1 / 100 ∧
    ∀ δ a b D l : ℝ, 0 < δ → δ ≤ d → δ ≤ a → a ≤ b → b ≤ 2 → 1 ≤ D → 1 ≤ l →
    ∀ (q : ℕ) (e : Fin q → AffineIsometryEquiv ℝ Space Space) (Z : Fin q → Set Space),
    0 < q → (q : ℝ) ≤ δ ^ (-100 : ℝ) →
    (∀ j, (e j '' StandardPrism a b ∩ ball (0 : Space) 1).Nonempty) →
    (∀ j, MeasurableSet (Z j)) → (∀ j, Z j ⊆ e j '' dilatedPrism 3 a b) →
    (∀ j, ENNReal.ofReal (δ ^ η * (a * b)) ≤ volume (Z j)) →
    BodyConvexCount (fun j => e j '' StandardPrism a b) (a * b) D →
    BodySlabCount (fun j => coarsePrism (e j) a b) (256 * D ^ 2 * l) →
    ENNReal.ofReal (A * δ ^ ε * b ^ u * D ^ (-2 : ℝ) * l ^ (-σ) *
      (q : ℝ) ^ (1 - σ) * (a * b) ^ (1 - σ / 2)) ≤ volume (⋃ j, Z j) := by
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ := hF (ε / 2) (by positivity)
  let d := min d₀ (min (1 / 2048) ((1 / 432 : ℝ) ^ η⁻¹))
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨coarseBodyConstant σ u A, η, d, coarseBodyConstant_pos hA, hη, hd,
    (min_le_left _ _).trans hd₀small, ?_⟩
  intro δ a b D l hδ hδd hδa hab hb2 hD hl q e Z hq hqmax hmeet hZm hZP hZd hconv hslab
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hD' : 0 < D := zero_lt_one.trans_le hD
  have hl' : 0 < l := zero_lt_one.trans_le hl
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hδsmall : δ ≤ 1 / 2048 := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hδroot : δ ≤ (1 / 432 : ℝ) ^ η⁻¹ := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδpow : δ ^ η ≤ 1 / 432 :=
    (Real.le_rpow_inv_iff_of_pos hδ.le (by norm_num) hη).mp hδroot
  have hdscale : δ ^ (2 : ℕ) ≤ d₀ :=
    (show δ ^ (2 : ℕ) ≤ δ by nlinarith).trans (hδd.trans (min_le_left _ _))
  have hinterior : δ ^ (2 : ℕ) ≤ a / 32 := by nlinarith
  have hwidth : δ ^ (2 : ℕ) ≤ b / 64 := by nlinarith
  have hqmax' : (q : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) := by
    rw [← Real.rpow_natCast_mul hδ.le]
    exact hqmax.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num))
  let J : ℝ := 1 / 32768
  let w := J * (432 * a * b)
  let U := fun j => coarsePrism (e j) a b
  let Y := fun j => coarseMap '' Z j
  have hJ : 0 < J := by norm_num [J]
  have hw : 0 < w := by dsimp [w]; positivity
  have hconv' : BodyConvexCount U w (432 * D) := by
    have hinc : ∀ j, e j '' StandardPrism a b ⊆ e j '' dilatedPrism 3 a b :=
      fun j => image_mono (standardPrism_subset_dilated ha.le hb.le (by norm_num))
    have hh := ((hconv.enlarge (by positivity) hinc).scale_weight (by norm_num : (0 : ℝ) ≤ 432)).affine_image
      (by positivity) hJ coarseMap coarseMap_volume
    convert hh using 1 <;> dsimp [U, coarsePrism, w] <;> ring
  have hpack : BodyPacking U w (432 * D) := hconv'.packing hw.le
  have hgeom : BodyGeometry U (fun j => coarseMap (e j 0)) (δ ^ (2 : ℕ)) (b / 64) w :=
    coarse_body_geometry ha hab hb2 hinterior e hmeet
  have hYd : ∀ j, ENNReal.ofReal ((δ ^ (2 : ℕ)) ^ η) * volume (U j) ≤ volume (Y j) := by
    intro j
    have hh : 432 * (δ ^ (2 : ℕ)) ^ η ≤ δ ^ η := by
      rw [← Real.rpow_natCast_mul hδ.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * η = η + η by ring, Real.rpow_add hδ]
      nlinarith [mul_le_mul_of_nonneg_left hδpow (Real.rpow_nonneg hδ.le η)]
    change ENNReal.ofReal _ * volume (coarsePrism (e j) a b) ≤ volume (coarseMap '' Z j)
    rw [coarsePrism_volume ha.le hb.le, coarseMap_volume]
    calc
      _ ≤ ENNReal.ofReal J * ENNReal.ofReal (δ ^ η * (a * b)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hJ.le]
        apply ENNReal.ofReal_le_ofReal
        dsimp [J]
        nlinarith only [mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (1 / 32768 : ℝ) * a * b)]
      _ ≤ _ := mul_le_mul' le_rfl (hZd j)
  have hslab1 : 1 ≤ 256 * D ^ 2 * l := by
    have hD2 : 1 ≤ D ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hD2 hl'.le]
  have hbound := H (δ ^ (2 : ℕ)) (by positivity) hdscale q U Y (fun j => coarseMap (e j 0))
    (b / 64) w (432 * D) (256 * D ^ 2 * l) (432 * D) hq hqmax' hwidth hw
    (by linarith) hslab1
    (by linarith) hgeom
    (fun j => coarseMap.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hZm j))
    (fun j => image_mono (hZP j)) hYd hconv' hslab hpack
  have hYvol : volume (⋃ j, Y j) = ENNReal.ofReal J * volume (⋃ j, Z j) := by
    rw [← coarseMap_volume, image_iUnion]
  rw [hYvol] at hbound
  have hscalar := coarse_body_factorization (σ := σ) (u := u) (ε := ε) hA hδ ha hb hD' hl' hq'
  change A * (δ ^ (2 : ℕ)) ^ (ε / 2) * (b / 64) ^ u * bodyWeight σ w (432 * D)
    (256 * D ^ 2 * l) (432 * D) q = _ at hscalar
  rw [hscalar, ENNReal.ofReal_mul hJ.le] at hbound
  have hbound' := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hJ).ne' ENNReal.ofReal_ne_top).mp hbound
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hbound'
  have hDp : D ^ (-2 : ℝ) ≤ D ^ (-1 - 3 / 2 * σ) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hA' := coarseBodyConstant_pos (σ := σ) (u := u) hA
  gcongr

end WangZahlLot.Obl.wz_flat_factored_improvement
