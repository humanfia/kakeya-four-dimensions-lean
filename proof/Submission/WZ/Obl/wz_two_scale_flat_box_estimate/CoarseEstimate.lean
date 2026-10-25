-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.CoarseEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.CoarseBoxGeometry
import Submission.WZ.Obl.wz_flat_factored_improvement.CoarseCounts
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyEstimate

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement
  (BodyEstimate BodyGeometry BodyConvexCount BodySlabCount BodyPacking bodyWeight)

noncomputable def coarseConstant (σ ω A : ℝ) : ℝ :=
  A * (512 : ℝ) ^ (-ω) * (262144 : ℝ) ^ (σ / 2)

lemma coarseConstant_pos {σ ω A : ℝ} (hA : 0 < A) : 0 < coarseConstant σ ω A := by
  unfold coarseConstant
  positivity

lemma coarse_factorization {σ ω ε A δ a b c D l q : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hD : 0 < D) (hl : 0 < l) (hq : 0 < q) :
    A * (δ ^ (2 : ℕ)) ^ (ε / 2) * (b / 512) ^ ω *
        bodyWeight σ ((1 / 262144 : ℝ) * (216 * (a * b * c))) (216 * D) l (216 * D) q =
      (1 / 262144 : ℝ) * (coarseConstant σ ω A * δ ^ ε * b ^ ω *
        D ^ (-1 + σ / 2) * l ^ (-σ) * q ^ (1 - σ) * (a * b * c) ^ (1 - σ / 2)) := by
  unfold coarseConstant bodyWeight
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Real.log_one]
  ring

set_option maxHeartbeats 600000 in
/-- The coarse use of E on enlarged boxes, with all three side lengths from the
frozen statement retained. -/
theorem coarse_box_estimate {σ ω : ℝ} (hF : BodyEstimate σ ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ A η d : ℝ, 0 < A ∧ 0 < η ∧ 0 < d ∧ d ≤ 1 / 100 ∧
    ∀ δ a b c D l : ℝ, 0 < δ → δ ≤ d → δ ≤ a → a ≤ b → b ≤ c → 1 ≤ c → c ≤ 8 →
    1 ≤ D → 1 ≤ l →
    ∀ (q : ℕ) (z : Fin q → Space) (e : Fin q → Space ≃ₗᵢ[ℝ] Space) (Z : Fin q → Set Space),
    0 < q → (q : ℝ) ≤ δ ^ (-100 : ℝ) →
    (∀ j, (Box a b c (z j) (e j) ∩ ball (0 : Space) 1).Nonempty) →
    (∀ j, MeasurableSet (Z j)) → (∀ j, Z j ⊆ Box (6 * a) (6 * b) (6 * c) (z j) (e j)) →
    (∀ j, ENNReal.ofReal (δ ^ η * (a * b)) ≤ volume (Z j)) →
    BodyConvexCount (fun j => Box a b c (z j) (e j)) (a * b * c) D →
    BodySlabCount (fun j => coarseBox a b c (z j) (e j)) l →
    ENNReal.ofReal (A * δ ^ ε * b ^ ω * D ^ (-1 + σ / 2) * l ^ (-σ) *
      (q : ℝ) ^ (1 - σ) * (a * b * c) ^ (1 - σ / 2)) ≤ volume (⋃ j, Z j) := by
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ := hF (ε / 2) (by positivity)
  let d := min d₀ (min (1 / 4096) ((1 / 1728 : ℝ) ^ η⁻¹))
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨coarseConstant σ ω A, η, d, coarseConstant_pos hA, hη, hd,
    (min_le_left _ _).trans hd₀small, ?_⟩
  intro δ a b c D l hδ hδd hδa hab hbc hc hc8 hD hl q z e Z hq hqmax hmeet hZm hZP hZd hconv hslab
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hδsmall : δ ≤ 1 / 4096 := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hδroot : δ ≤ (1 / 1728 : ℝ) ^ η⁻¹ :=
    hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδpow : δ ^ η ≤ 1 / 1728 :=
    (Real.le_rpow_inv_iff_of_pos hδ.le (by norm_num) hη).mp hδroot
  have hdscale : δ ^ (2 : ℕ) ≤ d₀ :=
    (show δ ^ (2 : ℕ) ≤ δ by nlinarith).trans (hδd.trans (min_le_left _ _))
  have hinterior : δ ^ (2 : ℕ) ≤ a / 64 := by nlinarith
  have hwidth : δ ^ (2 : ℕ) ≤ b / 512 := by nlinarith
  have hqmax' : (q : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) := by
    rw [← Real.rpow_natCast_mul hδ.le]
    exact hqmax.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num))
  let J : ℝ := 1 / 262144
  let w := J * (216 * (a * b * c))
  let U := fun j => coarseBox a b c (z j) (e j)
  let Y := fun j => boxContraction '' Z j
  have hJ : 0 < J := by norm_num [J]
  have hw : 0 < w := by dsimp [w]; positivity
  have hconv' : BodyConvexCount U w (216 * D) :=
    ((hconv.enlarge (by positivity) (fun j => box_subset_sixfold ha.le hb.le hcpos.le (z j) (e j))).scale_weight
      (by norm_num : (0 : ℝ) ≤ 216)).affine_image (by positivity) hJ boxContraction boxContraction_volume
  have hpack : BodyPacking U w (216 * D) := hconv'.packing hw.le
  have hgeom : BodyGeometry U (fun j => boxContraction (z j)) (δ ^ (2 : ℕ)) (b / 512) w :=
    coarse_box_geometry ha hab hbc hc hc8 hinterior z e hmeet
  have hYd : ∀ j, ENNReal.ofReal ((δ ^ (2 : ℕ)) ^ η) * volume (U j) ≤ volume (Y j) := by
    intro j
    have hsmall : 1728 * (δ ^ (2 : ℕ)) ^ η ≤ δ ^ η := by
      rw [← Real.rpow_natCast_mul hδ.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * η = η + η by ring, Real.rpow_add hδ]
      nlinarith [mul_le_mul_of_nonneg_left hδpow (Real.rpow_nonneg hδ.le η)]
    have hh : 216 * c * (δ ^ (2 : ℕ)) ^ η ≤ δ ^ η := by
      have ht := mul_le_mul_of_nonneg_right hc8 (by positivity : 0 ≤ 216 * (δ ^ (2 : ℕ)) ^ η)
      nlinarith
    change ENNReal.ofReal _ * volume (coarseBox a b c (z j) (e j)) ≤ volume (boxContraction '' Z j)
    rw [coarseBox_volume ha.le hb.le hcpos.le, boxContraction_volume]
    calc
      _ ≤ ENNReal.ofReal J * ENNReal.ofReal (δ ^ η * (a * b)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hJ.le]
        apply ENNReal.ofReal_le_ofReal
        dsimp [J]
        nlinarith only [mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (1 / 262144 : ℝ) * a * b)]
      _ ≤ _ := mul_le_mul' le_rfl (hZd j)
  have hbound := H (δ ^ (2 : ℕ)) (by positivity) hdscale q U Y (fun j => boxContraction (z j))
    (b / 512) w (216 * D) l (216 * D) hq hqmax' hwidth hw (by linarith) hl
    (by linarith) hgeom
    (fun j => boxContraction.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hZm j))
    (fun j => image_mono (hZP j)) hYd hconv' hslab hpack
  have hYvol : volume (⋃ j, Y j) = ENNReal.ofReal J * volume (⋃ j, Z j) := by
    rw [← boxContraction_volume, image_iUnion]
  rw [hYvol] at hbound
  have he := coarse_factorization (σ := σ) (ω := ω) (ε := ε) (q := (q : ℝ)) hA hδ ha hb hcpos
    (zero_lt_one.trans_le hD) (zero_lt_one.trans_le hl) (by exact_mod_cast hq)
  change A * (δ ^ (2 : ℕ)) ^ (ε / 2) * (b / 512) ^ ω * bodyWeight σ w (216 * D) l (216 * D) q = _ at he
  rw [he, ENNReal.ofReal_mul hJ.le] at hbound
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hJ).ne' ENNReal.ofReal_ne_top).mp hbound

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
