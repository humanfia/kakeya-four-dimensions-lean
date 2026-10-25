-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.BodyCoarse.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyEstimate
import Submission.WZ.Obl.wz_flat_factored_improvement.CoarseCounts
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file BodyCoarse.lean), namespace renamed.

/-!
# Level ii from the accepted body estimate of o065

`body_coarse_estimate` applies `BodyEstimate` (proved from `E` in the accepted o065,
`body_estimate_of_tube_estimate`) to the fixed contraction of the threefold dilates of
`a × b × 2` prisms. Unlike o065's `flat_coarse_estimate`, the convex count is a Frostman
count relative to the number `q` of prisms (constant `F`), and the packing constant `P` is
a separate parameter, so overfilled families are allowed. No separation (half-overlap) of
the prisms is assumed.
-/

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement
  (BodyEstimate BodyGeometry BodyConvexCount BodySlabCount BodyPacking bodyWeight
    StandardPrism dilatedPrism dilatedPrism_norm coarseMap coarseMap_apply coarseMap_volume
    coarsePrism coarsePrism_volume coarse_body_geometry standardPrism_subset_dilated
    prism_center_bound body_slab_of_convex_count)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Fewer enlarged bodies fit in a container. -/
theorem bodyPacking_enlarge {n : ℕ} {U V : Fin n → Set E3} {w P : ℝ}
    (hw : 0 ≤ w) (h : BodyPacking U w P) (hUV : ∀ i, U i ⊆ V i) : BodyPacking V w P := by
  intro Q hQ
  have hn : Set.ncard {i | V i ⊆ Q} ≤ Set.ncard {i | U i ⊆ Q} :=
    Set.ncard_mono (fun i hi => (hUV i).trans hi)
  have hs : Real.sqrt (Set.ncard {i | V i ⊆ Q} : ℝ) ≤ Real.sqrt (Set.ncard {i | U i ⊆ Q} : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hn)
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hs hw)).trans (h Q hQ)

/-- Scaling the weight and the packing constant together. -/
theorem bodyPacking_scale {n : ℕ} {U : Fin n → Set E3} {w P C : ℝ}
    (hC : 0 ≤ C) (h : BodyPacking U w P) : BodyPacking U (C * w) (C * P) := by
  intro Q hQ
  calc
    _ = ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (Set.ncard {i | U i ⊆ Q} : ℝ) * w) := by
      rw [← ENNReal.ofReal_mul hC]; congr 1; ring
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal P * volume Q) := mul_le_mul' le_rfl (h Q hQ)
    _ = _ := by rw [ENNReal.ofReal_mul hC, mul_assoc]

/-- The contracted dilated prisms meeting the unit ball lie in the open unit ball. -/
theorem coarsePrism_subset_ball {a b : ℝ} (hab : a ≤ b) (hb2 : b ≤ 2)
    (e : AffineIsometryEquiv ℝ E3 E3)
    (hmeet : (e '' StandardPrism a b ∩ ball (0 : E3) 1).Nonempty) :
    coarsePrism e a b ⊆ ball (0 : E3) 1 := by
  rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  have hn : ‖p‖ ≤ 12 := by
    convert dilatedPrism_norm (by norm_num : (0 : ℝ) ≤ 3) hab hb2 hp using 1 <;> norm_num
  have hc := prism_center_bound hab hb2 e hmeet
  have hd : dist (e p) (e 0) = ‖p‖ := by simp
  have hh := dist_triangle (e p) (e 0) 0
  rw [hd, dist_zero_right, dist_zero_right] at hh
  apply mem_ball_zero_iff.mpr
  simp only [coarseMap_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 32)]
  linarith

/-- The exact exponent bookkeeping of `body_coarse_estimate`. -/
theorem body_coarse_factorization {σ u ε A δ a b F P q : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b) (hF : 0 < F) (hP : 0 < P)
    (hq : 0 < q) :
    A * (δ ^ (2 : ℕ)) ^ (ε / 2) * (b / 64) ^ u *
        bodyWeight σ ((1 / 32768 : ℝ) * (432 * (a * b))) (432 * (F * q * (a * b)))
          (262144 * F) (432 * P) q =
      (1 / 32768 : ℝ) * (A * (64 : ℝ) ^ (-u) * (432 : ℝ) ^ (-1 + 3 / 2 * σ) *
        (262144 : ℝ) ^ (-σ) * (432 : ℝ) ^ (-σ) * (432 : ℝ) ^ (1 - σ / 2) *
        (32768 : ℝ) ^ (σ / 2) * δ ^ ε * b ^ u * F ^ (-1 + σ / 2) * P ^ (-σ) *
        (q * (a * b) ^ 2) ^ (σ / 2)) := by
  unfold bodyWeight
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_inv,
    Real.log_rpow, Real.log_pow, Real.log_one]
  ring

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement
  (BodyEstimate BodyGeometry BodyConvexCount BodySlabCount BodyPacking bodyWeight
    StandardPrism dilatedPrism coarseMap coarseMap_volume coarsePrism coarsePrism_volume
    coarse_body_geometry standardPrism_subset_dilated body_slab_of_convex_count)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000 in
/-- Level ii: the body estimate for the contracted threefold dilates of `a × b × 2` prisms,
with a Frostman count of constant `F` relative to the number `q` of prisms and a separate
packing constant `P`. No separation of the prisms is assumed. -/
theorem body_coarse_estimate {σ u : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hF : BodyEstimate σ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ A η d : ℝ, 0 < A ∧ 0 < η ∧ 0 < d ∧ d ≤ 1 / 100 ∧
    ∀ δ a b F P : ℝ, 0 < δ → δ ≤ d → δ ≤ a → a ≤ b → b ≤ 2 → 1 ≤ F → 1 ≤ P →
    ∀ (q : ℕ) (e : Fin q → AffineIsometryEquiv ℝ E3 E3) (Z : Fin q → Set E3),
    0 < q → (q : ℝ) ≤ δ ^ (-100 : ℝ) →
    (∀ j, (e j '' StandardPrism a b ∩ ball (0 : E3) 1).Nonempty) →
    (∀ j, MeasurableSet (Z j)) → (∀ j, Z j ⊆ e j '' dilatedPrism 3 a b) →
    (∀ j, ENNReal.ofReal (δ ^ η * (a * b)) ≤ volume (Z j)) →
    (∀ Q : Set E3, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {j | e j '' StandardPrism a b ⊆ Q} : ℝ) ≤
        ENNReal.ofReal (F * q) * volume Q) →
    BodyPacking (fun j => e j '' StandardPrism a b) (a * b) P →
    ENNReal.ofReal (A * δ ^ ε * b ^ u * F⁻¹ * P ^ (-σ) * ((q : ℝ) * (a * b) ^ 2) ^ (σ / 2)) ≤
      volume (⋃ j, Z j) := by
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ := hF (ε / 2) (by positivity)
  let d := min d₀ (min (1 / 2048) ((1 / 432 : ℝ) ^ η⁻¹))
  have hd : 0 < d := by dsimp [d]; positivity
  let C : ℝ := A * (64 : ℝ) ^ (-u) * (432 : ℝ) ^ (-1 + 3 / 2 * σ) *
    (262144 : ℝ) ^ (-σ) * (432 : ℝ) ^ (-σ) * (432 : ℝ) ^ (1 - σ / 2) * (32768 : ℝ) ^ (σ / 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, η, d, hC, hη, hd, (min_le_left _ _).trans hd₀small, ?_⟩
  intro δ a b F P hδ hδd hδa hab hb2 hF1 hP1 q e Z hq hqmax hmeet hZm hZP hZd hfrost hpack
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hFpos : 0 < F := zero_lt_one.trans_le hF1
  have hPpos : 0 < P := zero_lt_one.trans_le hP1
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hδsmall : δ ≤ 1 / 2048 := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hδroot : δ ≤ (1 / 432 : ℝ) ^ η⁻¹ :=
    hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
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
  have hJ : 0 < J := by norm_num [J]
  let w : ℝ := J * (432 * (a * b))
  have hw : 0 < w := by dsimp [w]; positivity
  let m : ℝ := 432 * (F * q * (a * b))
  let U := fun j => coarsePrism (e j) a b
  let Y := fun j => coarseMap '' Z j
  let V := fun j => e j '' dilatedPrism 3 a b
  have hinc : ∀ j, e j '' StandardPrism a b ⊆ V j :=
    fun j => image_mono (standardPrism_subset_dilated ha.le hb.le (by norm_num))
  have hconv0 : BodyConvexCount (fun j => e j '' StandardPrism a b) (a * b)
      (F * q * (a * b)) := by
    intro Q hQ
    calc
      _ = ENNReal.ofReal (Set.ncard {j | e j '' StandardPrism a b ⊆ Q} : ℝ) *
          ENNReal.ofReal (a * b) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (F * q) * volume Q * ENNReal.ofReal (a * b) :=
        mul_le_mul' (hfrost Q hQ) le_rfl
      _ = _ := by
        rw [mul_comm (ENNReal.ofReal (F * q)) (volume Q), mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), mul_comm (volume Q)]
  have hconv : BodyConvexCount U w m :=
    ((hconv0.enlarge (by positivity) hinc).scale_weight
      (by norm_num : (0 : ℝ) ≤ 432)).affine_image (by positivity) hJ coarseMap coarseMap_volume
  have hpackU : BodyPacking U w (432 * P) :=
    (bodyPacking_scale (by norm_num : (0 : ℝ) ≤ 432)
      (bodyPacking_enlarge (by positivity) hpack hinc)).affine_image
        (by positivity) hJ coarseMap coarseMap_volume
  have hUball : ∀ j, U j ⊆ ball (0 : E3) 1 :=
    fun j => coarsePrism_subset_ball hab hb2 (e j) (hmeet j)
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hslab : BodySlabCount U (262144 * F) := by
    have hh := body_slab_of_convex_count hq hw hm0 hUball hconv
    have heq : 8 * m / (w * q) = 262144 * F := by
      dsimp [m, w, J]
      field_simp
      ring
    rwa [heq] at hh
  have hm1 : 1 ≤ m := by
    let j₀ : Fin q := ⟨0, hq⟩
    have hcard : 1 ≤ Set.ncard {j | e j '' StandardPrism a b ⊆ e j₀ '' StandardPrism a b} :=
      Nat.succ_le_iff.mpr ((Set.ncard_pos (Set.toFinite _)).mpr
        ⟨j₀, show e j₀ '' StandardPrism a b ⊆ e j₀ '' StandardPrism a b from subset_rfl⟩)
    have hconvex : Convex ℝ (e j₀ '' StandardPrism a b) :=
      (WangZahlLot.Obl.wz_flat_factored_improvement.standardPrism_convex a b).affine_image
        (e j₀).toAffineEquiv.toAffineMap
    have hvol : volume (e j₀ '' StandardPrism a b) = ENNReal.ofReal (16 * a * b) := by
      rw [WangZahlLot.Obl.wz_frostman_rigid_copies_volume.affine_volume_image,
        WangZahlLot.Obl.wz_flat_factored_improvement.standardPrism_volume ha.le hb.le]
    have hh := hfrost _ hconvex
    rw [hvol, ← ENNReal.ofReal_mul (by positivity)] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
    have h1 : (1 : ℝ) ≤ F * q * (16 * a * b) :=
      (by exact_mod_cast hcard : (1 : ℝ) ≤ _).trans hh'
    dsimp [m]
    nlinarith
  have hgeom : BodyGeometry U (fun j => coarseMap (e j 0)) (δ ^ (2 : ℕ)) (b / 64) w := by
    have hh := coarse_body_geometry ha hab hb2 hinterior e hmeet
    convert hh using 1
    dsimp [w, J]
    ring
  have hYm : ∀ j, MeasurableSet (Y j) := fun j =>
    coarseMap.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (hZm j)
  have hYU : ∀ j, Y j ⊆ U j := fun j => image_mono (hZP j)
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
        nlinarith only [mul_le_mul_of_nonneg_right hh
          (by positivity : 0 ≤ (1 / 32768 : ℝ) * a * b)]
      _ ≤ _ := mul_le_mul' le_rfl (hZd j)
  have hbound := H (δ ^ (2 : ℕ)) (by positivity) hdscale q U Y (fun j => coarseMap (e j 0))
    (b / 64) w m (262144 * F) (432 * P) hq hqmax' hwidth hw hm1 (by linarith) (by linarith)
    hgeom hYm hYU hYd hconv hslab hpackU
  have hYvol : volume (⋃ j, Y j) = ENNReal.ofReal J * volume (⋃ j, Z j) := by
    rw [← coarseMap_volume, image_iUnion]
  rw [hYvol] at hbound
  have hscalar := body_coarse_factorization (σ := σ) (u := u) (ε := ε) hA hδ ha hb hFpos hPpos hq'
  change A * (δ ^ (2 : ℕ)) ^ (ε / 2) * (b / 64) ^ u *
    bodyWeight σ w m (262144 * F) (432 * P) q = _ at hscalar
  rw [hscalar, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 32768)] at hbound
  have hbound' := (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 32768)).ne'
      ENNReal.ofReal_ne_top).mp hbound
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hbound'
  have hFp : F⁻¹ ≤ F ^ (-1 + σ / 2) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hF1 (by linarith)
  dsimp only [C]
  gcongr

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
