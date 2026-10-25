-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.FineEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Interfaces
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatBodies
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyEstimate

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement
  (BodyEstimate BodyConvexCount BodySlabCount BodyPacking BodyGeometry bodyWeight
   flatMap flatMap_volume flat_body_geometry closedTube_packing)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (closedTube tube_subset_closedTube closedTube_volume_bounds)

noncomputable def fineConstant (σ ω A : ℝ) : ℝ :=
  A * (1024 : ℝ) ^ (-ω) * (1000 : ℝ) ^ (-σ) * (128 : ℝ) ^ (σ / 2)

lemma fineConstant_pos {σ ω A : ℝ} (hA : 0 < A) : 0 < fineConstant σ ω A := by
  unfold fineConstant
  positivity

lemma fine_factorization {σ ω ε A δ a b m l n : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hl : 0 < l) (hn : 0 < n) :
    A * (δ ^ (2 : ℕ)) ^ (ε / 2) * (δ / (1024 * a)) ^ ω *
        bodyWeight σ ((1 / (128 * a * b)) * δ ^ 2) m l 1000 n =
      (1 / (128 * a * b)) * (fineConstant σ ω A * δ ^ ε * (δ / a) ^ ω *
        m ^ (-1 + 3 / 2 * σ) * l ^ (-σ) * n ^ (1 - σ) *
        δ ^ (2 - σ) * (a * b) ^ (σ / 2)) := by
  unfold fineConstant bodyWeight
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_inv,
    Real.log_rpow, Real.log_pow, Real.log_one]
  ring

lemma closedTube_katz_tao {δ m : ℝ} {n : ℕ} (x v : Fin n → Space)
    (h : WangZahlLot.Obl.wz_tower_balanced_refinement.ConvexCount δ m n x v) :
    BodyConvexCount (fun i => closedTube δ (x i) (v i)) (δ ^ 2) m := by
  intro W hW
  have hh : Set.ncard {i | closedTube δ (x i) (v i) ⊆ W} ≤
      Set.ncard {i | Tube δ (x i) (v i) ⊆ W} :=
    ncard_mono (fun i hi => (tube_subset_closedTube _ _ _).trans hi)
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hh) (sq_nonneg δ))).trans (h W hW)

set_option maxHeartbeats 600000 in
/-- The fine body estimate with global Katz--Tao counting and a separately supplied
slab bound after flattening. This is the local analytic input for two-scale factoring. -/
theorem fine_estimate_from_flattened_slabs {σ ω : ℝ} (hF : BodyEstimate σ ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A η d : ℝ, 0 < A ∧ 0 < η ∧ 0 < d ∧ d ≤ 1 / 100 ∧
    ∀ (δ a b m l : ℝ) (hδ : 0 < δ), δ ≤ d →
    ∀ (hδa : δ ≤ a) (hab : a ≤ b), b ≤ 2 → a ≤ 1 / 100 → 1 ≤ m → 1 ≤ l →
    ∀ (e : AffineIsometryEquiv ℝ Space Space) (n : ℕ) (x v : Fin n → Space)
      (Y : Fin n → Set Space),
    0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → (∀ i, ‖v i‖ = 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ e '' WangZahlLot.Obl.wz_flat_factored_improvement.StandardPrism a b) →
    Distinct δ n x v → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
    (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
    WangZahlLot.Obl.wz_tower_balanced_refinement.ConvexCount δ m n x v →
    BodySlabCount (fun i => flatMap e a b (hδ.trans_le hδa) ((hδ.trans_le hδa).trans_le hab) ''
      closedTube δ (x i) (v i)) l →
    ENNReal.ofReal (A * δ ^ ε * (δ / a) ^ ω * m ^ (-1 + 3 / 2 * σ) * l ^ (-σ) *
      (n : ℝ) ^ (1 - σ) * δ ^ (2 - σ) * (a * b) ^ (σ / 2)) ≤ volume (⋃ i, Y i) := by
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ := hF (ε / 2) (by positivity)
  let d := min d₀ (min (1 / 2048) ((1 / 384 : ℝ) ^ η⁻¹))
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨fineConstant σ ω A, η, d, fineConstant_pos hA, hη, hd,
    (min_le_left _ _).trans hd₀small, ?_⟩
  intro δ a b m l hδ hδd hδa hab hb2 haSmall hm hl e n x v Y hn hnmax hv hball hT hover hYm hYT hYden hconv hslab
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hδsmall : δ ≤ 1 / 2048 := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hδroot : δ ≤ (1 / 384 : ℝ) ^ η⁻¹ :=
    hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδpow : δ ^ η ≤ 1 / 384 :=
    (Real.le_rpow_inv_iff_of_pos hδ.le (by norm_num) hη).mp hδroot
  have hdscale : δ ^ (2 : ℕ) ≤ d₀ :=
    (show δ ^ (2 : ℕ) ≤ δ by nlinarith).trans (hδd.trans (min_le_left _ _))
  have hinterior : δ ^ (2 : ℕ) ≤ δ / 8 := by nlinarith
  have hwidth : δ ^ (2 : ℕ) ≤ δ / (1024 * a) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hda : δ * (1024 * a) ≤ 1 := by
      have hh := mul_le_mul hδsmall haSmall ha.le (by norm_num : (0 : ℝ) ≤ 1 / 2048)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hda hδ.le]
  have hnmax' : (n : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) := by
    rw [← Real.rpow_natCast_mul hδ.le]
    exact hnmax.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num))
  let f := flatMap e a b ha hb
  let J := 1 / (128 * a * b)
  let U := fun i => f '' closedTube δ (x i) (v i)
  let Z := fun i => f '' Y i
  have hJ : 0 < J := by dsimp [J]; positivity
  have hvol : ∀ W, volume (f '' W) = ENNReal.ofReal J * volume W := flatMap_volume e ha hb
  have hgeom : BodyGeometry U (fun i => f (x i)) (δ ^ (2 : ℕ))
      (δ / (1024 * a)) (J * δ ^ 2) :=
    flat_body_geometry hδ hδa hab haSmall hb2 hinterior e x v hv hball hT
  have hconv' : BodyConvexCount U (J * δ ^ 2) m :=
    (closedTube_katz_tao x v hconv).affine_image (sq_nonneg δ) hJ f hvol
  have hpack : BodyPacking U (J * δ ^ 2) 1000 :=
    (closedTube_packing hδ x v hv hover).affine_image (sq_nonneg δ) hJ f hvol
  have hZd : ∀ i, ENNReal.ofReal ((δ ^ (2 : ℕ)) ^ η) * volume (U i) ≤ volume (Z i) := by
    intro i
    have hh : 384 * (δ ^ (2 : ℕ)) ^ η ≤ δ ^ η := by
      rw [← Real.rpow_natCast_mul hδ.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * η = η + η by ring, Real.rpow_add hδ]
      nlinarith [mul_le_mul_of_nonneg_left hδpow (Real.rpow_nonneg hδ.le η)]
    change ENNReal.ofReal _ * volume (f '' closedTube δ (x i) (v i)) ≤ volume (f '' Y i)
    rw [hvol, hvol]
    calc
      _ ≤ ENNReal.ofReal ((δ ^ (2 : ℕ)) ^ η) * (ENNReal.ofReal J * ENNReal.ofReal (384 * δ ^ 2)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (closedTube_volume_bounds hδ hδ1 (x i) (v i) (hv i)).2)
      _ ≤ ENNReal.ofReal J * ENNReal.ofReal (δ ^ η * δ ^ 2) := by
        simp only [← ENNReal.ofReal_mul hJ.le,
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ (δ ^ (2 : ℕ)) ^ η)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith only [mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ J * δ ^ 2)]
      _ ≤ _ := mul_le_mul' le_rfl (hYden i)
  have hbound := H (δ ^ (2 : ℕ)) (by positivity) hdscale n U Z (fun i => f (x i))
    (δ / (1024 * a)) (J * δ ^ 2) m l 1000 hn hnmax' hwidth (by positivity) hm hl
    (by norm_num) hgeom
    (fun i => f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm i))
    (fun i => image_mono ((hYT i).trans (tube_subset_closedTube _ _ _))) hZd hconv' hslab hpack
  have hZvol : volume (⋃ i, Z i) = ENNReal.ofReal J * volume (⋃ i, Y i) := by
    rw [← hvol, image_iUnion]
  rw [hZvol] at hbound
  have hscalar := fine_factorization (σ := σ) (ω := ω) (ε := ε) (n := (n : ℝ)) hA hδ ha hb
    (zero_lt_one.trans_le hm) (zero_lt_one.trans_le hl) (by exact_mod_cast hn)
  change A * (δ ^ (2 : ℕ)) ^ (ε / 2) * (δ / (1024 * a)) ^ ω *
    bodyWeight σ (J * δ ^ 2) m l 1000 n = _ at hscalar
  rw [hscalar, ENNReal.ofReal_mul hJ.le] at hbound
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hJ).ne' ENNReal.ofReal_ne_top).mp hbound

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
