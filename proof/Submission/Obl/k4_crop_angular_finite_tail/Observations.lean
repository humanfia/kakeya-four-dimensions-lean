/- Adapted from this LOT tree, obligation o091, session x0299, commit 918e44ebabf26b3b2fd56f3cccbf12b4ac1bac6e,
Submission/Obl/k4_dyadic_crop_typicality/Observations.lean. Transfer.lean in that branch was written by session x0302 (9db252b). -/

import Submission.Obl.k4_crop_angular_finite_tail.Grid

open MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace Submission.Obl.k4_crop_angular_finite_tail

open Submission.Obl.k4_profile_density_bounds (width base velocity hidden observe selected reference)

abbrev BaseObservation := Base × ℤ
abbrev VelocityBin := Fin 2 → ℤ

noncomputable def baseReference : Measure BaseObservation := volume.prod Measure.count

scoped instance baseReference_sigmaFinite : SigmaFinite baseReference := by
  unfold baseReference
  infer_instance

noncomputable def observeBase (N r : ℝ) (p : State) : BaseObservation :=
  (base p, ⌊Submission.Obl.k4_profile_density_bounds.hidden p / width N r⌋)

noncomputable def observeWidth (N r a : ℝ) (p : State) : Observation :=
  (observeBase N r p, fun j => ⌊velocity p.1 j / a⌋)

lemma observeWidth_eq (N r u : ℝ) : observeWidth N r (width N u) = observe N r u := rfl

lemma measurable_observeBase (N r : ℝ) : Measurable (observeBase N r) := by
  unfold observeBase
  exact Submission.Obl.k4_profile_density_bounds.measurable_base.prodMk
    (Int.measurable_floor.comp
      (Submission.Obl.k4_profile_density_bounds.measurable_hidden.div_const _))

lemma measurable_observeWidth (N r a : ℝ) : Measurable (observeWidth N r a) := by
  unfold observeWidth
  exact (measurable_observeBase N r).prodMk (by unfold velocity; fun_prop)

def coarsenObservation (d : ℕ) (z : Observation) : Observation :=
  (z.1, fun j => z.2 j / (2 : ℤ) ^ d)

lemma measurable_coarsenObservation (d : ℕ) : Measurable (coarsenObservation d) := by
  exact measurable_fst.prodMk ((measurable_of_countable (fun v : VelocityBin =>
    fun j => v j / (2 : ℤ) ^ d)).comp measurable_snd)

lemma observeWidth_product {N u v : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) (hv : 0 ≤ v)
    {d : ℕ} (hd : height N (u + v) = height N u + height N v + d)
    (r : ℝ) (p : State) :
    observeWidth N r (width N u * width N v) p =
      coarsenObservation d (observe N r (u + v) p) := by
  apply Prod.ext
  · rfl
  · funext j
    change ⌊velocity p.1 j / (width N u * width N v)⌋ =
      ⌊velocity p.1 j / width N (u + v)⌋ / (2 : ℤ) ^ d
    simp only [div_eq_mul_inv, mul_inv_rev, width_inv_height hN hu,
      width_inv_height hN hv, width_inv_height hN (add_nonneg hu hv)]
    rw [show velocity p.1 j * ((2 : ℝ) ^ height N v * (2 : ℝ) ^ height N u) =
        velocity p.1 j * (2 : ℝ) ^ (height N u + height N v) by rw [pow_add]; ring,
      Submission.Obl.k4_matching_homogeneous_records.floor_dyadic_refinement
        (show height N u + height N v ≤ height N (u + v) by omega),
      show height N (u + v) - (height N u + height N v) = d by omega]

def shiftBins (h : ℕ) (q : Fin 4 → ℤ) (v : VelocityBin) : VelocityBin :=
  fun j => v j - q (j.natAdd 2) * (2 : ℤ) ^ h

def shiftBinsEquiv (h : ℕ) (q : Fin 4 → ℤ) : VelocityBin ≃ᵐ VelocityBin where
  toFun := shiftBins h q
  invFun := fun v j => v j + q (j.natAdd 2) * (2 : ℤ) ^ h
  left_inv := by intro v; funext j; simp [shiftBins]
  right_inv := by intro v; funext j; simp [shiftBins]
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

def baseObservationCropEquiv {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ) :
    BaseObservation ≃ᵐ BaseObservation :=
  MeasurableEquiv.prodCongr (cropBaseEquiv ha q) (MeasurableEquiv.refl ℤ)

def observationCropEquiv {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ) (h : ℕ) :
    Observation ≃ᵐ Observation :=
  MeasurableEquiv.prodCongr (baseObservationCropEquiv ha q) (shiftBinsEquiv h q)

lemma observeBase_crop {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ)
    (N r : ℝ) (p : State) :
    observeBase N r (cropState a q p) = baseObservationCropEquiv ha q (observeBase N r p) := by
  apply Prod.ext
  · exact base_cropState a q p
  · simp only [observeBase, hidden_cropState]
    rfl

lemma observe_crop {N u v : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) (hv : 0 ≤ v)
    {d : ℕ} (hd : height N (u + v) = height N u + height N v + d)
    (q : Fin 4 → ℤ) (r : ℝ) (p : State) :
    observe N r v (cropState (width N u) q p) =
      observationCropEquiv (ne_of_gt (Submission.Obl.k4_profile_density_bounds.width_pos N u)) q
        (height N v) (coarsenObservation d (observe N r (u + v) p)) := by
  apply Prod.ext
  · exact observeBase_crop (ne_of_gt (Submission.Obl.k4_profile_density_bounds.width_pos N u)) q N r p
  · funext j
    change ⌊velocity (cropLine (width N u) q p.1) j / width N v⌋ =
      ⌊velocity p.1 j / width N (u + v)⌋ / (2 : ℤ)^d -
        q (j.natAdd 2) * (2 : ℤ)^height N v
    rw [velocity_cropLine]
    exact angular_floor hN hu hv hd (velocity p.1 j) (q (j.natAdd 2))

lemma floor_width_product {N u v : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (x : ℝ) :
    ⌊x / width N u⌋ = ⌊x / (width N u * width N v)⌋ / (2 : ℤ)^height N v := by
  simp only [div_eq_mul_inv, mul_inv_rev, width_inv_height hN hu, width_inv_height hN hv]
  rw [show x * ((2 : ℝ)^height N v * (2 : ℝ)^height N u) =
      x * (2 : ℝ)^(height N u + height N v) by rw [pow_add]; ring]
  simpa only [Nat.add_sub_cancel_left] using
    Submission.Obl.k4_matching_homogeneous_records.floor_dyadic_refinement
      (show height N u ≤ height N u + height N v by omega) x

def compatibleCrop (a : ℝ) (h : ℕ) (q : Fin 4 → ℤ) : Set Observation :=
  {z | q ∈ cropCandidates a z.1.1 (fun j => z.2 j / (2 : ℤ)^h)}

lemma measurableSet_compatibleCrop (a : ℝ) (h : ℕ) (q : Fin 4 → ℤ) :
    MeasurableSet (compatibleCrop a h q) := by
  classical
  simp only [compatibleCrop, cropCandidates, Finset.mem_image, Finset.mem_univ, true_and]
  rw [show {z : Observation | ∃ e : Fin 2 → Fin 2,
      cropCandidate a z.1.1 (fun j => z.2 j / (2 : ℤ)^h) e = q} =
      ⋃ e : Fin 2 → Fin 2, {z : Observation |
        cropCandidate a z.1.1 (fun j => z.2 j / (2 : ℤ)^h) e = q} by ext z; simp]
  apply MeasurableSet.iUnion
  intro e
  apply measurableSet_eq_fun _ measurable_const
  unfold cropCandidate
  fun_prop

lemma cropBox_observeWidth_compatible {N u v : ℝ} (hN : 1 ≤ N)
    (hu : 0 ≤ u) (hv : 0 ≤ v) {q : Fin 4 → ℤ} {p : State}
    (hp : p.1 ∈ cropBox (width N u) q) (ht : p.2 ∈ Icc (0 : ℝ) 1) (r : ℝ) :
    observeWidth N r (width N u * width N v) p ∈
      compatibleCrop (width N u) (height N v) q := by
  change q ∈ cropCandidates (width N u) (base p)
    (fun j => ⌊velocity p.1 j / (width N u * width N v)⌋ / (2 : ℤ)^height N v)
  simp_rw [← floor_width_product hN hu hv]
  exact cropBox_mem_candidates (Submission.Obl.k4_profile_density_bounds.width_pos N u) hp ht

lemma card_compatibleCrop_indices {n : ℕ} (q : Fin n → Fin 4 → ℤ)
    (hq : Function.Injective q) (a : ℝ) (h : ℕ) (z : Observation)
    [DecidablePred (fun i => z ∈ compatibleCrop a h (q i))] :
    (Finset.univ.filter (fun i => z ∈ compatibleCrop a h (q i))).card ≤ 4 := by
  simpa only [compatibleCrop, Set.mem_setOf_eq] using
    card_cropCandidate_indices q hq a z.1.1 (fun j => z.2 j / (2 : ℤ)^h)

end Submission.Obl.k4_crop_angular_finite_tail
