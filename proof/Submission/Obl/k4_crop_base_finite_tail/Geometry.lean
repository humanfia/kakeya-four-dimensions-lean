/- Adapted from this LOT tree, o091, session x0299, commit 918e44e,
Submission/Obl/k4_dyadic_crop_typicality/Grid.lean and Observations.lean. -/
import Submission.Obl.k4_dyadic_crop_affine_laws.CropDensities

namespace Submission.Obl.k4_crop_base_finite_tail.Geometry

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_dyadic_crop_affine_laws
noncomputable section

/-- Knowing the position and the velocity bin leaves two possible intercept
bins in one coordinate. -/
lemma intercept_floor_bounds {a t : ℝ} (_ha : 0 < a)
    (ht : t ∈ Icc (0 : ℝ) 1) (b v : ℝ) :
    ⌊(b + t * v) / a - t * (⌊v / a⌋ : ℝ)⌋ - 1 ≤ ⌊b / a⌋ ∧
      ⌊b / a⌋ ≤ ⌊(b + t * v) / a - t * (⌊v / a⌋ : ℝ)⌋ := by
  have hθ0 : 0 ≤ v / a - (⌊v / a⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le _)
  have hθ1 : v / a - (⌊v / a⌋ : ℝ) < 1 := by
    linarith [Int.lt_floor_add_one (v / a)]
  have hmul0 := mul_nonneg ht.1 hθ0
  have hmul1 : t * (v / a - (⌊v / a⌋ : ℝ)) < 1 :=
    (mul_le_mul_of_nonneg_right ht.2 hθ0).trans_lt (by simpa using hθ1)
  have he : (b + t * v) / a - t * (⌊v / a⌋ : ℝ) =
      b / a + t * (v / a - (⌊v / a⌋ : ℝ)) := by ring
  rw [he]
  constructor
  · have hb : b / a + t * (v / a - (⌊v / a⌋ : ℝ)) < (⌊b / a⌋ : ℝ) + 2 := by
      linarith [Int.lt_floor_add_one (b / a)]
    have hh : ⌊b / a + t * (v / a - (⌊v / a⌋ : ℝ))⌋ < ⌊b / a⌋ + 2 := by
      rw [Int.floor_lt]
      push_cast
      exact hb
    omega
  · exact Int.floor_mono (by linarith)

def cropCandidate (a : ℝ) (z : EuclideanSpace ℝ (Fin 3)) (v : Fin 2 → ℤ)
    (e : Fin 2 → Fin 2) : Fin 4 → ℤ :=
  ![⌊z 1 / a - z 0 * v 0⌋ - (e 0).val,
    ⌊z 2 / a - z 0 * v 1⌋ - (e 1).val, v 0, v 1]

def cropCandidates (a : ℝ) (z : EuclideanSpace ℝ (Fin 3)) (v : Fin 2 → ℤ) : Finset (Fin 4 → ℤ) :=
  Finset.univ.image (cropCandidate a z v)

lemma card_cropCandidates (a : ℝ) (z : EuclideanSpace ℝ (Fin 3)) (v : Fin 2 → ℤ) :
    (cropCandidates a z v).card ≤ 4 := by
  exact (Finset.card_image_le).trans (by decide)

lemma cell_mem_candidates {a : ℝ} (ha : 0 < a) {q : Fin 4 → ℤ}
    {p : Inc} (hp : p.1 ∈ Cell a q) (ht : p.2 ∈ Icc (0 : ℝ) 1) :
    q ∈ cropCandidates a (Framework.baseObservation p) (fun j => ⌊Framework.planarVelocity p.1 j / a⌋) := by
  classical
  have hb0 := intercept_floor_bounds ha ht (p.1.2 0) (p.1.2 3)
  have hb1 := intercept_floor_bounds ha ht (p.1.2 1) (p.1.2 4)
  let c0 : ℤ := ⌊(p.1.2 0 + p.2 * p.1.2 3) / a - p.2 * (⌊p.1.2 3 / a⌋ : ℝ)⌋
  let c1 : ℤ := ⌊(p.1.2 1 + p.2 * p.1.2 4) / a - p.2 * (⌊p.1.2 4 / a⌋ : ℝ)⌋
  have h0 : 0 ≤ c0 - q 0 ∧ c0 - q 0 < 2 := by dsimp [c0]; rw [hp.1] at hb0; omega
  have h1 : 0 ≤ c1 - q 1 ∧ c1 - q 1 < 2 := by dsimp [c1]; rw [hp.2.1] at hb1; omega
  let e : Fin 2 → Fin 2 :=
    ![⟨(c0 - q 0).toNat, by omega⟩, ⟨(c1 - q 1).toNat, by omega⟩]
  apply Finset.mem_image.mpr
  refine ⟨e, Finset.mem_univ _, ?_⟩
  funext j
  fin_cases j
  · simp [cropCandidate, Framework.baseObservation, Framework.trajectoryPoint, e, c0, Framework.planarVelocity]
    omega
  · simp [cropCandidate, Framework.baseObservation, Framework.trajectoryPoint, e, c1, Framework.planarVelocity]
    omega
  · simpa [cropCandidate, Framework.planarVelocity] using hp.2.2.1
  · simpa [cropCandidate, Framework.planarVelocity] using hp.2.2.2

lemma card_cropCandidate_indices {n : ℕ} (q : Fin n → Fin 4 → ℤ)
    (hq : Function.Injective q) (a : ℝ) (z : EuclideanSpace ℝ (Fin 3)) (v : Fin 2 → ℤ) :
    (Finset.univ.filter (fun i => q i ∈ cropCandidates a z v)).card ≤ 4 := by
  classical
  let s := Finset.univ.filter (fun i => q i ∈ cropCandidates a z v)
  calc
    s.card = (s.image q).card := (Finset.card_image_of_injective s hq).symm
    _ ≤ (cropCandidates a z v).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    _ ≤ 4 := card_cropCandidates a z v


lemma cell_disjoint (a : ℝ) {q q' : Fin 4 → ℤ} (h : q ≠ q') :
    Disjoint (Cell a q) (Cell a q') := by
  rw [Set.disjoint_left]
  intro l hl hl'
  apply h
  funext j
  fin_cases j
  · exact hl.1.symm.trans hl'.1
  · exact hl.2.1.symm.trans hl'.2.1
  · exact hl.2.2.1.symm.trans hl'.2.2.1
  · exact hl.2.2.2.symm.trans hl'.2.2.2

def compatibleCrop (a : ℝ) (q : Fin 4 → ℤ) : Set Joint :=
  {z | q ∈ cropCandidates a z.1.1 z.2}

lemma measurableSet_compatibleCrop (a : ℝ) (q : Fin 4 → ℤ) :
    MeasurableSet (compatibleCrop a q) := by
  classical
  simp only [compatibleCrop, cropCandidates, Finset.mem_image, Finset.mem_univ, true_and]
  rw [show {z : Joint | ∃ e : Fin 2 → Fin 2,
      cropCandidate a z.1.1 z.2 e = q} =
      ⋃ e : Fin 2 → Fin 2, {z : Joint |
        cropCandidate a z.1.1 z.2 e = q} by ext z; simp]
  apply MeasurableSet.iUnion
  intro e
  apply measurableSet_eq_fun _ measurable_const
  unfold cropCandidate
  fun_prop

lemma cell_jointObs_compatible {a : ℝ} (ha : 0 < a) (N : ℕ → ℝ)
    (k : ℕ) (r u : ℝ) (haeq : a = Scale N k u) {q : Fin 4 → ℤ} {x : Inc}
    (hx : x.1 ∈ Cell a q) (ht : x.2 ∈ Icc (0 : ℝ) 1) :
    JointObs N k r u x ∈ compatibleCrop a q := by
  change q ∈ cropCandidates a (Framework.baseObservation x)
    (fun j => ⌊Framework.planarVelocity x.1 j / Scale N k u⌋)
  rw [← haeq]
  exact cell_mem_candidates ha hx ht

lemma compatibleCrop_overlap {w : ℕ} (q : Fin w → Fin 4 → ℤ)
    (hq : Function.Injective q) (a : ℝ) (z : Joint) :
    (∑ γ, (compatibleCrop a (q γ)).indicator (fun _ => (1 : ENNReal)) z) ≤ 4 := by
  classical
  have hc := card_cropCandidate_indices q hq a z.1.1 z.2
  have heq : (∑ γ, (compatibleCrop a (q γ)).indicator (fun _ => (1 : ENNReal)) z) =
      ((Finset.univ.filter (fun γ => q γ ∈ cropCandidates a z.1.1 z.2)).card : ENNReal) := by
    simp only [Set.indicator_apply, compatibleCrop, mem_ofPred_eq]
    rw [← Finset.sum_filter]
    simp
  rw [heq]
  exact_mod_cast hc

end
end Submission.Obl.k4_crop_base_finite_tail.Geometry
