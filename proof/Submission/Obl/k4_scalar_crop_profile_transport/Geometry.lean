import Submission.Obl.k4_scalar_crop_profile_transport.Types
import Submission.Obl.k4_crop_base_finite_tail.Geometry

noncomputable section

namespace Submission.Obl.k4_scalar_crop_profile_transport

open MeasureTheory Set
open scoped ENNReal

/-- The velocity bin and a point on the line leave at most two intercept bins. -/
def cropCandidate (a : ℝ) (b : Fin 2 → ℝ) (v : ℤ) (e : Fin 2) : Fin 2 → ℤ :=
  ![⌊b 1 / a - b 0 * (v : ℝ)⌋ - e.val, v]

def cropCandidates (a : ℝ) (b : Fin 2 → ℝ) (v : ℤ) : Finset (Fin 2 → ℤ) :=
  Finset.univ.image (cropCandidate a b v)

lemma card_cropCandidates (a : ℝ) (b : Fin 2 → ℝ) (v : ℤ) :
    (cropCandidates a b v).card ≤ 2 :=
  Finset.card_image_le.trans (by decide)

lemma cell_mem_candidates {a : ℝ} (ha : 0 < a) {z : Fin 2 → ℤ}
    {p : Inc} (hp : p.1 ∈ Cell a z) (ht : p.2 ∈ Icc (0 : ℝ) 1) :
    z ∈ cropCandidates a ![p.2, y p.1 p.2] ⌊p.1.2 1 / a⌋ := by
  classical
  have hb := k4_crop_base_finite_tail.Geometry.intercept_floor_bounds ha ht
    (p.1.2 0) (p.1.2 1)
  let c : ℤ := ⌊y p.1 p.2 / a - p.2 * (⌊p.1.2 1 / a⌋ : ℝ)⌋
  have h : 0 ≤ c - z 0 ∧ c - z 0 < 2 := by
    dsimp [c, y]
    rw [hp.1] at hb
    omega
  let e : Fin 2 := ⟨(c - z 0).toNat, by omega⟩
  apply Finset.mem_image.mpr
  refine ⟨e, Finset.mem_univ _, ?_⟩
  ext i
  fin_cases i
  · simp [cropCandidate, e, c]
    omega
  · simpa [cropCandidate] using hp.2

def compatibleCrop (a : ℝ) (z : Fin 2 → ℤ) : Set Joint :=
  {b | z ∈ cropCandidates a b.1.1 b.2}

lemma measurableSet_compatibleCrop (a : ℝ) (z : Fin 2 → ℤ) :
    MeasurableSet (compatibleCrop a z) := by
  classical
  simp only [compatibleCrop, cropCandidates, Finset.mem_image, Finset.mem_univ, true_and]
  rw [show {b : Joint | ∃ e : Fin 2, cropCandidate a b.1.1 b.2 e = z} =
    ⋃ e : Fin 2, {b : Joint | cropCandidate a b.1.1 b.2 e = z} by ext b; simp]
  apply MeasurableSet.iUnion
  intro e
  apply measurableSet_eq_fun _ measurable_const
  unfold cropCandidate
  fun_prop

lemma cell_Aug_compatible {N u : ℝ} (hN : 0 < N) (r : ℝ) {z : Fin 2 → ℤ} {p : Inc}
    (hp : p.1 ∈ Cell (N ^ (-u)) z) (ht : p.2 ∈ Icc (0 : ℝ) 1) :
    Aug N r u p ∈ compatibleCrop (N ^ (-u)) z :=
  cell_mem_candidates (Real.rpow_pos_of_pos hN _) hp ht

lemma compatibleCrop_overlap {w : ℕ} (z : Fin w → Fin 2 → ℤ)
    (hz : Function.Injective z) (a : ℝ) (b : Joint) :
    (∑ γ, (compatibleCrop a (z γ)).indicator (fun _ => (1 : ENNReal)) b) ≤ 2 := by
  classical
  let s := Finset.univ.filter (fun γ => z γ ∈ cropCandidates a b.1.1 b.2)
  have hc : s.card ≤ 2 := by
    calc
      s.card = (s.image z).card := (Finset.card_image_of_injective s hz).symm
      _ ≤ (cropCandidates a b.1.1 b.2).card := by
        apply Finset.card_le_card
        intro q hq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
        exact (Finset.mem_filter.mp hi).2
      _ ≤ 2 := card_cropCandidates a b.1.1 b.2
  have heq : (∑ γ, (compatibleCrop a (z γ)).indicator (fun _ => (1 : ENNReal)) b) =
      (s.card : ENNReal) := by
    simp only [Set.indicator_apply, compatibleCrop, mem_ofPred_eq]
    rw [← Finset.sum_filter]
    simp [s]
  rw [heq]
  exact_mod_cast hc

lemma selected_mass_le_one (ν : Measure Line) [IsProbabilityMeasure ν] (E : Set Inc)
    (htime : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) : Selected ν E univ ≤ 1 := by
  calc
    Selected ν E univ = (ν.prod volume) E := Measure.restrict_apply_univ E
    _ ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono htime
    _ = 1 := by rw [Measure.prod_prod]; simp

lemma selected_finite (ν : Measure Line) [IsProbabilityMeasure ν] (E : Set Inc)
    (htime : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) : IsFiniteMeasure (Selected ν E) :=
  k4_dyadic_crop_affine_laws.Framework.finite_selected_incidence ν E htime

end Submission.Obl.k4_scalar_crop_profile_transport
