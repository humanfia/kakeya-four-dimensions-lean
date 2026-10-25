/- Adapted within this LOT tree from o006/x0006, Submission/Obl/k4_core/FiniteSmoothing/UniformBoxes.lean.
Original o018/x0048 attribution is retained below. -/

/- Adapted from the same LOT tree, obligation o018, session x0048, commit 6d775765b92912e6ea3c223ec01500dda1f728e5,
Submission/Obl/k4_framework_from_matching_clustering_conic/UniformBoxes.lean. Namespace and own-submodule import paths changed; proof content retained. -/

import Mathlib

/-!
The elementary probability calculation in the smoothing paragraph of
Theorem 2.17.  Coordinate boxes are used before transport to Euclidean space.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing

/-- A coordinate box of radius `r` in every coordinate. -/
def coordBox {d : ℕ} (r : ℝ) (c : Fin d → ℝ) : Set (Fin d → ℝ) :=
  Icc (fun j => c j - r) (fun j => c j + r)

theorem measurableSet_coordBox {d : ℕ} (r : ℝ) (c : Fin d → ℝ) :
    MeasurableSet (coordBox r c) := measurableSet_Icc

theorem mem_coordBox_iff {d : ℕ} {r : ℝ} {c x : Fin d → ℝ} :
    x ∈ coordBox r c ↔ ∀ j, |x j - c j| ≤ r := by
  constructor
  · rintro ⟨hlo, hhi⟩ j
    exact abs_le.mpr ⟨by linarith [hlo j], by linarith [hhi j]⟩
  · intro h
    exact ⟨fun j => by linarith [(abs_le.mp (h j)).1],
      fun j => by linarith [(abs_le.mp (h j)).2]⟩

theorem volume_coordBox {d : ℕ} (r : ℝ) (c : Fin d → ℝ) :
    volume (coordBox r c) = ENNReal.ofReal (2 * r) ^ d := by
  rw [coordBox, Real.volume_Icc_pi]
  simp only [add_sub_sub_cancel, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  congr 1
  ring

/-- Normalized Lebesgue measure on a coordinate box. -/
noncomputable def boxLaw {d : ℕ} (r : ℝ) (c : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  ProbabilityTheory.cond volume (coordBox r c)

local instance boxLaw_isFiniteMeasure {d : ℕ} (r : ℝ) (c : Fin d → ℝ) :
    IsFiniteMeasure (boxLaw r c) :=
  inferInstanceAs (IsFiniteMeasure (ProbabilityTheory.cond volume (coordBox r c)))

theorem boxLaw_isProbabilityMeasure {d : ℕ} {r : ℝ} (hr : 0 < r) (c : Fin d → ℝ) :
    IsProbabilityMeasure (boxLaw r c) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [volume_coordBox]
    exact pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  · rw [volume_coordBox]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

theorem boxLaw_eq {d : ℕ} (r : ℝ) (c : Fin d → ℝ) :
    boxLaw r c = (ENNReal.ofReal (2 * r) ^ d)⁻¹ • volume.restrict (coordBox r c) := by
  rw [boxLaw, ProbabilityTheory.cond, volume_coordBox]

theorem boxLaw_self {d : ℕ} {r : ℝ} (hr : 0 < r) (c : Fin d → ℝ) :
    boxLaw r c (coordBox r c) = 1 := by
  rw [boxLaw, ProbabilityTheory.cond_apply (measurableSet_coordBox r c)]
  simp only [inter_self, volume_coordBox]
  exact ENNReal.inv_mul_cancel
    (pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)))
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- Disjoint smoothing boxes have no multiplicity loss in their common density bound. -/
theorem sum_boxLaw_le {d n : ℕ} (r : ℝ) (c : Fin n → Fin d → ℝ)
    (hc : Pairwise (fun i j => Disjoint (coordBox r (c i)) (coordBox r (c j)))) :
    (∑ i, boxLaw r (c i)) ≤ (ENNReal.ofReal (2 * r) ^ d)⁻¹ • volume := by
  simp_rw [boxLaw_eq]
  rw [← Finset.smul_sum, ← Measure.sum_fintype,
    ← Measure.restrict_iUnion hc (fun i => measurableSet_coordBox r (c i))]
  gcongr
  exact Measure.restrict_le_self

/-- A uniform mixture of independently smoothed intercepts and slopes. -/
noncomputable def smoothedPrior {d n : ℕ} (r : ℝ)
    (b s : Fin n → Fin d → ℝ) : Measure ((Fin d → ℝ) × (Fin d → ℝ)) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, (boxLaw r (b i)).prod (boxLaw r (s i))

theorem smoothedPrior_isProbabilityMeasure {d n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (b s : Fin n → Fin d → ℝ) :
    IsProbabilityMeasure (smoothedPrior r b s) := by
  let : ∀ i, IsProbabilityMeasure (boxLaw r (b i)) := fun i =>
    boxLaw_isProbabilityMeasure hr (b i)
  let : ∀ i, IsProbabilityMeasure (boxLaw r (s i)) := fun i =>
    boxLaw_isProbabilityMeasure hr (s i)
  constructor
  simp only [smoothedPrior, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by simpa using hn.ne') (by simp)

/-- The full slope marginal has density at most the inverse total box volume. -/
theorem smoothedPrior_slope_le {d n : ℕ} {r : ℝ} (hr : 0 < r)
    (b s : Fin n → Fin d → ℝ)
    (hs : Pairwise (fun i j => Disjoint (coordBox r (s i)) (coordBox r (s j))))
    (A : Set (Fin d → ℝ)) :
    smoothedPrior r b s (univ ×ˢ A) ≤
      (n : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (2 * r) ^ d)⁻¹ * volume A := by
  let : ∀ i, IsProbabilityMeasure (boxLaw r (b i)) := fun i =>
    boxLaw_isProbabilityMeasure hr (b i)
  simp only [smoothedPrior, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    Measure.prod_prod, measure_univ, one_mul]
  rw [mul_assoc]
  gcongr
  simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using
    sum_boxLaw_le r s hs A

/-- Any set containing all coefficient boxes supports the entire mixture. -/
theorem smoothedPrior_support {d n : ℕ} {r : ℝ} (hr : 0 < r)
    (b s : Fin n → Fin d → ℝ) (P : Set ((Fin d → ℝ) × (Fin d → ℝ)))
    (hP : ∀ i, coordBox r (b i) ×ˢ coordBox r (s i) ⊆ P) :
    smoothedPrior r b s Pᶜ = 0 := by
  let : ∀ i, IsProbabilityMeasure (boxLaw r (b i)) := fun i =>
    boxLaw_isProbabilityMeasure hr (b i)
  let : ∀ i, IsProbabilityMeasure (boxLaw r (s i)) := fun i =>
    boxLaw_isProbabilityMeasure hr (s i)
  have hcomp (i : Fin n) : (boxLaw r (b i)).prod (boxLaw r (s i)) Pᶜ = 0 := by
    apply measure_mono_null (Set.compl_subset_compl.mpr (hP i))
    rw [measure_compl ((measurableSet_coordBox r (b i)).prod
      (measurableSet_coordBox r (s i))) (measure_ne_top _ _), measure_univ,
      Measure.prod_prod, boxLaw_self hr, boxLaw_self hr, one_mul, tsub_self]
  simp only [smoothedPrior, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    hcomp, Finset.sum_const_zero, mul_zero]

/-- If every perturbation preserves each old successful time set, smoothing preserves its
common time-mass lower bound.  Neither the event nor the successful time sets are normalized. -/
theorem smoothedPrior_time_mass {d n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (b s : Fin n → Fin d → ℝ)
    (T : Fin n → Set ℝ) (m : ℝ≥0∞)
    (hT : ∀ i, m ≤ volume (T i))
    (E : Set (((Fin d → ℝ) × (Fin d → ℝ)) × ℝ))
    (hE : ∀ i, (coordBox r (b i) ×ˢ coordBox r (s i)) ×ˢ T i ⊆ E) :
    m ≤ (smoothedPrior r b s).prod volume E := by
  have hcomp (i : Fin n) :
      m ≤ ((boxLaw r (b i)).prod (boxLaw r (s i))).prod volume E := by
    calc
      m ≤ volume (T i) := hT i
      _ = ((boxLaw r (b i)).prod (boxLaw r (s i))).prod volume
          ((coordBox r (b i) ×ˢ coordBox r (s i)) ×ˢ T i) := by
        rw [Measure.prod_prod, Measure.prod_prod, boxLaw_self hr, boxLaw_self hr,
          one_mul, one_mul]
      _ ≤ _ := measure_mono (hE i)
  rw [smoothedPrior, Measure.prod_smul_left, ← Measure.sum_fintype,
    Measure.prod_sum_left, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply_of_countable, tsum_fintype]
  calc
    m = (n : ℝ≥0∞)⁻¹ * ∑ _ : Fin n, m := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by simpa using hn.ne') (by simp), one_mul]
    _ ≤ _ := by
      gcongr with i
      exact hcomp i

end Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing
