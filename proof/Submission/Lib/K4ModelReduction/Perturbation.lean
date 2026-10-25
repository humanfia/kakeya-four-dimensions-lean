import Mathlib

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-!
Preservation of marked times under the coefficient smoothing in the supplied
paper's Theorem 2.17. A fixed enlargement of the covering balls suffices.
-/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Small independent perturbations of intercept and slope stay small on the
whole common graph-time interval. -/
theorem affine_perturbation_dist_le {x x' v v' : V} {δ t : ℝ}
    (hx : dist x' x ≤ δ / 4) (hv : dist v' v ≤ δ / 4)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (x' + t • v') (x + t • v) ≤ δ / 2 := by
  calc
    dist (x' + t • v') (x + t • v) ≤ dist x' x + dist (t • v') (t • v) :=
      dist_add_add_le _ _ _ _
    _ = dist x' x + |t| * dist v' v := by rw [dist_smul₀, Real.norm_eq_abs]
    _ ≤ δ / 2 := by
      rw [abs_of_nonneg ht.1]
      nlinarith [show 0 ≤ dist v' v from dist_nonneg, ht.2]

/-- A point lying in an original covering ball remains in its fixed double-scale
enlargement after either coefficient perturbation. -/
theorem affine_perturbation_mem_ball {x x' v v' z : V} {δ ρ t : ℝ}
    (hδ : 0 < δ) (hx : dist x' x ≤ δ / 4) (hv : dist v' v ≤ δ / 4)
    (ht : t ∈ Icc (0 : ℝ) 1) (hρ : ρ ≤ δ)
    (hmem : x + t • v ∈ ball z ρ) :
    x' + t • v' ∈ ball z (2 * δ) := by
  have hnear := affine_perturbation_dist_le hx hv ht
  have htri := dist_triangle (x' + t • v') (x + t • v) z
  rw [mem_ball] at hmem ⊢
  linarith

/-- Smoothing preserves each original trajectory's selected time mass, when
the union of covering balls is enlarged by an absolute factor. -/
theorem covered_time_measure_le_of_perturbation
    {ι : Type*} (z : ι → V) (ρ : ι → ℝ) {x x' v v' : V} {δ : ℝ}
    (hδ : 0 < δ) (hx : dist x' x ≤ δ / 4) (hv : dist v' v ≤ δ / 4)
    (hρ : ∀ i, ρ i ≤ δ) :
    volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ x + t • v ∈ ⋃ i, ball (z i) (ρ i)} ≤
      volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ x' + t • v' ∈ ⋃ i, ball (z i) (2 * δ)} := by
  apply measure_mono
  rintro t ⟨ht, hm⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 hm
  exact ⟨ht, mem_iUnion.2 ⟨i, affine_perturbation_mem_ball hδ hx hv ht (hρ i) hi⟩⟩

variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Every prior supported on the small coefficient perturbations has at least
the original selected time mass. The prior is normalized independently of
the selected incidences. -/
theorem smoothed_selected_mass_lower_bound
    {ι : Type*} (z : ι → V) (ρ : ι → ℝ) {x v : V} {δ : ℝ}
    (hδ : 0 < δ) (hρ : ∀ i, ρ i ≤ δ)
    (μ : Measure (V × V)) [IsProbabilityMeasure μ] (c : ℝ≥0∞)
    (hnear : ∀ᵐ l ∂μ, dist l.1 x ≤ δ / 4 ∧ dist l.2 v ≤ δ / 4)
    (hmass : c ≤ volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      x + t • v ∈ ⋃ i, ball (z i) (ρ i)}) :
    c ≤ μ.prod volume {p : (V × V) × ℝ | p.2 ∈ Icc (0 : ℝ) 1 ∧
      p.1.1 + p.2 • p.1.2 ∈ ⋃ i, ball (z i) (2 * δ)} := by
  have hU : IsOpen (⋃ i, ball (z i) (2 * δ)) := isOpen_iUnion fun _ => isOpen_ball
  have hmap : Continuous (fun p : (V × V) × ℝ => p.1.1 + p.2 • p.1.2) := by
    fun_prop
  have hE : MeasurableSet {p : (V × V) × ℝ | p.2 ∈ Icc (0 : ℝ) 1 ∧
      p.1.1 + p.2 • p.1.2 ∈ ⋃ i, ball (z i) (2 * δ)} :=
    (measurableSet_Icc.preimage measurable_snd).inter
      (hU.measurableSet.preimage hmap.measurable)
  rw [Measure.prod_apply hE]
  calc
    c = ∫⁻ _l, c ∂μ := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [hnear] with l hl
      exact hmass.trans (covered_time_measure_le_of_perturbation z ρ hδ hl.1 hl.2 hρ)

end Submission.Lib.K4ModelReduction
