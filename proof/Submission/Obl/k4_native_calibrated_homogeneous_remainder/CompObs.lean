/- Adapted from this LOT tree, obligation o119, session x0404, commit b1aa67e,
   Submission/Obl/k4_finite_width_critical_contradiction/CompObs.lean. -/
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CompWorlds

/-!
# Observations of encoded incidences

`jobs B a v p` is the joint observation of the frozen statement: time, base point, the
hidden bin `⌊B w / a⌋` and the velocity bins of width `v`.  An encoded incidence of world
`c` observed with `B = 1` at thickness `σ a'` is the world-`c` observation at thickness `a'`
with its hidden bin shifted by an integer.
-/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp

attribute [local simp] encCoeff_zero encCoeff_one encCoeff_two encCoeff_three encCoeff_four encCoeff_five

open MeasureTheory Set

abbrev JObs := (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)

/-- The joint observation with hidden scale `B`, hidden thickness `a`, velocity width `v`. -/
noncomputable def jobs (B a v : ℝ) (p : Inc) : JObs :=
  ((WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4],
      ⌊B * (p.1.2 2 + p.2 * p.1.2 5) / a⌋),
    fun j => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4] : EuclideanSpace ℝ (Fin 2)) j / v⌋)

/-- Shift of the hidden bin. -/
def shiftObs (z : ℤ) (q : JObs) : JObs := ((q.1.1, q.1.2 + z), q.2)

theorem shiftObs_shiftObs (z z' : ℤ) (q : JObs) :
    shiftObs z (shiftObs z' q) = shiftObs (z' + z) q := by
  simp [shiftObs, add_assoc]

theorem shiftObs_zero (q : JObs) : shiftObs 0 q = q := by simp [shiftObs]

theorem measurable_shiftObs (z : ℤ) : Measurable (shiftObs z) := by
  unfold shiftObs
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) measurable_snd
  · exact measurable_fst.comp measurable_fst
  · exact (measurable_of_countable (fun n : ℤ => n + z)).comp (measurable_snd.comp measurable_fst)

/-- The shift as a measurable equivalence. -/
def shiftEquiv (z : ℤ) : JObs ≃ᵐ JObs where
  toFun := shiftObs z
  invFun := shiftObs (-z)
  left_inv q := by simp [shiftObs]
  right_inv q := by simp [shiftObs]
  measurable_toFun := measurable_shiftObs z
  measurable_invFun := measurable_shiftObs (-z)

/-- The reference measure of joint observations. -/
noncomputable abbrev jref : Measure JObs :=
  ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).prod Measure.count

theorem map_shiftObs_jref (z : ℤ) : Measure.map (shiftObs z) jref = jref := by
  have hcount : Measure.map (fun n : ℤ => n + z) (Measure.count : Measure ℤ) = Measure.count := by
    ext s hs
    rw [Measure.map_apply (measurable_of_countable _) hs, Measure.count_apply hs,
      Measure.count_apply (MeasurableSet.of_discrete)]
    have : (fun n : ℤ => n + z) ⁻¹' s = (fun n => n - z) '' s := by
      ext n
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro h; exact ⟨n + z, h, by ring⟩
      · rintro ⟨m, hm, rfl⟩; simpa using hm
    rw [this, (sub_left_injective (b := z)).encard_image]
  have h1 : Measure.map (fun q : EuclideanSpace ℝ (Fin 3) × ℤ => (q.1, q.2 + z))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count) =
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count := by
    have := Measure.map_prod_map (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (Measure.count : Measure ℤ) measurable_id
      (measurable_of_countable (fun n : ℤ => n + z))
    rw [Measure.map_id, hcount] at this
    exact this.symm
  have h2 := Measure.map_prod_map ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
      (Measure.count : Measure ℤ)) (Measure.count : Measure (Fin 2 → ℤ))
      (f := fun q : EuclideanSpace ℝ (Fin 3) × ℤ => (q.1, q.2 + z)) (g := id)
      (measurable_fst.prodMk ((measurable_of_countable (fun n : ℤ => n + z)).comp measurable_snd))
      measurable_id
  rw [h1, Measure.map_id] at h2
  exact h2.symm

/-- The hidden bin of an encoded incidence. -/
theorem floor_enc_hidden {B σ a' w z : ℝ} (hσ : 0 < σ) (ha' : 0 < a') (Z : ℤ)
    (hz : z = (Z : ℝ) * (σ * a')) :
    ⌊(B * σ * w + z) / (σ * a')⌋ = ⌊B * w / a'⌋ + Z := by
  have hne : σ * a' ≠ 0 := by positivity
  have : (B * σ * w + z) / (σ * a') = B * w / a' + Z := by
    rw [hz]; field_simp
  rw [this, Int.floor_add_intCast]

/-- The joint observation of an encoded incidence of world `c`, observed with `B = 1` at
thickness `σ * a'`, is the world observation at thickness `a'`, shifted by `Z`. -/
theorem jobs_encInc (W c : ℕ) {B σ a' v : ℝ} (hσ : 0 < σ) (ha' : 0 < a') (Z : ℤ) (o : ℝ)
    (ho : o = (Z : ℝ) * (σ * a')) (p : Inc) :
    jobs 1 (σ * a') v (encInc W c (B * σ) o p) = shiftObs Z (jobs B a' v p) := by
  have hhid := floor_enc_hidden (B := B) (w := p.1.2 2 + p.2 * p.1.2 5) hσ ha' Z ho
  simp only [jobs, encInc, encTraj, shiftObs, encCoeff_zero, encCoeff_one, encCoeff_three,
    encCoeff_four, one_mul]
  refine Prod.ext (Prod.ext rfl ?_) rfl
  simp only [encCoeff_two, encCoeff_five]
  rw [← hhid]
  congr 1
  ring_nf

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp
