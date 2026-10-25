import Submission.Obl.k4_remainder_angular_cap_transport.NormDensityFormula
/- Adapted from this LOT tree, o064, session x0214, commit a612574618456ee4cdb4d54c4cee48847fe99758,
Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/.
The original file names are recorded beside each adapted group below. -/

/-!
# Angular cap of normalized problems

The velocity of a normalized trajectory is `V' = q D⁻¹ (V - u)` (`Frame.velocity_normTraj`), so
`V = u + q⁻¹ D V'` (`Frame.velocity_of_normTraj`). When `Σ |D| ≤ κ q`, every original velocity
bin at width `δ` met by a normalized velocity bin lies within `⌈κ⌉` of the bin of its corner
(`Frame.velocity_bin_close`, `Frame.coverBins`, `Frame.mem_coverBins`): `(2⌈κ⌉+1)²` bins.

`jobs B a δu` is the joint observation (observation at width `a`, velocity bins at width `δu`)
and `jointRef` its reference measure (`vol ⊗ count ⊗ count`). **`Frame.normalized_joint_le`**:
a ceiling `thr` on the joint law of a measure gives the ceiling
`thr |det obsMatrix|⁻¹ (2⌈κ⌉+1)²` on the joint law of its normalization.
-/

namespace Submission.Obl.k4_remainder_angular_cap_transport.Geometry
open MeasureTheory MvPolynomial

namespace Frame
variable (F : Frame)

/-- The velocity of a normalized trajectory: `q D⁻¹ (V - u)`. -/
theorem velocity_normTraj (l : Trajectory) (j : Fin 2) :
    velocity (F.normTraj l) j =
      F.q * (F.D⁻¹ j 0 * (velocity l 0 - F.u 0) + F.D⁻¹ j 1 * (velocity l 1 - F.u 1)) := by
  fin_cases j <;> simp [velocity, normTraj, normCoeff]

/-- Original velocities in terms of normalized ones: `V = u + q⁻¹ D V'`. -/
theorem velocity_of_normTraj (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (l : Trajectory) (j : Fin 2) :
    velocity l j = F.u j + F.q⁻¹ * (F.D j 0 * velocity (F.normTraj l) 0 +
      F.D j 1 * velocity (F.normTraj l) 1) := by
  have hm : F.D * F.D⁻¹ = 1 := Matrix.mul_nonsing_inv F.D hD
  have h00 : F.D 0 0 * F.D⁻¹ 0 0 + F.D 0 1 * F.D⁻¹ 1 0 = 1 := by
    have := congrFun (congrFun hm 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : F.D 0 0 * F.D⁻¹ 0 1 + F.D 0 1 * F.D⁻¹ 1 1 = 0 := by
    have := congrFun (congrFun hm 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : F.D 1 0 * F.D⁻¹ 0 0 + F.D 1 1 * F.D⁻¹ 1 0 = 0 := by
    have := congrFun (congrFun hm 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : F.D 1 0 * F.D⁻¹ 0 1 + F.D 1 1 * F.D⁻¹ 1 1 = 1 := by
    have := congrFun (congrFun hm 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rw [F.velocity_normTraj, F.velocity_normTraj]
  fin_cases j <;> simp <;> field_simp
  · linear_combination (-(velocity l 0 - F.u 0)) * h00 - (velocity l 1 - F.u 1) * h01
  · linear_combination (-(velocity l 0 - F.u 0)) * h10 - (velocity l 1 - F.u 1) * h11


/-- The original velocity at the corner of a normalized velocity bin. -/
noncomputable def binCenterVel (δ : ℝ) (w : Fin 2 → ℤ) (j : Fin 2) : ℝ :=
  F.u j + F.q⁻¹ * (F.D j 0 * (δ * w 0) + F.D j 1 * (δ * w 1))

theorem floor_close {x y κ : ℝ} (hκ : 0 ≤ κ) (h : |x - y| ≤ κ) :
    |⌊x⌋ - ⌊y⌋| ≤ ⌈κ⌉ := by
  rw [abs_le] at h ⊢
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  have h5 := Int.le_ceil κ
  constructor
  · have : ((⌊y⌋ : ℤ) : ℝ) - ⌈κ⌉ - 1 < ⌊x⌋ := by push_cast; linarith
    have : ⌊y⌋ - ⌈κ⌉ - 1 < ⌊x⌋ := by exact_mod_cast this
    omega
  · have : ((⌊x⌋ : ℤ) : ℝ) < ⌊y⌋ + ⌈κ⌉ + 1 := by push_cast; linarith
    have : ⌊x⌋ < ⌊y⌋ + ⌈κ⌉ + 1 := by exact_mod_cast this
    omega

/-- **Velocity bin covering**: the original velocity bin at width `δ` is within `⌈κ⌉` of the
bin of the corner of the normalized velocity bin, when `Σ |D| ≤ κ q`. -/
theorem velocity_bin_close (hq : 0 < F.q) (hD : IsUnit F.D.det) {κ δ : ℝ} (hδ : 0 < δ)
    (hκ : 0 ≤ κ) (hDs : (∑ e : Fin 2, ∑ e' : Fin 2, |F.D e e'|) ≤ κ * F.q) (l : Trajectory)
    (j : Fin 2) :
    |⌊velocity l j / δ⌋ -
      ⌊F.binCenterVel δ (fun i => ⌊velocity (F.normTraj l) i / δ⌋) j / δ⌋| ≤ ⌈κ⌉ := by
  apply floor_close hκ
  set w : Fin 2 → ℤ := fun i => ⌊velocity (F.normTraj l) i / δ⌋
  set θ : Fin 2 → ℝ := fun i => velocity (F.normTraj l) i / δ - w i
  have hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1 := by
    intro i
    have a := Int.floor_le (velocity (F.normTraj l) i / δ)
    have b := Int.lt_floor_add_one (velocity (F.normTraj l) i / δ)
    exact ⟨by simp only [θ, w]; linarith, by simp only [θ, w]; linarith⟩
  have hV : ∀ i, velocity (F.normTraj l) i = δ * (w i + θ i) := by
    intro i; simp only [θ]; field_simp; ring
  have hdiff : velocity l j / δ - F.binCenterVel δ w j / δ =
      F.q⁻¹ * (F.D j 0 * θ 0 + F.D j 1 * θ 1) := by
    rw [F.velocity_of_normTraj hq.ne' hD l j, hV 0, hV 1]
    unfold binCenterVel
    field_simp
    ring
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.mpr hq)]
  have hrow : |F.D j 0 * θ 0 + F.D j 1 * θ 1| ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |F.D e e'| := by
    calc |F.D j 0 * θ 0 + F.D j 1 * θ 1| ≤ |F.D j 0| * |θ 0| + |F.D j 1| * |θ 1| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |F.D j 0| + |F.D j 1| := by
          have e0 : |θ 0| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hθ 0]
          have e1 : |θ 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hθ 1]
          nlinarith [abs_nonneg (F.D j 0), abs_nonneg (F.D j 1)]
      _ ≤ _ := by
          have hsum : ∑ e : Fin 2, ∑ e' : Fin 2, |F.D e e'| =
              |F.D 0 0| + |F.D 0 1| + (|F.D 1 0| + |F.D 1 1|) := by simp [Fin.sum_univ_two]
          rw [hsum]
          fin_cases j <;> simp <;> linarith [abs_nonneg (F.D 0 0), abs_nonneg (F.D 0 1),
            abs_nonneg (F.D 1 0), abs_nonneg (F.D 1 1)]
  calc F.q⁻¹ * |F.D j 0 * θ 0 + F.D j 1 * θ 1| ≤ F.q⁻¹ * (κ * F.q) :=
        mul_le_mul_of_nonneg_left (hrow.trans hDs) (inv_nonneg.mpr hq.le)
    _ = κ := by field_simp


end Frame

/-- The joint observation: observation at width `a` and velocity bins at width `δu`. -/
noncomputable def jobs (B a δu : ℝ) (p : Incidence) :
    (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) :=
  (obs B a p, fun j => ⌊velocity p.1 j / δu⌋)

theorem measurable_velocity_coord (j : Fin 2) : Measurable fun l : Trajectory => velocity l j := by
  fin_cases j <;> simp [velocity] <;> fun_prop

theorem measurable_jobs (B a δu : ℝ) : Measurable (jobs B a δu) := by
  refine (measurable_obs B a).prodMk ?_
  refine measurable_pi_iff.mpr fun j => ?_
  exact Int.measurable_floor.comp
    (((measurable_velocity_coord j).comp measurable_fst).div_const _)

namespace Frame
variable (F : Frame)

/-- The original velocity bins covering a normalized velocity bin. -/
noncomputable def coverBins (δ κ : ℝ) (w : Fin 2 → ℤ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun j => Finset.Icc (⌊F.binCenterVel δ w j / δ⌋ - ⌈κ⌉)
    (⌊F.binCenterVel δ w j / δ⌋ + ⌈κ⌉)

theorem card_coverBins (δ κ : ℝ) (hκ : 0 ≤ κ) (w : Fin 2 → ℤ) :
    ((F.coverBins δ κ w).card : ENNReal) = ((2 * ⌈κ⌉ + 1).toNat : ENNReal) ^ 2 := by
  have hc : 0 ≤ ⌈κ⌉ := Int.ceil_nonneg hκ
  unfold coverBins
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc]
  have : ∀ x : ℤ, (x + ⌈κ⌉ + 1 - (x - ⌈κ⌉)) = 2 * ⌈κ⌉ + 1 := fun x => by ring
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rfl

theorem mem_coverBins (hq : 0 < F.q) (hD : IsUnit F.D.det) {κ δ : ℝ} (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (hDs : (∑ e : Fin 2, ∑ e' : Fin 2, |F.D e e'|) ≤ κ * F.q) (l : Trajectory) :
    (fun j => ⌊velocity l j / δ⌋) ∈
      F.coverBins δ κ (fun i => ⌊velocity (F.normTraj l) i / δ⌋) := by
  unfold coverBins
  rw [Fintype.mem_piFinset]
  intro j
  have h := F.velocity_bin_close hq hD hδ hκ hDs l j
  rw [abs_le] at h
  rw [Finset.mem_Icc]
  constructor <;> linarith [h.1, h.2]

end Frame

/-- The reference measure of joint observations. -/
noncomputable abbrev jointRef : Measure ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure ℤ)).prod
    (Measure.count : Measure (Fin 2 → ℤ))

theorem jointRef_apply {S : Set ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ))}
    (hS : MeasurableSet S) :
    jointRef S = ∑' w, ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
      (Measure.count : Measure ℤ)) {y | (y, w) ∈ S} := by
  rw [jointRef, Measure.prod_apply_symm hS, lintegral_count]
  rfl

theorem jointRef_prod_singleton (A : Set (EuclideanSpace ℝ (Fin 3) × ℤ)) (w : Fin 2 → ℤ) :
    jointRef (A ×ˢ {w}) = ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
      (Measure.count : Measure ℤ)) A := by
  rw [jointRef, Measure.prod_prod, Measure.count_singleton, mul_one]

namespace Frame
variable (F : Frame)

/-- **Angular transfer**: a ceiling `thr` on the original joint observation density of a
measure gives the ceiling `thr |det obsMatrix|⁻¹ (2⌈κ⌉+1)²` on the joint observation density
of its normalization, when `Σ |D| ≤ κ q`. -/
theorem normalized_joint_le (hq : 0 < F.q) (hD : IsUnit F.D.det) {κ δu : ℝ} (hδu : 0 < δu)
    (hκ : 0 ≤ κ) (hDs : (∑ e : Fin 2, ∑ e' : Fin 2, |F.D e e'|) ≤ κ * F.q)
    (ν₀ : Measure Incidence) (B δ a : ℝ) (hδ : δ ≠ 0) (thr : ENNReal)
    (hceil : Measure.map (jobs B (δ * a) δu) ν₀ ≤ thr • jointRef) :
    Measure.map (jobs (B / δ) a δu) (Measure.map F.normInc ν₀) ≤
      (thr * (ENNReal.ofReal |F.obsMatrix.det|⁻¹ * ((2 * ⌈κ⌉ + 1).toNat : ENNReal) ^ 2)) •
        jointRef := by
  classical
  set ρ := ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure ℤ))
  set e := F.obsEquiv hq.ne' hD
  set C := ENNReal.ofReal |F.obsMatrix.det|⁻¹
  set m := ((2 * ⌈κ⌉ + 1).toNat : ENNReal) ^ 2
  have he : ∀ A, ρ (e ⁻¹' A) = C * ρ A := by
    intro A
    have := e.map_apply (μ := ρ) A
    rw [F.map_obsEquiv hq.ne' hD, Measure.smul_apply, smul_eq_mul] at this
    exact this.symm
  refine Measure.le_iff.mpr fun S hS => ?_
  rw [Measure.map_apply (measurable_jobs _ _ _) hS,
    Measure.map_apply F.measurable_normInc ((measurable_jobs _ _ _) hS), Measure.smul_apply,
    smul_eq_mul, jointRef_apply hS]
  set T : (Fin 2 → ℤ) → Set (EuclideanSpace ℝ (Fin 3) × ℤ) := fun w => {y | (y, w) ∈ S}
  have hsub : F.normInc ⁻¹' (jobs (B / δ) a δu ⁻¹' S) ⊆
      ⋃ w' : Fin 2 → ℤ, ⋃ w ∈ F.coverBins δu κ w', jobs B (δ * a) δu ⁻¹' ((e ⁻¹' T w') ×ˢ {w}) := by
    intro p hp
    simp only [Set.mem_preimage] at hp
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
    refine ⟨fun i => ⌊velocity (F.normTraj p.1) i / δu⌋, fun j => ⌊velocity p.1 j / δu⌋,
      F.mem_coverBins hq hD hδu hκ hDs p.1, ?_, rfl⟩
    show e (obs B (δ * a) p) ∈ T _
    have h1 : jobs (B / δ) a δu (F.normInc p) =
        (Prod.map F.obsBase id (obs B (δ * a) p), fun i => ⌊velocity (F.normTraj p.1) i / δu⌋) := by
      simp only [jobs]
      rw [F.obs_normInc hq.ne' B δ a hδ p]
      rfl
    rw [h1] at hp
    exact hp
  calc ν₀ (F.normInc ⁻¹' (jobs (B / δ) a δu ⁻¹' S))
      ≤ ν₀ (⋃ w' : Fin 2 → ℤ, ⋃ w ∈ F.coverBins δu κ w',
          jobs B (δ * a) δu ⁻¹' ((e ⁻¹' T w') ×ˢ {w})) := measure_mono hsub
    _ ≤ ∑' w' : Fin 2 → ℤ, ν₀ (⋃ w ∈ F.coverBins δu κ w',
          jobs B (δ * a) δu ⁻¹' ((e ⁻¹' T w') ×ˢ {w})) := measure_iUnion_le _
    _ ≤ ∑' w' : Fin 2 → ℤ, ∑ w ∈ F.coverBins δu κ w',
          ν₀ (jobs B (δ * a) δu ⁻¹' ((e ⁻¹' T w') ×ˢ {w})) :=
        ENNReal.tsum_le_tsum fun w' => measure_biUnion_finset_le _ _
    _ ≤ ∑' w' : Fin 2 → ℤ, ∑ w ∈ F.coverBins δu κ w', thr * ρ (e ⁻¹' T w') := by
        refine ENNReal.tsum_le_tsum fun w' => Finset.sum_le_sum fun w _ => ?_
        have hT : MeasurableSet (T w') := measurable_prodMk_right hS
        have hm : MeasurableSet ((e ⁻¹' T w') ×ˢ ({w} : Set (Fin 2 → ℤ))) :=
          (e.measurable hT).prod (measurableSet_singleton w)
        have := hceil ((e ⁻¹' T w') ×ˢ ({w} : Set (Fin 2 → ℤ)))
        rw [Measure.map_apply (measurable_jobs _ _ _) hm, Measure.smul_apply, smul_eq_mul,
          jointRef_prod_singleton] at this
        exact this
    _ = ∑' w' : Fin 2 → ℤ, thr * (C * m) * ρ (T w') := by
        refine tsum_congr fun w' => ?_
        rw [Finset.sum_const, nsmul_eq_mul, he, F.card_coverBins δu κ hκ w']
        ring
    _ = thr * (C * m) * ∑' w', ρ (T w') := ENNReal.tsum_mul_left

end Frame
end Submission.Obl.k4_remainder_angular_cap_transport.Geometry
