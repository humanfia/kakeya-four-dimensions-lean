/- Adapted from this LOT tree, obligation o119, session x0404, commit b1aa67e,
   Submission/Obl/k4_finite_width_critical_contradiction/CompDecode.lean. -/
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CompObs

/-!
# Decoding observation densities of the encoded world

At one sample: the encoded incidence law restricted to any measurable selection is the
weighted sum of the world laws restricted to the decoded selections; its joint observation
is the weighted sum of shifted world observations.  World densities supported in a hidden
window, shifted into disjoint windows and summed, give a density of the encoded
observation whose value at an encoded incidence is the weighted world density.
-/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp

attribute [local simp] encCoeff_zero encCoeff_one encCoeff_two encCoeff_three encCoeff_four encCoeff_five

open MeasureTheory Set
open scoped ENNReal

theorem measurable_jobs (B a v : ℝ) : Measurable (jobs B a v) := by
  unfold jobs
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
  · refine (PiLp.continuous_toLp 2 _).measurable.comp ?_
    refine Measurable.of_eval fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  · exact Int.measurable_floor.comp (by fun_prop)
  · refine Measurable.of_eval fun j => ?_
    refine Int.measurable_floor.comp ?_
    refine Measurable.div_const ?_ _
    have : Measurable (fun p : Inc => (WithLp.toLp 2 ![p.1.2 3, p.1.2 4] :
        EuclideanSpace ℝ (Fin 2))) := by
      refine (PiLp.continuous_toLp 2 _).measurable.comp ?_
      refine Measurable.of_eval fun i => ?_
      fin_cases i <;> simp <;> fun_prop
    exact (measurable_pi_apply j).comp ((PiLp.continuous_ofLp 2 _).measurable.comp this)

/-- The encoded law restricted to a measurable selection. -/
theorem encLaw_restrict (W : ℕ) (a b o : Fin W → ℝ) (ν : Fin W → Measure Traj)
    [∀ c, SFinite (ν c)] {S : Set Inc} (hS : MeasurableSet S) :
    ((encPrior W a b o ν).prod volume).restrict S =
      ∑ c, ENNReal.ofReal (a c) • Measure.map (encInc W c (b c) (o c))
        (((ν c).prod volume).restrict (encInc W c (b c) (o c) ⁻¹' S)) := by
  have hprod : (encPrior W a b o ν).prod volume = ∑ c, ENNReal.ofReal (a c) •
      Measure.map (encInc W c (b c) (o c)) ((ν c).prod volume) := by
    unfold encPrior
    rw [← Measure.sum_fintype, Measure.prod_sum_left]
    rw [← Measure.sum_fintype]
    congr 1
    funext c
    rw [Measure.prod_smul_left]
    congr 1
    have h := Measure.map_prod_map (ν c) (volume : Measure ℝ)
      (measurable_encTraj W c (b c) (o c)) measurable_id
    rw [Measure.map_id] at h
    rw [h]
    rfl
  rw [hprod]
  ext T hT
  rw [Measure.restrict_apply hT]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [Measure.map_apply (measurable_encInc _ _ _ _) (hT.inter hS),
    Measure.map_apply (measurable_encInc _ _ _ _) hT,
    Measure.restrict_apply ((measurable_encInc _ _ _ _) hT), preimage_inter]

/-- The joint observation of the encoded law is the weighted sum of shifted world
observations. -/
theorem map_jobs_encLaw (W : ℕ) (a : Fin W → ℝ) (B : Fin W → ℝ) (o : Fin W → ℝ)
    (ν : Fin W → Measure Traj) [∀ c, SFinite (ν c)] {S : Set Inc} (hS : MeasurableSet S)
    {σ a' v : ℝ} (hσ : 0 < σ) (ha' : 0 < a') (Z : Fin W → ℤ)
    (ho : ∀ c, o c = (Z c : ℝ) * (σ * a')) :
    Measure.map (jobs 1 (σ * a') v)
        (((encPrior W a (fun c => B c * σ) o ν).prod volume).restrict S) =
      ∑ c, ENNReal.ofReal (a c) • Measure.map (shiftObs (Z c))
        (Measure.map (jobs (B c) a' v)
          (((ν c).prod volume).restrict (encInc W c (B c * σ) (o c) ⁻¹' S))) := by
  rw [encLaw_restrict W a _ o ν hS, Measure.map_finset_sum (measurable_jobs _ _ _).aemeasurable]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Measure.map_smul, Measure.map_map (measurable_jobs _ _ _) (measurable_encInc _ _ _ _),
    Measure.map_map (measurable_shiftObs _) (measurable_jobs _ _ _)]
  · congr 2
    funext p
    exact jobs_encInc W c hσ ha' (Z c) (o c) (ho c) p
  · exact (measurable_jobs _ _ _).aemeasurable

/-- Hidden window of half-width `H`. -/
def homeWin (H : ℤ) : Set JObs := {q | |q.1.2| < H}

theorem measurableSet_homeWin (H : ℤ) : MeasurableSet (homeWin H) :=
  (measurable_of_countable (fun n : ℤ => |n|)).comp (measurable_snd.comp measurable_fst)
    (measurableSet_Iio)

theorem shiftObs_not_mem_homeWin {H : ℤ} {q : JObs} (hq : q ∈ homeWin H) {k : ℤ} (hk : k ≠ 0) :
    shiftObs (2 * H * k) q ∉ homeWin H := by
  simp only [homeWin, shiftObs, mem_ofPred_eq, not_lt] at hq ⊢
  have hk1 : 1 ≤ |k| := Int.one_le_abs hk
  have hH : 0 ≤ H := le_trans (abs_nonneg _) hq.le
  have : 2 * H ≤ |2 * H * k| := by
    rw [abs_mul, abs_of_nonneg (by omega : (0:ℤ) ≤ 2 * H)]
    nlinarith
  have h2 : |2 * H * k| ≤ |q.1.2 + 2 * H * k| + |q.1.2| := by
    have := abs_sub (q.1.2 + 2 * H * k) q.1.2
    simp only [add_sub_cancel_left] at this
    linarith
  linarith

/-- The hidden bin is in the window when the scaled hidden coordinate is small. -/
theorem jobs_mem_homeWin {B a' v : ℝ} (ha' : 0 < a') {H : ℤ} {p : Inc}
    (hp : |B * (p.1.2 2 + p.2 * p.1.2 5)| + a' < H * a') : jobs B a' v p ∈ homeWin H := by
  simp only [homeWin, jobs, mem_ofPred_eq]
  have hx : |B * (p.1.2 2 + p.2 * p.1.2 5) / a'| + 1 < H := by
    rw [abs_div, abs_of_pos ha', div_add_one ha'.ne', div_lt_iff₀ ha']
    linarith
  have h1 := Int.floor_le (B * (p.1.2 2 + p.2 * p.1.2 5) / a')
  have h2 := Int.lt_floor_add_one (B * (p.1.2 2 + p.2 * p.1.2 5) / a')
  have habs : |(⌊B * (p.1.2 2 + p.2 * p.1.2 5) / a'⌋ : ℝ)| < H := by
    rw [abs_lt]
    constructor
    · have := neg_abs_le (B * (p.1.2 2 + p.2 * p.1.2 5) / a')
      linarith
    · have := le_abs_self (B * (p.1.2 2 + p.2 * p.1.2 5) / a')
      linarith
  exact_mod_cast habs

/-- Pushing a density forward along a hidden shift. -/
theorem map_shiftObs_withDensity (z : ℤ) {f : JObs → ℝ≥0∞} (hf : Measurable f) :
    Measure.map (shiftObs z) (jref.withDensity f) = jref.withDensity (f ∘ shiftObs (-z)) := by
  ext s hs
  rw [Measure.map_apply (measurable_shiftObs z) hs,
    withDensity_apply _ ((measurable_shiftObs z) hs), withDensity_apply _ hs]
  conv_rhs => rw [← map_shiftObs_jref z]
  rw [setLIntegral_map hs (hf.comp (measurable_shiftObs (-z))) (measurable_shiftObs z)]
  congr 1
  funext x
  simp [shiftObs]

/-- A world density supported in a window. -/
theorem withDensity_indicator_homeWin {μ : Measure Inc} {B a' v : ℝ} {H : ℤ}
    {g : JObs → ℝ≥0∞}
    (hg : Measure.map (jobs B a' v) μ = jref.withDensity g)
    (hhome : ∀ᵐ q ∂μ, jobs B a' v q ∈ homeWin H) :
    Measure.map (jobs B a' v) μ = jref.withDensity ((homeWin H).indicator g) := by
  rw [withDensity_indicator (measurableSet_homeWin H), ← restrict_withDensity
    (measurableSet_homeWin H), ← hg, Measure.restrict_eq_self_of_ae_mem]
  exact (ae_map_iff (measurable_jobs _ _ _).aemeasurable (measurableSet_homeWin H)).2 hhome

/-- **Per-sample decoding.**  World densities `g c`, supported in the window of half-width
`H`, shifted by `Z c = 2 H c` and summed with the weights, give a density of the encoded
joint observation, whose value at an encoded incidence of world `c` is `a c` times the
world density. -/
theorem decode_density (W : ℕ) (a B o : Fin W → ℝ) (ν : Fin W → Measure Traj)
    [∀ c, SFinite (ν c)] {S : Set Inc} (hS : MeasurableSet S)
    {σ a' v : ℝ} (hσ : 0 < σ) (ha' : 0 < a') (H : ℤ)
    (ho : ∀ c : Fin W, o c = ((2 * H * (c : ℤ) : ℤ) : ℝ) * (σ * a'))
    (g : Fin W → JObs → ℝ≥0∞) (hgm : ∀ c, Measurable (g c))
    (hg : ∀ c, Measure.map (jobs (B c) a' v)
      (((ν c).prod volume).restrict (encInc W c (B c * σ) (o c) ⁻¹' S)) =
        jref.withDensity (g c))
    (hhome : ∀ c : Fin W, ∀ᵐ q ∂(((ν c).prod volume).restrict (encInc W c (B c * σ) (o c) ⁻¹' S)),
      jobs (B c) a' v q ∈ homeWin H) :
    ∃ G : JObs → ℝ≥0∞, Measurable G ∧
      Measure.map (jobs 1 (σ * a') v)
        (((encPrior W a (fun c => B c * σ) o ν).prod volume).restrict S) =
          jref.withDensity G ∧
      ∀ c : Fin W, ∀ᵐ q ∂(((ν c).prod volume).restrict (encInc W c (B c * σ) (o c) ⁻¹' S)),
        G (jobs 1 (σ * a') v (encInc W c (B c * σ) (o c) q)) =
          ENNReal.ofReal (a c) * g c (jobs (B c) a' v q) := by
  classical
  let Z : Fin W → ℤ := fun c => 2 * H * (c : ℤ)
  let gH : Fin W → JObs → ℝ≥0∞ := fun c => (homeWin H).indicator (g c)
  have hgHm : ∀ c, Measurable (gH c) := fun c => (hgm c).indicator (measurableSet_homeWin H)
  refine ⟨fun x => ∑ c, ENNReal.ofReal (a c) * gH c (shiftObs (-Z c) x), ?_, ?_, ?_⟩
  · exact Finset.measurable_sum _ fun c _ =>
      (measurable_const.mul ((hgHm c).comp (measurable_shiftObs _)))
  · rw [map_jobs_encLaw W a B o ν hS hσ ha' Z ho]
    have hsum : jref.withDensity (fun x => ∑ c, ENNReal.ofReal (a c) * gH c (shiftObs (-Z c) x)) =
        ∑ c, jref.withDensity (fun x => ENNReal.ofReal (a c) * gH c (shiftObs (-Z c) x)) := by
      ext s hs
      rw [withDensity_apply _ hs, Measure.coe_finsetSum, Finset.sum_apply]
      rw [lintegral_finsetSum (s := Finset.univ)
        (f := fun c x => ENNReal.ofReal (a c) * gH c (shiftObs (-Z c) x))
        (fun c _ => ((hgHm c).comp (measurable_shiftObs _)).const_mul _)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [withDensity_apply _ hs]
    rw [hsum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [withDensity_indicator_homeWin (hg c) (hhome c),
      map_shiftObs_withDensity _ (hgHm c)]
    rw [show (fun x => ENNReal.ofReal (a c) * gH c (shiftObs (-Z c) x)) =
      (fun _ => ENNReal.ofReal (a c)) * (gH c ∘ shiftObs (-Z c)) from rfl]
    rw [withDensity_mul _ measurable_const ((hgHm c).comp (measurable_shiftObs _)),
      withDensity_const, withDensity_smul_measure]
  · intro c
    filter_upwards [hhome c] with q hq
    rw [jobs_encInc W c hσ ha' (Z c) (o c) (ho c) q]
    rw [Finset.sum_eq_single c]
    · simp only [shiftObs_shiftObs, add_neg_cancel, shiftObs_zero, gH,
        Set.indicator_of_mem hq]
    · intro c' _ hc'
      have hk : ((c : ℤ) - (c' : ℤ)) ≠ 0 := by
        intro h
        apply hc'
        ext
        omega
      have hshift : shiftObs (-Z c') (shiftObs (Z c) (jobs (B c) a' v q)) =
          shiftObs (2 * H * ((c : ℤ) - (c' : ℤ))) (jobs (B c) a' v q) := by
        rw [shiftObs_shiftObs]
        congr 1
        simp only [Z]
        ring
      rw [hshift]
      simp only [gH, Set.indicator_of_notMem (shiftObs_not_mem_homeWin hq hk), mul_zero]
    · intro h; exact absurd (Finset.mem_univ c) h

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp
