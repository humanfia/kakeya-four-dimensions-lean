import Submission.Obl.k4_dk4_smoothed_problem.NativePrior

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_dk4_smoothed_problem.Framework

def planarCoordinates (a : Fin 3 → ℝ) : Fin 2 → ℝ := ![a 0, a 1]

def slopeCylinder (M : ℝ) (T : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (Fin 3 → ℝ) :=
  {a | (WithLp.toLp 2 (planarCoordinates a) : EuclideanSpace ℝ (Fin 2)) ∈ T ∧
    |a 2| ≤ M}

theorem volume_toLp_preimage {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) :
    volume {a : Fin d → ℝ | WithLp.toLp 2 a ∈ S} = volume S := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin d)) => μ S)
    (PiLp.volume_preserving_toLp (Fin d)).map_eq
  rw [← MeasurableEquiv.coe_toLp, (MeasurableEquiv.toLp 2 (Fin d → ℝ)).map_apply] at h
  exact h

theorem volume_split_set (S : Set (Fin 2 → ℝ)) (T : Set (Fin 1 → ℝ)) :
    volume {a : Fin 3 → ℝ |
      (fun j : Fin 2 => a (Fin.castAdd 1 j)) ∈ S ∧
      (fun j : Fin 1 => a (Fin.natAdd 2 j)) ∈ T} = volume S * volume T := by
  let e := concatenateCoefficients 2 1
  have hpre : e ⁻¹' {a : Fin 3 → ℝ |
      (fun j : Fin 2 => a (Fin.castAdd 1 j)) ∈ S ∧
      (fun j : Fin 1 => a (Fin.natAdd 2 j)) ∈ T} = S ×ˢ T := by
    ext p
    simp only [mem_preimage, mem_setOf_eq, e, concatenateCoefficients_castAdd,
      concatenateCoefficients_natAdd, mem_prod]
  rw [← (measurePreserving_concatenateCoefficients 2 1).map_eq,
    (concatenateCoefficients 2 1).map_apply, hpre, Measure.prod_prod]

theorem volume_slopeCylinder (M : ℝ) (T : Set (EuclideanSpace ℝ (Fin 2))) :
    volume (slopeCylinder M T) = volume T * ENNReal.ofReal (2 * M) := by
  have heq : slopeCylinder M T = {a : Fin 3 → ℝ |
      (fun j : Fin 2 => a (Fin.castAdd 1 j)) ∈
        {u : Fin 2 → ℝ | WithLp.toLp 2 u ∈ T} ∧
      (fun j : Fin 1 => a (Fin.natAdd 2 j)) ∈ FiniteSmoothing.coordBox M 0} := by
    ext a
    have hplan : (fun j : Fin 2 => a (Fin.castAdd 1 j)) = planarCoordinates a := by
      ext j
      fin_cases j <;> rfl
    simp [slopeCylinder, FiniteSmoothing.mem_coordBox_iff, hplan, Fin.forall_fin_one]
  rw [heq, volume_split_set, volume_toLp_preimage, FiniteSmoothing.volume_coordBox, pow_one]

theorem volume_shifted_planar_preimage (c : Fin 2 → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin 2))) :
    volume {a : Fin 2 → ℝ | WithLp.toLp 2 (a + c) ∈ S} = volume S := by
  calc
    volume {a : Fin 2 → ℝ | WithLp.toLp 2 (a + c) ∈ S} =
        volume {a : Fin 2 → ℝ | WithLp.toLp 2 a ∈ S} :=
      measure_preimage_add_right volume c {a : Fin 2 → ℝ | WithLp.toLp 2 a ∈ S}
    _ = volume S := volume_toLp_preimage S

/-- The planar marginal of one intercept box has the expected square-density
ceiling, uniformly under any translation and for arbitrary outer-measure sets. -/
theorem boxLaw_planar_le {r : ℝ} (hr : 0 < r) (b : Fin 3 → ℝ)
    (c : Fin 2 → ℝ) (S : Set (EuclideanSpace ℝ (Fin 2))) :
    FiniteSmoothing.boxLaw r b
      {a | (WithLp.toLp 2 (planarCoordinates a + c) : EuclideanSpace ℝ (Fin 2)) ∈ S} ≤
      (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * volume S := by
  have hrad : 0 < 2 * r := by positivity
  have hrad0 : ENNReal.ofReal (2 * r) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hrad
  have hradtop : ENNReal.ofReal (2 * r) ≠ ⊤ := ENNReal.ofReal_ne_top
  let P : Set (Fin 2 → ℝ) := {a | WithLp.toLp 2 (a + c) ∈ S}
  let lastBox : Set (Fin 1 → ℝ) :=
    Icc (fun _ => b 2 - r) (fun _ => b 2 + r)
  have hsub : {a : Fin 3 → ℝ | WithLp.toLp 2 (planarCoordinates a + c) ∈ S} ∩
      FiniteSmoothing.coordBox r b ⊆
      {a : Fin 3 → ℝ |
        (fun j : Fin 2 => a (Fin.castAdd 1 j)) ∈ P ∧
        (fun j : Fin 1 => a (Fin.natAdd 2 j)) ∈ lastBox} := by
    rintro a ⟨ha, hlo, hhi⟩
    constructor
    · have hplan : (fun j : Fin 2 => a (Fin.castAdd 1 j)) = planarCoordinates a := by
        ext j
        fin_cases j <;> rfl
      simpa only [P, mem_setOf_eq, hplan] using ha
    · exact ⟨fun j => by fin_cases j; exact hlo 2,
        fun j => by fin_cases j; exact hhi 2⟩
  have hI : volume lastBox = ENNReal.ofReal (2 * r) := by
    change volume (Icc (fun _ : Fin 1 => b 2 - r) (fun _ => b 2 + r)) = _
    rw [Real.volume_Icc_pi]
    simp only [Fin.prod_univ_one]
    congr 1
    ring
  rw [FiniteSmoothing.boxLaw_eq, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (FiniteSmoothing.measurableSet_coordBox r b)]
  calc
    (ENNReal.ofReal (2 * r) ^ 3)⁻¹ *
        volume ({a : Fin 3 → ℝ | WithLp.toLp 2 (planarCoordinates a + c) ∈ S} ∩
          FiniteSmoothing.coordBox r b) ≤
        (ENNReal.ofReal (2 * r) ^ 3)⁻¹ *
          volume {a : Fin 3 → ℝ |
            (fun j : Fin 2 => a (Fin.castAdd 1 j)) ∈ P ∧
            (fun j : Fin 1 => a (Fin.natAdd 2 j)) ∈ lastBox} := by
      exact mul_le_mul' le_rfl (measure_mono hsub)
    _ = (ENNReal.ofReal (2 * r) ^ 3)⁻¹ * (volume S * ENNReal.ofReal (2 * r)) := by
      rw [volume_split_set, hI, show volume P = volume S from volume_shifted_planar_preimage c S]
    _ = (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * volume S := by
      rw [mul_comm (volume S), ← mul_assoc, pow_succ,
        ENNReal.mul_inv (Or.inr hradtop) (Or.inl (ENNReal.pow_ne_top hradtop))]
      simp only [mul_assoc]
      rw [← mul_assoc (ENNReal.ofReal (2 * r))⁻¹ (ENNReal.ofReal (2 * r)) (volume S),
        ENNReal.inv_mul_cancel hrad0 hradtop, one_mul]

def pairJointEvent (t : ℝ) (S T : Set (EuclideanSpace ℝ (Fin 2))) :
    Set PairCoefficients :=
  {p | (WithLp.toLp 2 (planarCoordinates p.1 + t • planarCoordinates p.2) :
      EuclideanSpace ℝ (Fin 2)) ∈ S ∧
    (WithLp.toLp 2 (planarCoordinates p.2) : EuclideanSpace ℝ (Fin 2)) ∈ T}

theorem measurableSet_pairJointEvent (t : ℝ)
    {S T : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    MeasurableSet (pairJointEvent t S T) := by
  apply (hS.preimage _).inter (hT.preimage _)
  all_goals unfold planarCoordinates; fun_prop

theorem measurableSet_slopeCylinder (M : ℝ)
    {T : Set (EuclideanSpace ℝ (Fin 2))} (hT : MeasurableSet T) :
    MeasurableSet (slopeCylinder M T) := by
  change MeasurableSet
    ((fun a : Fin 3 → ℝ => (WithLp.toLp 2 (planarCoordinates a) :
      EuclideanSpace ℝ (Fin 2))) ⁻¹' T ∩ {a : Fin 3 → ℝ | |a 2| ≤ M})
  apply (hT.preimage _).inter (measurableSet_le _ measurable_const)
  · unfold planarCoordinates
    fun_prop
  · fun_prop

theorem component_joint_le {r M : ℝ} (hr : 0 < r) (b s : Fin 3 → ℝ)
    (hM : |s 2| + r ≤ M) (t : ℝ)
    {S T : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ((FiniteSmoothing.boxLaw r b).prod (FiniteSmoothing.boxLaw r s))
        (pairJointEvent t S T) ≤
      ((ENNReal.ofReal (2 * r) ^ 2)⁻¹ * volume S) *
        FiniteSmoothing.boxLaw r s (slopeCylinder M T) := by
  classical
  letI := FiniteSmoothing.boxLaw_isProbabilityMeasure hr b
  letI := FiniteSmoothing.boxLaw_isProbabilityMeasure hr s
  have hbox : ∀ᵐ a ∂FiniteSmoothing.boxLaw r s, a ∈ FiniteSmoothing.coordBox r s := by
    apply ae_iff.mpr
    change FiniteSmoothing.boxLaw r s (FiniteSmoothing.coordBox r s)ᶜ = 0
    rw [measure_compl (FiniteSmoothing.measurableSet_coordBox r s) (measure_ne_top _ _),
      measure_univ, FiniteSmoothing.boxLaw_self hr, tsub_self]
  rw [Measure.prod_apply_symm (measurableSet_pairJointEvent t hS hT)]
  calc
    (∫⁻ a, FiniteSmoothing.boxLaw r b
        ((fun x => (x, a)) ⁻¹' pairJointEvent t S T) ∂FiniteSmoothing.boxLaw r s) ≤
        ∫⁻ a, (slopeCylinder M T).indicator
          (fun _ => (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * volume S) a
            ∂FiniteSmoothing.boxLaw r s := by
      apply lintegral_mono_ae
      filter_upwards [hbox] with a ha
      have haM : |a 2| ≤ M := by
        have ha2 := FiniteSmoothing.mem_coordBox_iff.mp ha 2
        calc
          |a 2| = |(a 2 - s 2) + s 2| := by rw [sub_add_cancel]
          _ ≤ |a 2 - s 2| + |s 2| := abs_add_le _ _
          _ ≤ M := by linarith
      by_cases hTa : (WithLp.toLp 2 (planarCoordinates a) : EuclideanSpace ℝ (Fin 2)) ∈ T
      · rw [indicator_of_mem (show a ∈ slopeCylinder M T from ⟨hTa, haM⟩)]
        have heq : ((fun x : Fin 3 → ℝ => (x, a)) ⁻¹' pairJointEvent t S T) =
            {x : Fin 3 → ℝ | WithLp.toLp 2 (planarCoordinates x + t • planarCoordinates a) ∈ S} := by
          ext x
          simp [pairJointEvent, hTa]
        rw [heq]
        exact boxLaw_planar_le hr b (t • planarCoordinates a) S
      · have heq : ((fun x : Fin 3 → ℝ => (x, a)) ⁻¹' pairJointEvent t S T) = ∅ := by
          ext x
          simp [pairJointEvent, hTa]
        rw [heq, measure_empty]
        exact bot_le
    _ = _ := lintegral_indicator_const (measurableSet_slopeCylinder M hT) _

theorem smoothedPrior_joint_le_measurable {n : ℕ} {r M : ℝ} (hr : 0 < r)
    (b s : Fin n → Fin 3 → ℝ) (hM : ∀ i, |s i 2| + r ≤ M)
    (hs : Pairwise (fun i j => Disjoint
      (FiniteSmoothing.coordBox r (s i)) (FiniteSmoothing.coordBox r (s j))))
    (t : ℝ) {S T : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    FiniteSmoothing.smoothedPrior r b s (pairJointEvent t S T) ≤
      (n : ENNReal)⁻¹ * (ENNReal.ofReal (2 * r) ^ 3)⁻¹ *
        (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * ENNReal.ofReal (2 * M) * volume S * volume T := by
  rw [FiniteSmoothing.smoothedPrior, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply]
  have hsum : ∑ i : Fin n, FiniteSmoothing.boxLaw r (s i) (slopeCylinder M T) ≤
      (ENNReal.ofReal (2 * r) ^ 3)⁻¹ * volume (slopeCylinder M T) := by
    simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using
      FiniteSmoothing.sum_boxLaw_le r s hs (slopeCylinder M T)
  calc
    (n : ENNReal)⁻¹ * ∑ i : Fin n,
        ((FiniteSmoothing.boxLaw r (b i)).prod (FiniteSmoothing.boxLaw r (s i)))
          (pairJointEvent t S T) ≤
        (n : ENNReal)⁻¹ * ∑ i : Fin n,
          ((ENNReal.ofReal (2 * r) ^ 2)⁻¹ * volume S) *
            FiniteSmoothing.boxLaw r (s i) (slopeCylinder M T) := by
      apply mul_le_mul' le_rfl
      apply Finset.sum_le_sum
      intro i _
      exact component_joint_le hr (b i) (s i) (hM i) t hS hT
    _ = (n : ENNReal)⁻¹ * (((ENNReal.ofReal (2 * r) ^ 2)⁻¹ * volume S) *
        ∑ i : Fin n, FiniteSmoothing.boxLaw r (s i) (slopeCylinder M T)) := by
      rw [← Finset.mul_sum]
    _ ≤ (n : ENNReal)⁻¹ * (((ENNReal.ofReal (2 * r) ^ 2)⁻¹ * volume S) *
        ((ENNReal.ofReal (2 * r) ^ 3)⁻¹ * volume (slopeCylinder M T))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hsum)
    _ = _ := by rw [volume_slopeCylinder]; ac_rfl

theorem smoothedPrior_joint_le {n : ℕ} {r M : ℝ} (hr : 0 < r)
    (b s : Fin n → Fin 3 → ℝ) (hM : ∀ i, |s i 2| + r ≤ M)
    (hs : Pairwise (fun i j => Disjoint
      (FiniteSmoothing.coordBox r (s i)) (FiniteSmoothing.coordBox r (s j))))
    (t : ℝ) (S T : Set (EuclideanSpace ℝ (Fin 2))) :
    FiniteSmoothing.smoothedPrior r b s (pairJointEvent t S T) ≤
      (n : ENNReal)⁻¹ * (ENNReal.ofReal (2 * r) ^ 3)⁻¹ *
        (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * ENNReal.ofReal (2 * M) * volume S * volume T := by
  obtain ⟨S', hSS', hS', hvolS⟩ := exists_measurable_superset volume S
  obtain ⟨T', hTT', hT', hvolT⟩ := exists_measurable_superset volume T
  calc
    FiniteSmoothing.smoothedPrior r b s (pairJointEvent t S T) ≤
        FiniteSmoothing.smoothedPrior r b s (pairJointEvent t S' T') :=
      measure_mono (fun _ h => ⟨hSS' h.1, hTT' h.2⟩)
    _ ≤ _ := by
      simpa only [hvolS, hvolT] using
        smoothedPrior_joint_le_measurable hr b s hM hs t hS' hT'

theorem packLine_planarLine (p : PairCoefficients) (t : ℝ) :
    planarLine (packLine p) t =
      WithLp.toLp 2 (planarCoordinates p.1 + t • planarCoordinates p.2) := by
  have hb0 := packLine_coordinate p 0
  have hb1 := packLine_coordinate p 1
  have hs0 := packLine_slope_coordinate p 0
  have hs1 := packLine_slope_coordinate p 1
  ext j
  fin_cases j <;> simp_all [planarLine, trajectoryPoint, planarCoordinates]

theorem packLine_planarVelocity (p : PairCoefficients) :
    planarVelocity (packLine p) = WithLp.toLp 2 (planarCoordinates p.2) := by
  have hs0 := packLine_slope_coordinate p 0
  have hs1 := packLine_slope_coordinate p 1
  ext j
  fin_cases j <;> simp_all [planarVelocity, planarCoordinates]

theorem nativePrior_joint_le {n : ℕ} {r M : ℝ} (hr : 0 < r)
    (b s : Fin n → Fin 3 → ℝ) (hM : ∀ i, |s i 2| + r ≤ M)
    (hs : Pairwise (fun i j => Disjoint
      (FiniteSmoothing.coordBox r (s i)) (FiniteSmoothing.coordBox r (s j))))
    (t : ℝ) (S T : Set (EuclideanSpace ℝ (Fin 2))) :
    nativePrior r b s {l | planarLine l t ∈ S ∧ planarVelocity l ∈ T} ≤
      (n : ENNReal)⁻¹ * (ENNReal.ofReal (2 * r) ^ 3)⁻¹ *
        (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * ENNReal.ofReal (2 * M) * volume S * volume T := by
  rw [nativePrior_apply]
  have heq : packLine ⁻¹' {l | planarLine l t ∈ S ∧ planarVelocity l ∈ T} =
      pairJointEvent t S T := by
    ext p
    simp [pairJointEvent, packLine_planarLine, packLine_planarVelocity]
  rw [heq]
  exact smoothedPrior_joint_le hr b s hM hs t S T

end Submission.Obl.k4_dk4_smoothed_problem.Framework
