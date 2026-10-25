import Submission.Obl.k4_scalar_capped_heavy_potential.EfficientSelection

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d50c59d5b1367f287a76eef33f4c400a8e312ee2,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ChartPriorMass.lean`.
The namespace and internal imports are changed to o272. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- Discarding old charts with a poor current-to-original-prior ratio leaves
an original prior budget controlling all current mass, up to the chosen cutoff.
The same original assignment mass supplies every conditional density floor. -/
theorem heavy_original_chart_priors {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (σ : Measure (α × ℝ)) [IsFiniteMeasure σ]
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : ∀ᵐ p ∂σ, ∃ i, p ∈ A i ×ˢ Icc (0 : ℝ) 1)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hdom : σ ≤ ENNReal.ofReal K • ν.prod volume) :
    ∃ F : Finset ι,
      (∀ i ∈ F, 0 < ν (A i) ∧ ENNReal.ofReal δ * ν (A i) ≤
        σ (A i ×ˢ Icc (0 : ℝ) 1)) ∧
      σ.real univ ≤ K * (∑ i ∈ F, ν.real (A i)) + δ := by
  classical
  let E : ι → Set (α × ℝ) := fun i => A i ×ˢ Icc (0 : ℝ) 1
  have hE : ∀ i, MeasurableSet (E i) := fun i => (hA i).prod measurableSet_Icc
  have hdE : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint E := by
    intro i hi j hj hne
    apply disjoint_left.mpr
    rintro p ⟨hpi, -⟩ ⟨hpj, -⟩
    exact disjoint_left.mp (hdisj hne) hpi hpj
  have hsumσ : (∑ i, σ.real (E i)) = σ.real univ := by
    have hsum : (∑ i, σ.real (E i)) = σ.real (⋃ i, E i) := by
      simpa using (measureReal_biUnion_finset hdE (fun i hi => hE i)).symm
    have hU : ∀ᵐ p ∂σ, p ∈ ⋃ i, E i := hcover.mono (by
      rintro p ⟨i, hi⟩
      exact mem_iUnion.mpr ⟨i, hi⟩)
    have heq : σ (⋃ i, E i) = σ univ := measure_congr (hU.mono (by
      intro p hp
      simp only [hp, mem_univ]))
    exact hsum.trans (congrArg ENNReal.toReal heq)
  have hsumν : (∑ i, ν.real (A i)) ≤ 1 := by
    have hdA : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint A :=
      fun i hi j hj hne => hdisj hne
    have hsum : (∑ i, ν.real (A i)) = ν.real (⋃ i, A i) := by
      simpa using (measureReal_biUnion_finset hdA (fun i hi => hA i)).symm
    rw [hsum]
    exact measureReal_le_one
  have hentry (i : ι) : σ.real (E i) ≤ K * ν.real (A i) := by
    have hh : σ (E i) ≤ ENNReal.ofReal K * ν (A i) := by
      simpa only [E, Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
        Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one] using hdom (E i)
    have hr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν (A i))) hh
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using hr
  let F := Finset.univ.filter (fun i => 0 < σ.real (E i) ∧ δ * ν.real (A i) ≤ σ.real (E i))
  have hb := Submission.Obl.k4_scalar_capped_heavy_potential.efficient_group_mass_budget
    Finset.univ (fun i => σ.real (E i)) (fun i => ν.real (A i)) hδ
    (fun i hi => measureReal_nonneg) (fun i hi => measureReal_nonneg) hsumν
  change (∑ i, σ.real (E i)) ≤ (∑ i ∈ F, σ.real (E i)) + δ * 1 at hb
  rw [hsumσ, mul_one] at hb
  refine ⟨F, ?_, hb.trans (add_le_add ?_ le_rfl)⟩
  · intro i hi
    have hfi := (Finset.mem_filter.mp hi).2
    have hprior : 0 < ν.real (A i) := by
      by_contra hn
      have hz : ν.real (A i) = 0 := le_antisymm (le_of_not_gt hn) measureReal_nonneg
      have he := hentry i
      rw [hz, mul_zero] at he
      exact (not_lt_of_ge he) hfi.1
    refine ⟨(ENNReal.ofReal_pos.mpr hprior).trans_eq
      (ENNReal.ofReal_toReal (measure_ne_top ν (A i))), ?_⟩
    calc
      _ = ENNReal.ofReal (δ * ν.real (A i)) := by
        rw [ENNReal.ofReal_mul hδ, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top ν (A i))]
      _ ≤ ENNReal.ofReal (σ.real (E i)) := ENNReal.ofReal_le_ofReal hfi.2
      _ = _ := ENNReal.ofReal_toReal (measure_ne_top σ (E i))
  · calc
      _ ≤ ∑ i ∈ F, K * ν.real (A i) := Finset.sum_le_sum (fun i hi => hentry i)
      _ = _ := (Finset.mul_sum _ _ _).symm

end

end Submission.Obl.k4_horizontal_strict_parameter_step
