import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedWorlds

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set

noncomputable section

/-- Select groups using their unchanged reference prior. Excessive support and
insufficient current mass are charged once to their two global budgets. -/
theorem finite_groups_by_reference {ι : Type*} (Q : Finset ι)
    (prior mass cost : ι → ℝ) {K H B delta : ℝ}
    (hK : 0 ≤ K) (hH : 0 < H) (hd : 0 ≤ delta)
    (hp : ∀ i ∈ Q, 0 ≤ prior i) (hm : ∀ i ∈ Q, 0 ≤ mass i)
    (hc : ∀ i ∈ Q, 0 ≤ cost i) (hdom : ∀ i ∈ Q, mass i ≤ K * prior i)
    (hpsum : ∑ i ∈ Q, prior i ≤ 1) (hcsum : ∑ i ∈ Q, cost i ≤ B) :
    ∃ G : Finset ι, G ⊆ Q ∧
      (∀ i ∈ G, 0 < prior i ∧ cost i ≤ H * prior i ∧ delta * prior i ≤ mass i) ∧
      (∑ i ∈ Q, mass i) ≤ (∑ i ∈ G, mass i) + K * B / H + delta := by
  classical
  let good := fun i => 0 < prior i ∧ cost i ≤ H * prior i ∧ delta * prior i ≤ mass i
  let G := Q.filter good
  have hpoint (i : ι) (hi : i ∈ Q) :
      mass i ≤ (if good i then mass i else 0) + (K / H) * cost i + delta * prior i := by
    by_cases hg : good i
    · simp only [if_pos hg]
      nlinarith [mul_nonneg (div_nonneg hK hH.le) (hc i hi), mul_nonneg hd (hp i hi)]
    · simp only [if_neg hg, zero_add]
      by_cases hpi : 0 < prior i
      · by_cases hci : cost i ≤ H * prior i
        · have hmi : mass i ≤ delta * prior i := le_of_lt (lt_of_not_ge
            (fun h => hg ⟨hpi, hci, h⟩))
          exact hmi.trans (le_add_of_nonneg_left (mul_nonneg (div_nonneg hK hH.le) (hc i hi)))
        · have hpci : prior i ≤ cost i / H := (le_div_iff₀ hH).mpr (by nlinarith [lt_of_not_ge hci])
          have hh := (hdom i hi).trans (mul_le_mul_of_nonneg_left hpci hK)
          have heq : K * (cost i / H) = (K / H) * cost i := by ring
          rw [heq] at hh
          exact hh.trans (le_add_of_nonneg_right (mul_nonneg hd (hp i hi)))
      · have hp0 : prior i = 0 := le_antisymm (le_of_not_gt hpi) (hp i hi)
        have hm0 : mass i ≤ 0 := by simpa only [hp0, mul_zero] using hdom i hi
        exact hm0.trans (add_nonneg (mul_nonneg (div_nonneg hK hH.le) (hc i hi))
          (mul_nonneg hd (hp i hi)))
  refine ⟨G, Finset.filter_subset _ _, fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
  calc
    _ ≤ ∑ i ∈ Q, ((if good i then mass i else 0) + (K / H) * cost i + delta * prior i) :=
      Finset.sum_le_sum hpoint
    _ = (∑ i ∈ G, mass i) + (K / H) * (∑ i ∈ Q, cost i) + delta * (∑ i ∈ Q, prior i) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, G, Finset.sum_filter]
    _ ≤ (∑ i ∈ G, mass i) + (K / H) * B + delta * 1 := by
      gcongr
    _ = _ := by ring

/-- A finite selection of whole original coefficient crops. All conditional
mass and support bounds use the original prior; the selected current law is a
restriction of the given current law. -/
theorem select_scalar_worlds {α : Type} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ ζ : Measure (α × ℝ)) [IsFiniteMeasure ζ]
    {K H B delta chi g : ℝ} (hK : 0 ≤ K) (hH : 0 < H) (hd : 0 ≤ delta)
    (hdom : μ ≤ ENNReal.ofReal K • ν.prod volume) (hζ : ζ ≤ μ)
    (C : Set α) (hC : MeasurableSet C) (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (Q : Finset (Fin 4 → ℤ))
    (hQ : ∀ l ∈ C, projectedWorldTag chi g (b l) ∈ Q)
    (hsource : ∀ᵐ z ∂ζ, z.1 ∈ C) (hunit : ∀ᵐ z ∂ζ, z.2 ∈ Icc (0 : ℝ) 1)
    (cost : (Fin 4 → ℤ) → ℝ) (hcost : ∀ u ∈ Q, 0 ≤ cost u)
    (hbudget : ∑ u ∈ Q, cost u ≤ B) :
    ∃ (G : Finset (Fin 4 → ℤ)) (ζ₁ : Measure (α × ℝ)), G ⊆ Q ∧ ζ₁ ≤ ζ ∧
      (ζ univ).toReal ≤ (ζ₁ univ).toReal + K * B / H + delta ∧
      (∀ᵐ z ∂ζ₁, ∃ u ∈ G, z.1 ∈ projectedWorldCrop C b chi g u) ∧
      (ζ₁ univ).toReal ≤ K * (∑ u ∈ G, (ν (projectedWorldCrop C b chi g u)).toReal) ∧
      ∀ u ∈ G, ν (projectedWorldCrop C b chi g u) ≠ 0 ∧
        cost u ≤ H * (ν (projectedWorldCrop C b chi g u)).toReal ∧
        delta * (ν (projectedWorldCrop C b chi g u)).toReal ≤
          (ζ₁ (projectedWorldCrop C b chi g u ×ˢ Icc (0 : ℝ) 1)).toReal := by
  classical
  let A := fun u => projectedWorldCrop C b chi g u
  let E := fun u => A u ×ˢ Icc (0 : ℝ) 1
  have hA (u : Fin 4 → ℤ) : MeasurableSet (A u) := measurableSet_projectedWorldCrop hC b hb chi g u
  have hE (u : Fin 4 → ℤ) : MeasurableSet (E u) := (hA u).prod measurableSet_Icc
  have hEdisj (u u' : Fin 4 → ℤ) (hne : u ≠ u') : Disjoint (E u) (E u') :=
    Set.disjoint_prod.mpr (Or.inl (projectedWorldCrop_disjoint C b chi g hne))
  have hunion (F : Finset (Fin 4 → ℤ)) : ζ (⋃ u ∈ F, E u) = ∑ u ∈ F, ζ (E u) := by
    apply measure_biUnion_finset
    · intro u hu u' hu' hne
      exact hEdisj u u' hne
    · intro u hu
      exact hE u
  have htotal : ζ (⋃ u ∈ Q, E u) = ζ univ := by
    apply measure_congr
    filter_upwards [hsource, hunit] with z hz hzt
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      exact mem_iUnion.mpr ⟨projectedWorldTag chi g (b z.1),
        mem_iUnion.mpr ⟨hQ z.1 hz, ⟨hz, rfl⟩, hzt⟩⟩
  have hsum (F : Finset (Fin 4 → ℤ)) :
      (∑ u ∈ F, (ζ (E u)).toReal) = (ζ (⋃ u ∈ F, E u)).toReal := by
    rw [hunion, ENNReal.toReal_sum (by intro u hu; exact measure_ne_top _ _)]
  have hpriorSum : ∑ u ∈ Q, (ν (A u)).toReal ≤ 1 := by
    have hh := sum_projected_crop_prior_le_one ν hC b hb chi g Q
    have hh' : ∑ u ∈ Q, ν (A u) ≤ 1 := by
      rw [← Finset.sum_coe_sort]
      exact hh
    have hreal := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) hh'
    rw [ENNReal.toReal_sum (by intro u hu; exact measure_ne_top _ _)] at hreal
    simpa only [ENNReal.toReal_one] using hreal
  have hmass (u : Fin 4 → ℤ) : (ζ (E u)).toReal ≤ K * (ν (A u)).toReal := by
    have hh : ζ (E u) ≤ ENNReal.ofReal K * ν (A u) := by
      calc
        _ ≤ μ (E u) := hζ _
        _ ≤ (ENNReal.ofReal K • ν.prod volume) (E u) := hdom _
        _ = _ := by
          simp only [E, Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
            Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
    have hh' := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal K * ν (A u) ≠ ⊤) hh
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using hh'
  obtain ⟨G, hG, hgood, hmassGood⟩ := finite_groups_by_reference Q
    (fun u => (ν (A u)).toReal) (fun u => (ζ (E u)).toReal) cost hK hH hd
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg) hcost
    (fun u _ => hmass u) hpriorSum hbudget
  let S := ⋃ u ∈ G, E u
  have hS : MeasurableSet S := MeasurableSet.biUnion (Finset.countable_toSet G) (fun u _ => hE u)
  let ζ₁ := ζ.restrict S
  have hζ₁ : ζ₁ ≤ ζ := Measure.restrict_le_self
  have hζ₁mass : (ζ₁ univ).toReal = ∑ u ∈ G, (ζ (E u)).toReal := by
    change ((ζ.restrict S) univ).toReal = _
    rw [Measure.restrict_apply_univ]
    exact (hsum G).symm
  have hζ₁E (u : Fin 4 → ℤ) (hu : u ∈ G) : ζ₁ (E u) = ζ (E u) := by
    change (ζ.restrict S) (E u) = ζ (E u)
    rw [Measure.restrict_apply (hE u), inter_eq_left.mpr]
    exact fun z hz => mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨hu, hz⟩⟩
  refine ⟨G, ζ₁, hG, hζ₁, ?_, ?_, ?_, ?_⟩
  · rw [hζ₁mass, ← htotal, ← hsum]
    exact hmassGood
  · filter_upwards [ae_restrict_mem hS] with z hz
    obtain ⟨u, hu⟩ := mem_iUnion.mp hz
    obtain ⟨huG, hzE⟩ := mem_iUnion.mp hu
    exact ⟨u, huG, hzE.1⟩
  · rw [hζ₁mass, Finset.mul_sum]
    exact Finset.sum_le_sum (fun u _ => hmass u)
  · intro u hu
    have hh := hgood u hu
    refine ⟨?_, hh.2.1, ?_⟩
    · intro hz
      have hr0 : (ν (A u)).toReal = 0 := by rw [hz, ENNReal.toReal_zero]
      linarith [hh.1]
    · rw [hζ₁E u hu]
      exact hh.2.2

end

end Submission.Obl.k4_general_parent_projected_layers
