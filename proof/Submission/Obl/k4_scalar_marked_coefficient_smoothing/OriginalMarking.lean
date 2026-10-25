import Submission.Obl.k4_scalar_marked_coefficient_smoothing.MarkedMass
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.FiniteMarking

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open MeasureTheory Set
open scoped ENNReal

def originalCell {α : Type} {H J : ℕ} (tag : α → Fin H) (j : Fin H) (z : Fin J) :
    Set (α × ℝ) := {p | tag p.1 = j ∧ p.2 ∈ timeCell J z}

theorem original_time_support {α : Type} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ)) {K : ℝ}
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) :
    μ (univ ×ˢ Ico (0 : ℝ) 1) = μ univ ∧ μ univ ≤ ENNReal.ofReal K := by
  have hnull : μ (univ ×ˢ ({1} : Set ℝ)) = 0 := by
    apply le_antisymm _ bot_le
    calc
      _ ≤ (ENNReal.ofReal K • (ν.prod volume)) (univ ×ˢ ({1} : Set ℝ)) := hdom _
      _ = 0 := by rw [Measure.smul_apply, Measure.prod_prod]; simp
  have hcompl : μ (univ ×ˢ Ico (0 : ℝ) 1)ᶜ = 0 := by
    apply measure_mono_null _ (measure_union_null hsupp hnull)
    intro p hp
    by_cases ht : p.2 ∈ Icc (0 : ℝ) 1
    · right
      have ht1 : p.2 = 1 := by
        have hnot : ¬ p.2 < 1 := fun h => hp ⟨mem_univ _, ht.1, h⟩
        exact le_antisymm ht.2 (le_of_not_gt hnot)
      exact ⟨mem_univ _, ht1⟩
    · exact Or.inl (fun h => ht h.2)
  have heq : μ (univ ×ˢ Ico (0 : ℝ) 1) = μ univ := by
    simpa only [hcompl, add_zero] using
      (measure_add_measure_compl (μ := μ) (s := univ ×ˢ Ico (0 : ℝ) 1)
        (MeasurableSet.univ.prod measurableSet_Ico))
  refine ⟨heq, ?_⟩
  rw [← heq]
  calc
    _ ≤ (ENNReal.ofReal K • (ν.prod volume)) (univ ×ˢ Ico (0 : ℝ) 1) := hdom _
    _ = ENNReal.ofReal K := by
      rw [Measure.smul_apply, Measure.prod_prod]
      simp

theorem sum_original_cells {α : Type} [MeasurableSpace α] (μ : Measure (α × ℝ))
    {H J : ℕ} (hJ : 0 < J) (tag : α → Fin H) (htag : Measurable tag) :
    (∑ q : Fin H × Fin J, μ (originalCell tag q.1 q.2)) =
      μ (univ ×ˢ Ico (0 : ℝ) 1) := by
  classical
  have hunion : (⋃ q : Fin H × Fin J, originalCell tag q.1 q.2) =
      univ ×ˢ Ico (0 : ℝ) 1 := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq⟩ := mem_iUnion.mp hp
      exact ⟨mem_univ _, timeCell_subset hJ q.2 hq.2⟩
    · intro hp
      have ht : p.2 ∈ ⋃ z : Fin J, timeCell J z := by rw [iUnion_timeCell hJ]; exact hp.2
      obtain ⟨z, hz⟩ := mem_iUnion.mp ht
      exact mem_iUnion.mpr ⟨(tag p.1, z), rfl, hz⟩
  have hdisj : Pairwise (fun q q' : Fin H × Fin J =>
      Disjoint (originalCell tag q.1 q.2) (originalCell tag q'.1 q'.2)) := by
    intro q q' hne
    rw [Set.disjoint_left]
    intro p hp hp'
    have hj : q.1 = q'.1 := hp.1.symm.trans hp'.1
    have hz : q.2 ≠ q'.2 := fun hz => hne (Prod.ext hj hz)
    exact Set.disjoint_left.mp (timeCell_disjoint hJ hz) hp.2 hp'.2
  have hmeas (q : Fin H × Fin J) : MeasurableSet (originalCell tag q.1 q.2) := by
    exact ((measurableSet_singleton q.1).preimage (htag.comp measurable_fst)).inter
      ((measurableSet_timeCell J q.2).preimage measurable_snd)
  calc
    _ = ∑' q : Fin H × Fin J, μ (originalCell tag q.1 q.2) := (tsum_fintype _).symm
    _ = μ (⋃ q : Fin H × Fin J, originalCell tag q.1 q.2) :=
      (measure_iUnion hdisj hmeas).symm
    _ = _ := congrArg μ hunion

/-- Original mass domination and exact tag weights give a marked table with a true
mass floor in every marked original cell and a quantitative noisy mass lower bound. -/
theorem exists_original_marking {α : Type} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ))
    {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hlower : ENNReal.ofReal (K⁻¹) ≤ μ univ)
    {H J : ℕ} (hJ : 0 < J) (tag : α → Fin H) (htag : Measurable tag)
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hsum : (∑ j, w j) = 1)
    (hweight : ∀ j, ENNReal.ofReal (w j) = ν {l | tag l = j}) :
    ∃ mark : Fin H → Fin J → Bool,
      (∀ j z, mark j z = true →
        ENNReal.ofReal (w j / ((J : ℝ) * (2 * K))) ≤ μ (originalCell tag j z)) ∧
      ENNReal.ofReal (1 / (2 * K ^ 2)) ≤ MarkedLaw σ H J b₀ w mark univ := by
  classical
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsupport := original_time_support ν μ hdom hsupp
  have : IsFiniteMeasure μ := ⟨lt_of_le_of_lt hsupport.2 ENNReal.ofReal_lt_top⟩
  let v : Fin H × Fin J → ℝ := fun q => w q.1 / (J : ℝ)
  let a : Fin H × Fin J → ℝ := fun q => (μ (originalCell tag q.1 q.2)).toReal
  have hv (q : Fin H × Fin J) : 0 ≤ v q := div_nonneg (hw _) hJr.le
  have hvsum : (∑ q, v q) = 1 := by
    rw [Fintype.sum_prod_type]
    change (∑ j : Fin H, ∑ z : Fin J, w j / (J : ℝ)) = 1
    calc
      _ = ∑ j : Fin H, w j := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      _ = 1 := hsum
  have hcap (q : Fin H × Fin J) : a q ≤ K * v q := by
    have hbound : μ (originalCell tag q.1 q.2) ≤ ENNReal.ofReal (K * v q) := by
      calc
        _ ≤ (ENNReal.ofReal K • (ν.prod volume)) (originalCell tag q.1 q.2) := hdom _
        _ = ENNReal.ofReal (K * v q) := by
          change (ENNReal.ofReal K • (ν.prod volume))
            ({l | tag l = q.1} ×ˢ timeCell J q.2) = _
          rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
            ← hweight q.1, volume_timeCell hJ, ← ENNReal.ofReal_mul (hw q.1),
            ← ENNReal.ofReal_mul hK.le]
          congr 1
          dsimp [v]
          ring
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa [a, ENNReal.toReal_ofReal (mul_nonneg hK.le (hv q))] using h
  have hlow : K⁻¹ ≤ ∑ q, a q := by
    have h := ENNReal.toReal_mono (measure_ne_top μ _) hlower
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hK.le)] at h
    rw [← ENNReal.toReal_sum (fun q _ => measure_ne_top μ _),
      sum_original_cells μ hJ tag htag, hsupport.1]
    exact h
  obtain ⟨mark₁, hfloor, hmass⟩ := select_marked_mass hK v a hv hvsum hcap hlow
  let mark : Fin H → Fin J → Bool := fun j z => mark₁ (j, z)
  refine ⟨mark, ?_, ?_⟩
  · intro j z hz
    have h := ENNReal.ofReal_le_ofReal (hfloor (j, z) hz)
    rw [show v (j, z) / (2 * K) = w j / ((J : ℝ) * (2 * K)) by dsimp [v]; ring] at h
    exact h.trans_eq (ENNReal.ofReal_toReal (measure_ne_top μ _))
  · rw [markedLaw_total_mass hσ hJ b₀ w hw mark]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Fintype.sum_prod_type, v, mark] using hmass

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
