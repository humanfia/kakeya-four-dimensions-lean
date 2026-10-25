import Submission.Obl.k4_scalar_marked_coefficient_smoothing.RawNoise

/-!
# The marked law, tag by tag

`MarkedLaw σ H J b₀ w mark` puts, on tag `j`, the weight `w j` times the law of
`(b₀ j + noise, t)` with `t` Lebesgue on the marked times of `j`.  `MarkedLaw_apply` writes
the mass of a measurable set this way.
-/

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw

open MeasureTheory Set
open scoped ENNReal

/-- The marked times of tag `j`: the union of its marked time cells. -/
def markTimes {H J : ℕ} (mark : Fin H → Fin J → Bool) (j : Fin H) : Set ℝ :=
  {t | ∃ z : Fin J, mark j z = true ∧ t ∈ timeCell J z}

theorem measurableSet_timeCell (J : ℕ) (z : Fin J) : MeasurableSet (timeCell J z) :=
  measurableSet_Ico

theorem measurableSet_markTimes {H J : ℕ} (mark : Fin H → Fin J → Bool) (j : Fin H) :
    MeasurableSet (markTimes mark j) := by
  have : markTimes mark j = ⋃ z : Fin J, ⋃ (_ : mark j z = true), timeCell J z := by
    ext t; simp [markTimes]
  rw [this]
  exact MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun _ => measurableSet_timeCell J z

/-- A time cell lies in `[0, 1)`. -/
theorem timeCell_subset {J : ℕ} (z : Fin J) : timeCell J z ⊆ Ico 0 1 := by
  intro t ht
  have hJ : (0 : ℝ) < J := by exact_mod_cast (Nat.zero_lt_of_lt z.isLt)
  have hz : (z : ℝ) + 1 ≤ J := by exact_mod_cast z.isLt
  obtain ⟨h1, h2⟩ := ht
  refine ⟨le_trans (by positivity) h1, lt_of_lt_of_le h2 ?_⟩
  rw [div_le_one hJ]
  exact hz

theorem markTimes_subset {H J : ℕ} (mark : Fin H → Fin J → Bool) (j : Fin H) :
    markTimes mark j ⊆ Ico 0 1 := by
  rintro t ⟨z, -, hz⟩
  exact timeCell_subset z hz

/-- Two times in one cell are less than `1/J` apart. -/
theorem abs_sub_lt_of_mem_timeCell {J : ℕ} {z : Fin J} {t t' : ℝ} (ht : t ∈ timeCell J z)
    (ht' : t' ∈ timeCell J z) : |t - t'| < 1 / (J : ℝ) := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast (Nat.zero_lt_of_lt z.isLt)
  obtain ⟨h1, h2⟩ := ht
  obtain ⟨h1', h2'⟩ := ht'
  have e : ((z : ℝ) + 1) / J = z / J + 1 / J := by ring
  rw [e] at h2 h2'
  rw [abs_lt]
  constructor <;> linarith

theorem measurableSet_MarkedEvent (H J : ℕ) (mark : Fin H → Fin J → Bool) :
    MeasurableSet (MarkedEvent H J mark) := by
  have : MarkedEvent H J mark = ⋃ j : Fin H, ⋃ z : Fin J, ⋃ (_ : mark j z = true),
      ({p : Traj × ℝ | p.1.1 = (j : ℕ)} ∩ {p | p.2 ∈ timeCell J z}) := by
    ext p
    simp only [MarkedEvent, mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨j, hj, z, hz, ht⟩; exact ⟨j, z, hz, hj, ht⟩
    · rintro ⟨j, z, hz, hj, ht⟩; exact ⟨j, hj, z, hz, ht⟩
  rw [this]
  refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun z =>
    MeasurableSet.iUnion fun _ => ?_
  exact ((measurableSet_singleton _).preimage (measurable_fst.comp measurable_fst)).inter
    ((measurableSet_timeCell J z).preimage measurable_snd)

theorem mem_MarkedEvent_iff {H J : ℕ} (mark : Fin H → Fin J → Bool) (j : Fin H)
    (β : Coeff) (t : ℝ) :
    ((((j : ℕ), β), t) : Traj × ℝ) ∈ MarkedEvent H J mark ↔ t ∈ markTimes mark j := by
  simp only [MarkedEvent, markTimes, mem_ofPred_eq]
  constructor
  · rintro ⟨j', hj', z, hz, ht⟩
    have : j = j' := Fin.ext hj'
    subst this
    exact ⟨z, hz, ht⟩
  · rintro ⟨z, hz, ht⟩
    exact ⟨j, rfl, z, hz, ht⟩

theorem measurable_tagEmbed {H : ℕ} (b₀ : Fin H → Coeff) (j : Fin H) :
    Measurable (fun u : Coeff => (((j : ℕ), b₀ j + u) : Traj)) := by
  fun_prop

theorem MarkedPrior_apply (σ : ℝ) {H : ℕ} (b₀ : Fin H → Coeff) (w : Fin H → ℝ)
    {X : Set Traj} (hX : MeasurableSet X) :
    MarkedPrior σ H b₀ w X =
      ∑ j, ENNReal.ofReal (w j) * Noise σ {u | (((j : ℕ), b₀ j + u) : Traj) ∈ X} := by
  rw [MarkedPrior, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_tagEmbed b₀ j) hX]
  rfl

theorem isFiniteMeasure_MarkedPrior {σ : ℝ} (hσ : 0 < σ) {H : ℕ} (b₀ : Fin H → Coeff)
    (w : Fin H → ℝ) : IsFiniteMeasure (MarkedPrior σ H b₀ w) := by
  have := isProbabilityMeasure_Noise hσ
  constructor
  rw [MarkedPrior_apply σ b₀ w MeasurableSet.univ]
  exact ENNReal.sum_lt_top.mpr fun j _ =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- **The marked law tag by tag.** -/
theorem MarkedLaw_apply {σ : ℝ} (hσ : 0 < σ) {H J : ℕ} (b₀ : Fin H → Coeff) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) {A : Set (Traj × ℝ)} (hA : MeasurableSet A) :
    MarkedLaw σ H J b₀ w mark A = ∑ j, ENNReal.ofReal (w j) *
      ∫⁻ t, (markTimes mark j).indicator
        (fun t => Noise σ {u | ((((j : ℕ), b₀ j + u), t) : Traj × ℝ) ∈ A}) t := by
  have := isFiniteMeasure_MarkedPrior hσ b₀ w
  have := isProbabilityMeasure_Noise hσ
  have hE := measurableSet_MarkedEvent H J mark
  rw [MarkedLaw, Measure.restrict_apply hA, Measure.prod_apply_symm (hA.inter hE)]
  have hslice : ∀ t : ℝ,
      MarkedPrior σ H b₀ w ((fun x => (x, t)) ⁻¹' (A ∩ MarkedEvent H J mark)) =
        ∑ j, ENNReal.ofReal (w j) * (markTimes mark j).indicator
          (fun t => Noise σ {u | ((((j : ℕ), b₀ j + u), t) : Traj × ℝ) ∈ A}) t := by
    intro t
    rw [MarkedPrior_apply σ b₀ w (measurable_prodMk_right (hA.inter hE))]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    by_cases ht : t ∈ markTimes mark j
    · rw [indicator_of_mem ht]
      congr 1
      ext u
      simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_MarkedEvent_iff, ht, and_true]
    · rw [indicator_of_notMem ht]
      convert measure_empty (μ := Noise σ)
      ext u
      simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_MarkedEvent_iff, ht, and_false,
        mem_empty_iff_false]
  simp_rw [hslice]
  have hmeas : ∀ j : Fin H, Measurable (fun t : ℝ =>
      Noise σ {u | ((((j : ℕ), b₀ j + u), t) : Traj × ℝ) ∈ A}) := by
    intro j
    have hS : MeasurableSet {q : Coeff × ℝ | ((((j : ℕ), b₀ j + q.1), q.2) : Traj × ℝ) ∈ A} :=
      hA.preimage (((measurable_tagEmbed b₀ j).comp measurable_fst).prodMk measurable_snd)
    exact measurable_measure_prodMk_right hS
  rw [lintegral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [lintegral_const_mul]
    exact (hmeas j).indicator (measurableSet_markTimes mark j)
  · intro j _
    exact ((hmeas j).indicator (measurableSet_markTimes mark j)).const_mul _

end Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw
