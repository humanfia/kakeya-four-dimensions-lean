import Submission.Obl.k4_critical_conditional_row_preparation.NativeNormalization
import Submission.Obl.k4_critical_conditional_row_preparation.Pruning
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal

namespace Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace Data
variable {α : Type} [MeasurableSpace α] {cfg : Data α}

def parentWeight (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : ℝ :=
  cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i)

/-- The budget uses the original full assignments at their actual time depth. -/
theorem AssignmentLevel.parent_weight_budget (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) : ∑ i, cfg.parentWeight k s i ≤ 1 := by
  classical
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hh := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget
    (fun (_ : Unit) => cfg.ν k) (fun _ => (1 : ℝ≥0∞))
    (fun (_ : Fin (cfg.n k s)) => ()) (cfg.j k s) (cfg.A k s)
    (fun _ => measure_univ) (by simp) a.measurable
    (fun i i' hne _ heq => a.disjoint i i' hne heq)
  simp only [one_mul, Fintype.card_fin] at hh
  have hsum : ∑ i, (cfg.ν k).real (cfg.A k s i) ≤ ((2 ^ cfg.T k s : ℕ) : ℝ) := by
    have hr := ENNReal.toReal_mono (by simp) hh
    rw [ENNReal.toReal_sum (by intro i hi; exact measure_ne_top (cfg.ν k) (cfg.A k s i)),
      ENNReal.toReal_natCast] at hr
    exact hr
  calc
    _ = cfg.timeLength k s * ∑ i, (cfg.ν k).real (cfg.A k s i) := by
      simp only [parentWeight, Finset.mul_sum]
    _ ≤ cfg.timeLength k s * ((2 ^ cfg.T k s : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (by unfold timeLength; positivity)
    _ = 1 := by simp [timeLength]

def halfBlock (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : Set ℝ :=
  Ico (cfg.leftTime k s i) (cfg.leftTime k s i + cfg.timeLength k s)

def halfEvent (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : Set (α × ℝ) :=
  cfg.B k s i ×ˢ cfg.halfBlock k s i

theorem halfEvent_subset (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    cfg.halfEvent k s i ⊆ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i) := by
  rw [cfg.true_block_eq]
  exact Set.prod_mono (subset_refl _) Ico_subset_Icc_self

theorem AssignmentLevel.measurableSet_halfEvent {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    MeasurableSet (cfg.halfEvent k s i) :=
  (a.fitted_measurable i).prod measurableSet_Ico

theorem AssignmentLevel.disjoint_halfEvents {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) :
    Pairwise (fun i j => Disjoint (cfg.halfEvent k s i) (cfg.halfEvent k s j)) := by
  have hd := Submission.Obl.k4_quadratic_finite_greedy_cover.halfOpen_packets_disjoint
    (cfg.B k s) (fun i => (cfg.j k s i : ℕ)) ((2 : ℝ) ^ cfg.T k s) (by positivity)
    (fun i i' hne heq => (a.disjoint i i' hne (Fin.ext heq)).mono
      (a.fitted_subset i) (a.fitted_subset i'))
  have heq : ∀ i, cfg.halfEvent k s i = cfg.B k s i ×ˢ
      Ico (((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s)
        ((((cfg.j k s i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ cfg.T k s) := by
    intro i
    unfold halfEvent halfBlock leftTime timeLength
    congr 2
    ring
  simpa only [heq] using hd

theorem Valid.time_slice_null (h : cfg.Valid) (k : ℕ) (t : ℝ) :
    cfg.μ k (univ ×ˢ {t}) = 0 := by
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  apply le_antisymm _ bot_le
  calc
    _ ≤ (ENNReal.ofReal (cfg.K k) • ((cfg.ν k).prod volume)) (univ ×ˢ {t}) :=
      (h.basic k).2.2.2.1 _
    _ = 0 := by simp [Measure.smul_apply, Measure.prod_prod]

/-- Closing time endpoints changes none of the original incidence measures. -/
theorem AssignmentLevel.closed_ae_half (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) =ᵐ[cfg.μ k] cfg.halfEvent k s i := by
  have ht : ∀ᵐ p ∂cfg.μ k, p.2 ≠ cfg.leftTime k s i + cfg.timeLength k s := by
    apply ae_iff.mpr
    simp only [not_not]
    convert h.time_slice_null k (cfg.leftTime k s i + cfg.timeLength k s) using 1
    congr 1
    ext p
    simp
  filter_upwards [ht] with p hp
  simp only [cfg.true_block_eq, halfEvent, halfBlock, mem_prod, mem_Icc, mem_Ico]
  apply propext
  constructor
  · rintro ⟨hl, hlo, hhi⟩
    exact ⟨hl, hlo, lt_of_le_of_ne hhi hp⟩
  · rintro ⟨hl, hlo, hhi⟩
    exact ⟨hl, hlo, hhi.le⟩

theorem AssignmentLevel.half_covers (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) : ∀ᵐ p ∂cfg.μ k, ∃ i, p ∈ cfg.halfEvent k s i := by
  have hh : ∀ᵐ p ∂cfg.μ k, ∀ i, (p ∈ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) ↔
      p ∈ cfg.halfEvent k s i := ae_all_iff.mpr (fun i => (a.closed_ae_half h i).mono (fun _ heq => Iff.of_eq heq))
  filter_upwards [a.covers, hh] with p hp heq
  obtain ⟨i, hi⟩ := hp
  exact ⟨i, (heq i).mp hi⟩

/-- Nesting of closed nondegenerate blocks also gives nesting of half-open blocks. -/
theorem halfBlock_subset_of_closed {k : ℕ} {s t : ℝ}
    (i : Fin (cfg.n k s)) (j : Fin (cfg.n k t))
    (hsub : I (cfg.T k t) (cfg.j k t j) ⊆ I (cfg.T k s) (cfg.j k s i)) :
    cfg.halfBlock k t j ⊆ cfg.halfBlock k s i := by
  rw [cfg.true_block_eq, cfg.true_block_eq] at hsub
  have hH : 0 < cfg.timeLength k t := by unfold timeLength; positivity
  have hh := (Icc_subset_Icc_iff (by linarith : cfg.leftTime k t j ≤
    cfg.leftTime k t j + cfg.timeLength k t)).mp hsub
  exact Ico_subset_Ico hh.1 hh.2

/-- The whole nested assignment determines the coarse fitted label a.e. -/
theorem AssignmentLevel.deep_parent_ae (h : cfg.Valid) {k : ℕ} {s t : ℝ}
    (a : cfg.AssignmentLevel k s) (deep : cfg.AssignmentLevel k t)
    (parent : Fin (cfg.n k t) → Fin (cfg.n k s))
    (hA : ∀ j, cfg.A k t j ⊆ cfg.A k s (parent j))
    (hI : ∀ j, I (cfg.T k t) (cfg.j k t j) ⊆ I (cfg.T k s) (cfg.j k s (parent j))) :
    ∀ᵐ p ∂cfg.μ k, ∀ j, p ∈ cfg.halfEvent k t j →
      p ∈ cfg.halfEvent k s (parent j) := by
  have hd := a.disjoint_halfEvents
  have hdA := Submission.Obl.k4_quadratic_finite_greedy_cover.halfOpen_packets_disjoint
    (cfg.A k s) (fun i => (cfg.j k s i : ℕ)) ((2 : ℝ) ^ cfg.T k s) (by positivity)
    (fun i i' hne heq => a.disjoint i i' hne (Fin.ext heq))
  filter_upwards [a.half_covers h] with p hp
  intro j hj
  obtain ⟨i, hi⟩ := hp
  have hjA : p.1 ∈ cfg.A k s (parent j) := hA j (deep.fitted_subset j hj.1)
  have hjT : p.2 ∈ cfg.halfBlock k s (parent j) := halfBlock_subset_of_closed (parent j) j (hI j) hj.2
  have hiA : p.1 ∈ cfg.A k s i := a.fitted_subset i hi.1
  have heq : parent j = i := by
    by_contra hne
    have hdis := Set.disjoint_left.mp (hdA hne)
    apply hdis (a := p)
    · simpa only [mem_prod, mem_Ico, halfBlock, leftTime, timeLength,
        div_eq_mul_inv, add_mul, one_mul] using (show p.1 ∈ cfg.A k s (parent j) ∧
          p.2 ∈ cfg.halfBlock k s (parent j) from ⟨hjA, hjT⟩)
    · simpa only [mem_prod, mem_Ico, halfBlock, leftTime, timeLength,
        div_eq_mul_inv, add_mul, one_mul] using (show p.1 ∈ cfg.A k s i ∧
          p.2 ∈ cfg.halfBlock k s i from ⟨hiA, hi.2⟩)
  simpa only [heq] using hi

end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
