import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_matching_gap_regularization

open MeasureTheory Set
open scoped ENNReal

/-- A finite almost-everywhere cover of a probability space has a cell on
which conditioning costs at most the number of cells. -/
lemma finite_cover_restriction {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [Nonempty ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : ι → Set α) (hS : ∀ i, MeasurableSet (S i))
    (hcover : ∀ᵐ x ∂μ, ∃ i, x ∈ S i) :
    ∃ (i : ι) (ν : Measure α), IsProbabilityMeasure ν ∧
      (∀ E : Set α, ν E ≤ (Fintype.card ι : ℝ≥0∞) * μ E) ∧ ν (S i)ᶜ = 0 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => μ (S i))
    Finset.univ_nonempty
  have hmass : (1 : ℝ≥0∞) ≤ (Fintype.card ι : ℝ≥0∞) * μ (S i) := by
    calc
      1 = μ univ := (measure_univ (μ := μ)).symm
      _ ≤ μ (⋃ j, S j) := measure_mono_ae <| hcover.mono fun x hx _ => mem_iUnion.2 hx
      _ ≤ ∑ j, μ (S j) := measure_iUnion_fintype_le μ S
      _ ≤ ∑ _j : ι, μ (S i) := Finset.sum_le_sum fun j _ => hi j (Finset.mem_univ _)
      _ = (Fintype.card ι : ℝ≥0∞) * μ (S i) := by simp
  have hpos : μ (S i) ≠ 0 := by
    intro h
    simpa [h] using hmass
  have hfinite : μ (S i) ≠ ∞ := measure_ne_top _ _
  have hinv : (μ (S i))⁻¹ ≤ (Fintype.card ι : ℝ≥0∞) := by
    rw [← one_div, ENNReal.div_le_iff hpos hfinite]
    exact hmass
  let ν : Measure α := (μ (S i))⁻¹ • μ.restrict (S i)
  have hprob : IsProbabilityMeasure ν := by
    constructor
    simp only [ν, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hpos hfinite
  refine ⟨i, ν, hprob, ?_, ?_⟩
  · intro E
    exact (mul_le_mul' hinv (Measure.restrict_apply_le _ _)).trans_eq (by rfl)
  · simp only [ν, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' (hS i),
      compl_inter_self, measure_empty, mul_zero]

/-- Domination by a scalar multiple preserves every null set. -/
lemma null_of_bounded {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    {C : ℝ≥0∞} (h : ∀ E : Set α, ν E ≤ C * μ E) {E : Set α} (hE : μ E = 0) :
    ν E = 0 := by
  apply le_antisymm _ bot_le
  simpa [hE] using h E

/-- A cell of inverse-power mass can be normalized at the opposite power
cost. The estimate holds for every event, with no measurability requirement
on that event. -/
lemma normalize_restrict_power {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {S : Set α} (hS : MeasurableSet S)
    {N a : ℝ} (hN : 0 < N) (hmass : ENNReal.ofReal (N ^ (-a)) ≤ μ S) :
    IsProbabilityMeasure ((μ S)⁻¹ • μ.restrict S) ∧
      (∀ E : Set α, ((μ S)⁻¹ • μ.restrict S) E ≤ ENNReal.ofReal (N ^ a) * μ E) ∧
      ((μ S)⁻¹ • μ.restrict S) Sᶜ = 0 := by
  have hpos : μ S ≠ 0 := ne_of_gt <|
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hN (-a))).trans_le hmass
  have hfinite : μ S ≠ ∞ := measure_ne_top _ _
  have hcancel : ENNReal.ofReal (N ^ a) * ENNReal.ofReal (N ^ (-a)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le a), ← Real.rpow_add hN,
      add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one]
  have hinv : (μ S)⁻¹ ≤ ENNReal.ofReal (N ^ a) := by
    rw [← one_div, ENNReal.div_le_iff hpos hfinite]
    rw [← hcancel]
    exact mul_le_mul' le_rfl hmass
  refine ⟨?_, ?_, ?_⟩
  · constructor
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hpos hfinite
  · intro E
    exact mul_le_mul' hinv (Measure.restrict_apply_le _ _)
  · simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hS,
      compl_inter_self, measure_empty, mul_zero]

/-- Conditioning and the original marginal loss add in the exponent. -/
lemma marginal_power_loss {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    {N a η ε π : ℝ} (hN : 1 ≤ N) (hπ : 0 ≤ π) (hexp : a + η ≤ ε)
    (hν : ∀ E : Set α, ν E ≤ ENNReal.ofReal (N ^ a) * μ E)
    {E : Set α} {V : ℝ≥0∞}
    (hμ : μ E ≤ ENNReal.ofReal (N ^ η * π) * V) :
    ν E ≤ ENNReal.ofReal (N ^ ε * π) * V := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    ν E ≤ ENNReal.ofReal (N ^ a) * μ E := hν E
    _ ≤ ENNReal.ofReal (N ^ a) * (ENNReal.ofReal (N ^ η * π) * V) :=
      mul_le_mul' le_rfl hμ
    _ = ENNReal.ofReal (N ^ (a + η) * π) * V := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hNpos.le a),
        ← mul_assoc, ← Real.rpow_add hNpos]
    _ ≤ ENNReal.ofReal (N ^ ε * π) * V := by
      gcongr

end Submission.Obl.k4_matching_gap_regularization
