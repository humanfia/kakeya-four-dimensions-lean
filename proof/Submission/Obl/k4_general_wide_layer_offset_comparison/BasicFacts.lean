import Submission.Obl.k4_general_wide_layer_offset_comparison.Model

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/BasicFacts.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

theorem Basic.ae_unit (hbase : p.Basic) (k : ℕ) :
    ∀ᵐ ω ∂p.μ k, ω.2 ∈ Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  have heq : {ω : α × ℝ | ω.2 ∉ Icc (0 : ℝ) 1} = (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
    ext ω
    simp
  rw [heq]
  exact (hbase k).2.2.2.2.2.1

theorem Basic.ae_clipped (hbase : p.Basic) (k : ℕ) :
    ∀ᵐ ω ∂p.μ k,
      |p.b k ω.1 0| + |p.b k ω.1 1| + |p.b k ω.1 3| + |p.b k ω.1 4| ≤ p.K k := by
  have hclip := (hbase k).2.2.2.2.2.2.2.2.1
  have hprod := (Measure.quasiMeasurePreserving_fst (μ := p.ν k) (ν := (volume : Measure ℝ))).ae hclip
  exact (Measure.ae_smul_measure hprod (ENNReal.ofReal (p.K k))).filter_mono
    (ae_mono (hbase k).2.2.2.1)

theorem Basic.mass_le (hbase : p.Basic) (k : ℕ) :
    p.μ k univ ≤ ENNReal.ofReal (p.K k) := by
  letI := (hbase k).2.1
  have hunit : p.μ k (univ ×ˢ Icc (0 : ℝ) 1) = p.μ k univ := by
    apply measure_congr
    filter_upwards [Basic.ae_unit p hbase k] with ω ht
    simp only [mem_prod, mem_univ, true_and, ht]
  rw [← hunit]
  calc
    _ ≤ (ENNReal.ofReal (p.K k) • ((p.ν k).prod volume)) (univ ×ˢ Icc (0 : ℝ) 1) :=
      (hbase k).2.2.2.1 _
    _ = _ := by simp [Measure.smul_apply, Real.volume_Icc]

theorem Basic.finite_mu (hbase : p.Basic) (k : ℕ) : IsFiniteMeasure (p.μ k) :=
  ⟨(Basic.mass_le p hbase k).trans_lt ENNReal.ofReal_lt_top⟩

def baseGood (k : ℕ) : Set (α × ℝ) :=
  {ω | ω.2 ∈ Icc (0 : ℝ) 1 ∧
    |p.b k ω.1 0| + |p.b k ω.1 1| + |p.b k ω.1 3| + |p.b k ω.1 4| ≤ p.K k}

theorem Basic.measurableSet_baseGood (hbase : p.Basic) (k : ℕ) : MeasurableSet (p.baseGood k) := by
  have hb := (hbase k).1
  have hf : Measurable (fun ω : α × ℝ =>
      |p.b k ω.1 0| + |p.b k ω.1 1| + |p.b k ω.1 3| + |p.b k ω.1 4|) := by fun_prop
  exact (measurable_snd measurableSet_Icc).inter (measurableSet_le hf measurable_const)

theorem Basic.ae_baseGood (hbase : p.Basic) (k : ℕ) : ∀ᵐ ω ∂p.μ k, ω ∈ p.baseGood k :=
  (Basic.ae_unit p hbase k).and (Basic.ae_clipped p hbase k)

theorem baseGood_base_bound {k : ℕ} (hK : 1 ≤ p.K k) {ω : α × ℝ} (hω : ω ∈ p.baseGood k) :
    ∀ i : Fin 3, |(p.x k ω.1 ω.2) i.castSucc| ≤ p.K k := by
  obtain ⟨ht, hclip⟩ := hω
  have ht' : |ω.2| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  intro i
  fin_cases i
  · exact ht'.trans hK
  · change |p.b k ω.1 0 + ω.2 * p.b k ω.1 3| ≤ p.K k
    calc
      _ ≤ |p.b k ω.1 0| + |ω.2| * |p.b k ω.1 3| := by simpa only [abs_mul] using abs_add_le (p.b k ω.1 0) (ω.2 * p.b k ω.1 3)
      _ ≤ |p.b k ω.1 0| + 1 * |p.b k ω.1 3| := by gcongr
      _ ≤ _ := by linarith [abs_nonneg (p.b k ω.1 1), abs_nonneg (p.b k ω.1 4)]
  · change |p.b k ω.1 1 + ω.2 * p.b k ω.1 4| ≤ p.K k
    calc
      _ ≤ |p.b k ω.1 1| + |ω.2| * |p.b k ω.1 4| := by simpa only [abs_mul] using abs_add_le (p.b k ω.1 1) (ω.2 * p.b k ω.1 4)
      _ ≤ |p.b k ω.1 1| + 1 * |p.b k ω.1 4| := by gcongr
      _ ≤ _ := by linarith [abs_nonneg (p.b k ω.1 0), abs_nonneg (p.b k ω.1 3)]

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
