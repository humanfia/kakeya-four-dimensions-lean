import Submission.Obl.k4_general_wide_layer_offset_comparison.Model

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/OriginalBudgets.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- Arbitrary original trajectory spaces have one prior budget per time
block, provided the assignments in that block are disjoint. -/
theorem assignment_prior_budget {α ι κ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ν : Measure α) [IsProbabilityMeasure ν] (block : ι → κ) (A : ι → Set α)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i j, i ≠ j → block i = block j → Disjoint (A i) (A j)) :
    (∑ i, ν (A i)) ≤ Fintype.card κ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ block]
  calc
    (∑ q, ∑ i ∈ Finset.univ.filter (fun i => block i = q), ν (A i)) ≤
        ∑ _q : κ, (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro q _
      rw [← measure_biUnion_finset]
      · exact prob_le_one
      · intro i hi j hj hij
        have hiq : block i = q := (Finset.mem_filter.mp hi).2
        have hjq : block j = q := (Finset.mem_filter.mp hj).2
        exact hdisj i j hij (hiq.trans hjq.symm)
      · intro i _
        exact hA i
    _ = _ := by simp

/-- A finite original-reference budget selects a heavy entry without a
loss depending on the number of entries. -/
theorem exists_heavy_original_entry {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (σ : Measure Ω) (E : ι → Set Ω)
    (w : ι → ℝ≥0∞) {δ : ℝ≥0∞} (hbudget : (∑ i, w i) ≤ 1)
    (hcover : ∀ᵐ ω ∂σ, ∃ i, ω ∈ E i) (hmass : δ < σ univ) :
    ∃ i, δ * w i ≤ σ (E i) := by
  classical
  by_contra! hsmall
  have hcover' : σ univ ≤ σ (⋃ i, E i) := by
    apply measure_mono_ae
    filter_upwards [hcover] with ω hω
    exact fun _ => mem_iUnion.mpr hω
  have hsum : σ univ ≤ ∑ i, σ (E i) := hcover'.trans (measure_iUnion_fintype_le _ _)
  have hlt : (∑ i, σ (E i)) < ∑ i, δ * w i :=
    ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hsmall i)
  have hupper : (∑ i, δ * w i) ≤ δ := by
    rw [← Finset.mul_sum]
    simpa only [mul_one, one_mul, mul_comm] using mul_le_mul_left hbudget δ
  exact (not_lt_of_ge (hlt.le.trans hupper)) (hmass.trans_le hsum)

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The true packet reference is its full original assignment prior times
the actual dyadic time length. -/
def referenceWeight (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 : ℝ) ^ p.T k s)⁻¹) * p.ν k (p.A k s i)

theorem AtDepth.reference_budget (hbase : p.Basic) {k : ℕ} {s R : ℝ}
    (hat : p.AtDepth k s R) : (∑ i, p.referenceWeight k s i) ≤ 1 := by
  letI := (hbase k).2.1
  have hbudget := assignment_prior_budget (p.ν k) (p.j k s) (p.A k s)
    (fun i => (hat.2.2.1 i).1) hat.2.2.2.1
  simp only [referenceWeight]
  rw [← Finset.mul_sum]
  calc
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ p.T k s)⁻¹) * (2 ^ p.T k s : ℕ) := by
      gcongr
      simpa only [Fintype.card_fin] using hbudget
    _ = 1 := by
      have hpow : 0 < (2 : ℝ) ^ p.T k s := by positivity
      rw [← ENNReal.ofReal_natCast, Nat.cast_pow, Nat.cast_ofNat,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hpow.le), inv_mul_cancel₀ hpow.ne', ENNReal.ofReal_one]

/-- Summing the original true assignment ceilings gives a global palette
ceiling. In particular a zero original palette bin carries no current mass. -/
theorem AtDepth.global_palette_bin (hbase : p.Basic) {k : ℕ} {s R v : ℝ}
    (hat : p.AtDepth k s R) (hK : 0 ≤ p.K k)
    (hvlo : R⁻¹ ≤ v) (hvhi : v ≤ R) (v₀ : ℤ) :
    p.μ k {ω | ⌊p.b k ω.1 3 / (p.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (p.K k) * p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀} := by
  let q := (2 : ℝ) ^ (-(p.T k s : ℤ))
  have hbudget := AtDepth.reference_budget p hbase hat
  have hcover := hat.2.2.2.2.2.1
  have hpal := hat.2.2.2.2.2.2
  let E (i : Fin (p.n k s)) : Set (α × ℝ) :=
    {ω | ω.1 ∈ p.B k s i ∧ ω.2 ∈ block (p.T k s) (p.j k s i) ∧
      ⌊p.b k ω.1 3 / (p.N k ^ (-v))⌋ = v₀}
  have hsub : {ω | ⌊p.b k ω.1 3 / (p.N k ^ (-v))⌋ = v₀} ≤ᵐ[p.μ k] ⋃ i, E i := by
    filter_upwards [hcover] with ω hω
    intro hv
    obtain ⟨i, hi, ht⟩ := hω
    exact mem_iUnion.mpr ⟨i, hi, ht, hv⟩
  have hfactor (i : Fin (p.n k s)) :
      ENNReal.ofReal (p.K k * q) * p.ν k (p.A k s i) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀} =
      ENNReal.ofReal (p.K k) * p.referenceWeight k s i *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀} := by
    dsimp [q, referenceWeight]
    rw [ENNReal.ofReal_mul hK]
    simp only [zpow_neg, zpow_natCast]
    ring
  calc
    _ ≤ p.μ k (⋃ i, E i) := measure_mono_ae hsub
    _ ≤ ∑ i, p.μ k (E i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal (p.K k * q) * p.ν k (p.A k s i) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀} :=
      Finset.sum_le_sum (fun i _ => hpal i v v₀ hvlo hvhi)
    _ = ENNReal.ofReal (p.K k) * (∑ i, p.referenceWeight k s i) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀} := by
      simp_rw [hfactor]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ ENNReal.ofReal (p.K k) * 1 * p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀} := by
      gcongr
    _ = _ := by rw [mul_one]

theorem AtDepth.palette_null_source (hbase : p.Basic) {k : ℕ} {s R v : ℝ}
    (hat : p.AtDepth k s R) (hK : 0 ≤ p.K k)
    (hvlo : R⁻¹ ≤ v) (hvhi : v ≤ R) (v₀ : ℤ)
    (hzero : p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀} = 0)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.μ k) (E : Set (α × ℝ))
    (hE : ∀ ω ∈ E, ⌊p.b k ω.1 3 / (p.N k ^ (-v))⌋ = v₀) : σ E = 0 := by
  have h := AtDepth.global_palette_bin p hbase hat hK hvlo hvhi v₀
  rw [hzero, mul_zero] at h
  exact le_antisymm ((hσ E).trans ((measure_mono hE).trans h)) bot_le

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
