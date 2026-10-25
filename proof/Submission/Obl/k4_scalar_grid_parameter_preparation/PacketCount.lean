/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PacketCount.lean -/
import Submission.Lib.K4FinitePlankAtlases.DensityFloors

/-! Count saturated packets using their unchanged prior floors and block disjointness. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem finite_block_packet_count {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) [IsProbabilityMeasure ν] (q : ℕ) (block : ι → Fin q)
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → block i = block i' → Disjoint (A i) (A i'))
    (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ i, ENNReal.ofReal ε ≤ ν (A i)) :
    (Fintype.card ι : ℝ) ≤ (q : ℝ) / ε := by
  let I : Fin q → Finset ι := fun j => Finset.univ.filter fun i => block i = j
  have hIj (j : Fin q) : ((I j).card : ℝ) ≤ 1 / ε := by
    have hd : (I j : Set ι).PairwiseDisjoint A := by
      intro i hi i' hi' hne
      exact hdisj i i' hne ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hi').2.symm)
    have hm : ∀ i ∈ I j, ε ≤ ν.real (A i) := by
      intro i hi
      simpa only [measureReal_def, ENNReal.toReal_ofReal hε.le] using
        ENNReal.toReal_mono (measure_ne_top ν (A i)) (hfloor i)
    simpa using Submission.Lib.K4FinitePlankAtlases.old_cell_count ν (I j) A hd
      (fun i hi => hA i) hε hm
  have hcard : (Fintype.card ι : ℝ) = ∑ j : Fin q, ((I j).card : ℝ) := by
    have hn : (∑ j : Fin q, (I j).card) = Fintype.card ι := by
      simp only [I, Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
      simp
    exact_mod_cast hn.symm
  rw [hcard]
  calc
    _ ≤ ∑ _j : Fin q, (1 / ε) := Finset.sum_le_sum fun j hj => hIj j
    _ = _ := by simp; ring

theorem saturated_packet_count_le {X G : Type*} [MeasurableSpace X] [DecidableEq G]
    (ν : Measure X) [IsProbabilityMeasure ν] {n q : ℕ} (γ : Fin n → G) (block : Fin n → Fin q)
    (A : Fin n → Set X) (g : G) (K w : ℝ) (hK : 0 < K) (hw : 0 < w) (hq : 0 < q)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → block i = block i' → Disjoint (A i) (A i'))
    (hfloor : ∀ i, γ i = g → ENNReal.ofReal (w / (K * (q : ℝ))) ≤ ν (A i)) :
    ((Finset.univ.filter fun i => γ i = g).card : ℝ) ≤ K * (q : ℝ) ^ 2 / w := by
  let I := Finset.univ.filter fun i => γ i = g
  have hε : 0 < w / (K * (q : ℝ)) := by positivity
  have hm := finite_block_packet_count ν q (fun i : I => block i.val) (fun i : I => A i.val)
    (fun i => hA i.val) (fun i i' hne hb => hdisj i.val i'.val
      (by intro he; exact hne (Subtype.ext he))
      ((Finset.mem_filter.mp i.property).2.trans (Finset.mem_filter.mp i'.property).2.symm) hb)
    (w / (K * (q : ℝ))) hε (fun i => hfloor i.val (Finset.mem_filter.mp i.property).2)
  have he : (q : ℝ) / (w / (K * (q : ℝ))) = K * (q : ℝ) ^ 2 / w := by
    field_simp
  simpa only [Fintype.card_coe, he, I] using hm

/-- Summing packet exceptions cancels the original horizon and thickness factors.
The palette factor remains the same one used by every packet's original-law estimate. -/
theorem saturated_packet_exception_mass_le {X Ω G : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [DecidableEq G]
    (ν : Measure X) [IsProbabilityMeasure ν] (μ : Measure Ω) {n q : ℕ}
    (γ : Fin n → G) (block : Fin n → Fin q) (A : Fin n → Set X) (bad : Fin n → Set Ω)
    (g : G) (K w C : ℝ) (hK : 0 < K) (hw : 0 < w) (hC : 0 ≤ C) (hq : 0 < q)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → block i = block i' → Disjoint (A i) (A i'))
    (hfloor : ∀ i, γ i = g → ENNReal.ofReal (w / (K * (q : ℝ))) ≤ ν (A i))
    (P : ℝ≥0∞)
    (hbad : ∀ i, γ i = g → μ (bad i) ≤ ENNReal.ofReal (C * w / (q : ℝ) ^ 2) * P) :
    μ (⋃ i ∈ (Finset.univ.filter fun i => γ i = g), bad i) ≤ ENNReal.ofReal (C * K) * P := by
  let I := Finset.univ.filter fun i => γ i = g
  have hcard := saturated_packet_count_le ν γ block A g K w hK hw hq hA hdisj hfloor
  have hmass : μ (⋃ i ∈ I, bad i) ≤
      (I.card : ℝ≥0∞) * (ENNReal.ofReal (C * w / (q : ℝ) ^ 2) * P) := by
    calc
      _ ≤ ∑ i ∈ I, μ (bad i) := measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ I, ENNReal.ofReal (C * w / (q : ℝ) ^ 2) * P :=
        Finset.sum_le_sum fun i hi => hbad i (Finset.mem_filter.mp hi).2
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hnum : (I.card : ℝ) * (C * w / (q : ℝ) ^ 2) ≤ C * K := by
    calc
      _ ≤ (K * (q : ℝ) ^ 2 / w) * (C * w / (q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by field_simp
  have heq : (I.card : ℝ≥0∞) * (ENNReal.ofReal (C * w / (q : ℝ) ^ 2) * P) =
      ENNReal.ofReal ((I.card : ℝ) * (C * w / (q : ℝ) ^ 2)) * P := by
    simp [ENNReal.ofReal_mul, mul_assoc]
  exact (hmass.trans_eq heq).trans (mul_le_mul (ENNReal.ofReal_le_ofReal hnum) le_rfl bot_le bot_le)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
