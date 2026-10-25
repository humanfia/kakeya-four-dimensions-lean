/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockRecovery.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockRecovery.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarTimeRecovery

/-! Assemble local scalar fits and restore all original labels at their times. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem original_block_fit_recovery {Λ ι : Type*} [MeasurableSpace Λ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    (ν : Measure Λ) [SFinite ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (K : Finset ι) (T : ι → Set ℝ) (code : ℝ → ι) (hcode : Measurable code)
    (F : ℝ → ℝ) (a v : ι → ℝ) {ell τ B ε : ℝ} (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (hTm : ∀ k ∈ K, MeasurableSet (T k))
    (hTcode : ∀ k ∈ K, ∀ t ∈ T k, code t = k)
    (hlength : ∀ k ∈ K, ENNReal.ofReal ell ≤ volume (T k))
    (hfloor : ∀ k ∈ K, ∀ t ∈ T k, ENNReal.ofReal τ ≤ ν {l | (l, t) ∈ E})
    (ha : ∀ k ∈ K, |a k| ≤ B) (hv : ∀ k ∈ K, |v k| ≤ B)
    (hfit : ∀ k ∈ K, ∀ t ∈ T k, |F t - (a k + v k * t)| ≤ ε) :
    ∃ (U : Set ℝ) (A C : ℝ → ℝ), U = ⋃ k ∈ K, T k ∧ MeasurableSet U ∧
      Measurable A ∧ Measurable C ∧ (∀ t, |A t| ≤ B ∧ |C t| ≤ B) ∧
      ENNReal.ofReal ((K.card : ℝ) * ell) ≤ volume U ∧
      ENNReal.ofReal (τ * (K.card : ℝ) * ell) ≤ (ν.prod volume) (E ∩ (univ ×ˢ U)) ∧
      (∀ k ∈ K, ∀ t ∈ T k, A t = v k ∧ C t = a k) ∧
      (∀ t ∈ U, ENNReal.ofReal τ ≤ ν {l | (l, t) ∈ E ∩ (univ ×ˢ U)}) ∧
      ∀ p ∈ E ∩ (univ ×ˢ U), |F p.2 - (C p.2 + A p.2 * p.2)| ≤ ε := by
  classical
  have hdisj : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (T i) (T j) := by
    intro i hi j hj hne
    apply disjoint_left.mpr
    intro t ht ht'
    exact hne ((hTcode i hi t ht).symm.trans (hTcode j hj t ht'))
  obtain ⟨U, hUeq, hUm, hvol, hmass⟩ :=
    original_active_time_union ν hE K T hτ hTm hdisj hlength hfloor
  let A : ℝ → ℝ := fun t => if code t ∈ K then v (code t) else 0
  let C : ℝ → ℝ := fun t => if code t ∈ K then a (code t) else 0
  have hAm : Measurable A :=
    (Measurable.of_discrete : Measurable (fun k : ι => if k ∈ K then v k else (0 : ℝ))).comp hcode
  have hCm : Measurable C :=
    (Measurable.of_discrete : Measurable (fun k : ι => if k ∈ K then a k else (0 : ℝ))).comp hcode
  have hbound t : |A t| ≤ B ∧ |C t| ≤ B := by
    by_cases ht : code t ∈ K
    · simpa only [A, C, if_pos ht] using And.intro (hv _ ht) (ha _ ht)
    · simp only [A, C, if_neg ht, abs_zero]
      exact ⟨hB, hB⟩
  have hrows k (hk : k ∈ K) t (ht : t ∈ T k) : A t = v k ∧ C t = a k := by
    simp only [A, C, hTcode k hk t ht, if_pos hk, and_self]
  refine ⟨U, A, C, hUeq, hUm, hAm, hCm, hbound, hvol, hmass, hrows, ?_, ?_⟩
  · intro t ht
    have hsection : {l | (l, t) ∈ E ∩ (univ ×ˢ U)} = {l | (l, t) ∈ E} := by
      ext l
      simp only [mem_inter_iff, mem_prod, mem_univ, true_and, ht, and_true, mem_setOf_eq]
    rw [hsection]
    rw [hUeq] at ht
    obtain ⟨k, hk, htk⟩ := mem_iUnion₂.mp ht
    exact hfloor k hk t htk
  · intro p hp
    have ht : p.2 ∈ U := hp.2.2
    rw [hUeq] at ht
    obtain ⟨k, hk, htk⟩ := mem_iUnion₂.mp ht
    rw [(hrows k hk p.2 htk).1, (hrows k hk p.2 htk).2]
    exact hfit k hk p.2 htk

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
