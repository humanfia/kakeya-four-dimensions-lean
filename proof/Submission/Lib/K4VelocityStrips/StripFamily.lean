/-
Adapted from: here:o116

Original heavy-strip packing and frame proofs by session x0644.
-/

import Submission.Lib.K4VelocityStrips.StripPacking
import Submission.Lib.K4VelocityStrips.StripIntersections

/-! Heavy affine strips admit a short separated family of representatives.
All masses below are measured against the same original velocity palette. -/

noncomputable section

namespace Submission.Lib.K4VelocityStrips

open Set MeasureTheory
open scoped RealInnerProductSpace

def boundedStrip (n : StripSpace) (b r T : ℝ) : Set StripSpace :=
  Metric.closedBall 0 T ∩ affineStrip n b r

theorem measurableSet_boundedStrip (n : StripSpace) (b r T : ℝ) :
    MeasurableSet (boundedStrip n b r T) :=
  Metric.isClosed_closedBall.measurableSet.inter (measurableSet_affineStrip n b r)

/-- The angular cap bounds pairwise overlaps of separated strips, including
the empty-intersection case. -/
theorem bounded_strip_intersection_mass_le (μ : Measure StripSpace)
    {n m : StripSpace} {b c r ρ T ε : ℝ}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hT : 0 ≤ T) (hρ : 0 < ρ)
    (hsmall : 4 * r ≤ ρ)
    (hsep : ρ ≤ ‖n - m‖ + |b - c|) (hsep' : ρ ≤ ‖n + m‖ + |b + c|)
    (hcap : ∀ x : StripSpace,
      μ (Metric.closedBall x (32 * (1 + T) * r / ρ)) ≤ ENNReal.ofReal ε) :
    μ (boundedStrip n b r T ∩ boundedStrip m c r T) ≤ ENNReal.ofReal ε := by
  by_cases he : (boundedStrip n b r T ∩ boundedStrip m c r T).Nonempty
  · obtain ⟨x, hx⟩ := he
    have hdet := separated_strip_wedge hn hm hT
      (show ‖x‖ ≤ T by simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1.1)
      hρ hsmall hsep hsep' hx.1.2 hx.2.2
    have hsub : boundedStrip n b r T ∩ boundedStrip m c r T ⊆
        Metric.closedBall x (32 * (1 + T) * r / ρ) := by
      intro y hy
      rw [Metric.mem_closedBall, dist_comm]
      have h := strip_intersection_diameter hn hm
        (show 0 < ρ / (4 * (1 + T)) by positivity) hdet
        hx.1.2 hx.2.2 hy.1.2 hy.2.2
      convert h using 1
      field_simp
      ring
    exact (measure_mono hsub).trans (hcap x)
  · rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty]
    exact bot_le

/-- A separated family of heavy strips has cardinality bounded solely by its
mass floor, once the angular overlap error is smaller than that floor squared. -/
theorem heavy_strips_card_le {ι : Type*} [Fintype ι]
    (μ : Measure StripSpace) [IsProbabilityMeasure μ]
    (n : ι → StripSpace) (b : ι → ℝ) {κ ε r ρ T : ℝ}
    (hn : ∀ i, ‖n i‖ = 1) (hκ : 0 < κ) (hε : 0 ≤ ε)
    (hT : 0 ≤ T) (hρ : 0 < ρ) (hsmall : 4 * r ≤ ρ)
    (hmass : ∀ i, κ ≤ μ.real (boundedStrip (n i) (b i) r T))
    (hsep : ∀ i j, i ≠ j →
      ρ ≤ ‖n i - n j‖ + |b i - b j| ∧ ρ ≤ ‖n i + n j‖ + |b i + b j|)
    (hcap : ∀ x : StripSpace,
      μ (Metric.closedBall x (32 * (1 + T) * r / ρ)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ κ ^ 2) :
    (Fintype.card ι : ℝ) ≤ 2 / κ ^ 2 := by
  apply heavy_event_card_le μ (fun i => boundedStrip (n i) (b i) r T)
    (fun i => measurableSet_boundedStrip _ _ _ _) hκ hε hmass _ heps
  intro i j hij
  have h := bounded_strip_intersection_mass_le μ (hn i) (hn j) hT hρ hsmall
    (hsep i j hij).1 (hsep i j hij).2 hcap
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h
  simpa only [measureReal_def, ENNReal.toReal_ofReal hε] using hreal

/-- Finite parameter nets can be chosen before any later trajectory restriction.
Separation and coverage both identify the two orientations of the same line. -/
theorem exists_separated_strip_representatives {ι : Type*} [Fintype ι]
    (n : ι → StripSpace) (b : ι → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s : Finset ι,
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ρ ≤ ‖n i - n j‖ + |b i - b j| ∧ ρ ≤ ‖n i + n j‖ + |b i + b j|) ∧
      ∀ i, ∃ j ∈ s,
        ‖n i - n j‖ + |b i - b j| < ρ ∨ ‖n i + n j‖ + |b i + b j| < ρ := by
  classical
  let sep : ι → ι → Prop := fun i j =>
    ρ ≤ ‖n i - n j‖ + |b i - b j| ∧ ρ ≤ ‖n i + n j‖ + |b i + b j|
  have hsymm : ∀ i j, sep i j → sep j i := by
    intro i j h
    simpa only [sep, norm_sub_rev, abs_sub_comm, add_comm] using h
  let candidates := Finset.univ.powerset.filter (fun s : Finset ι =>
    ∀ i ∈ s, ∀ j ∈ s, i ≠ j → sep i j)
  have hne : candidates.Nonempty := ⟨∅, by simp [candidates]⟩
  obtain ⟨s, hs, hmax⟩ := candidates.exists_maximal hne
  have hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → sep i j := (Finset.mem_filter.mp hs).2
  refine ⟨s, hpair, ?_⟩
  intro i
  by_cases his : i ∈ s
  · exact ⟨i, his, Or.inl (by simpa using hρ)⟩
  · by_contra! hfar
    have hsep : ∀ j ∈ s, sep i j := by
      intro j hj
      exact ⟨(hfar j hj).1, (hfar j hj).2⟩
    have hiPair : ∀ j ∈ insert i s, ∀ k ∈ insert i s, j ≠ k → sep j k := by
      intro j hj k hk hjk
      rcases Finset.mem_insert.mp hj with hji | hj
      · rcases Finset.mem_insert.mp hk with hki | hk
        · exact False.elim (hjk (hji.trans hki.symm))
        · simpa only [hji] using hsep k hk
      · rcases Finset.mem_insert.mp hk with hki | hk
        · simpa only [hki] using hsymm i j (hsep j hj)
        · exact hpair j hj k hk hjk
    have hiMem : insert i s ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
        true_and]
      exact hiPair
    exact his ((hmax hiMem (Finset.subset_insert i s)) (Finset.mem_insert_self i s))

/-- The heavy-strip net is a short list, independently of the total number of
state-predicted strips. No posterior renormalization is used. -/
theorem exists_short_heavy_strip_net {ι : Type*} [Fintype ι]
    (μ : Measure StripSpace) [IsProbabilityMeasure μ]
    (n : ι → StripSpace) (b : ι → ℝ) {κ ε r ρ T : ℝ}
    (hn : ∀ i, ‖n i‖ = 1) (hκ : 0 < κ) (hε : 0 ≤ ε)
    (hT : 0 ≤ T) (hρ : 0 < ρ) (hsmall : 4 * r ≤ ρ)
    (hmass : ∀ i, κ ≤ μ.real (boundedStrip (n i) (b i) r T))
    (hcap : ∀ x : StripSpace,
      μ (Metric.closedBall x (32 * (1 + T) * r / ρ)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ κ ^ 2) :
    ∃ s : Finset ι, (s.card : ℝ) ≤ 2 / κ ^ 2 ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ρ ≤ ‖n i - n j‖ + |b i - b j| ∧ ρ ≤ ‖n i + n j‖ + |b i + b j|) ∧
      ∀ i, ∃ j ∈ s,
        ‖n i - n j‖ + |b i - b j| < ρ ∨ ‖n i + n j‖ + |b i + b j| < ρ := by
  classical
  obtain ⟨s, hsep, hcover⟩ := exists_separated_strip_representatives n b hρ
  refine ⟨s, ?_, hsep, hcover⟩
  have h := heavy_strips_card_le μ (fun i : s => n i) (fun i : s => b i)
    (fun i => hn i) hκ hε hT hρ hsmall (fun i => hmass i)
    (fun i j hij => hsep i i.2 j j.2 (by simpa using hij)) hcap heps
  simpa only [Fintype.card_coe] using h

end Submission.Lib.K4VelocityStrips
