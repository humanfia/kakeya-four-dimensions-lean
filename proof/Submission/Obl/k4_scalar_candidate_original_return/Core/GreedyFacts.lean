import Submission.Obl.k4_scalar_candidate_original_return.Core.Defs

/-!
# Facts about the maximal greedy candidate families
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set
open Submission.Lib.K4FinitePlankAtlases

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid)
include ha

/-- Probability, measurability and time support of the original world laws. -/
private theorem exact_world (k : ℕ) (g : Fin (a.Wk k)) :
    IsProbabilityMeasure (ν (a.p k) (a.sm k) g) ∧
      MeasurableSet (E (a.p k) (a.sm k) g) ∧
      E (a.p k) (a.sm k) g ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
  have h := ((ha.exact k).2.1 (a.sm k)).2.2.2.1 g
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Measurability of the full prior sets of every layer. -/
private theorem prior_measurable (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n) :
    MeasurableSet ((a.ls k ℓ).prior i) := by
  obtain ⟨-, -, hcd, -, -⟩ := ha.layer k ℓ
  obtain ⟨-, -, hmeas, -⟩ := hcd
  exact (hmeas i).1

theorem rho_univ_le_one (k : ℕ) (g : Fin (a.Wk k)) : a.ρ k g univ ≤ 1 := by
  obtain ⟨hprob, -, hsub⟩ := exact_world ha k g
  have := hprob
  calc a.ρ k g univ ≤ mu (a.p k) (a.sm k) g univ := Measure.le_iff'.1 (ha.rho_le k g) univ
    _ = ((ν (a.p k) (a.sm k) g).prod volume) (E (a.p k) (a.sm k) g) :=
        Measure.restrict_apply_univ _
    _ ≤ ((ν (a.p k) (a.sm k) g).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hsub
    _ = 1 := by simp [Measure.prod_prod]

theorem rho_finite (k : ℕ) (g : Fin (a.Wk k)) : IsFiniteMeasure (a.ρ k g) :=
  ⟨(rho_univ_le_one ha k g).trans_lt ENNReal.one_lt_top⟩

theorem plank_measurable (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n) :
    MeasurableSet (a.plank k ℓ i) :=
  (prior_measurable ha k ℓ i).prod measurableSet_Icc

theorem candSet_measurable (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) (P : Poly) : MeasurableSet (a.candSet θ σ k ℓ i P) :=
  ((prior_measurable ha k ℓ i).inter (Fit_closed P _ _ _).measurableSet).prod
    measurableSet_Icc

theorem candSet_subset_plank (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) (P : Poly) : a.candSet θ σ k ℓ i P ⊆ a.plank k ℓ i := by
  intro z hz
  exact ⟨hz.1.1, hz.2⟩

theorem greedy_spec (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) : a.GreedySpec θ σ k ℓ i (a.greedy θ σ k ℓ i) := by
  classical
  haveI := rho_finite ha k ((a.ls k ℓ).world i)
  haveI : IsFiniteMeasure (a.plankMeasure k ℓ i) := by
    unfold plankMeasure
    infer_instance
  have hex : ∃ l, a.GreedySpec θ σ k ℓ i l := by
    let η : ℝ := if 0 < a.thr θ σ k ℓ i then min (a.thr θ σ k ℓ i) 1 else 1
    have hη : 0 < η := by
      dsimp only [η]
      split_ifs with h
      · exact lt_min h one_pos
      · exact one_pos
    have hfloor : ∀ P, η ≤ a.greedyThr θ σ k ℓ i P := by
      intro P
      have hμ : 0 ≤ (a.plankMeasure k ℓ i).real univ := measureReal_nonneg
      have hη1 : η ≤ 1 := by
        dsimp only [η]
        split_ifs
        · exact min_le_right _ _
        · exact le_rfl
      unfold greedyThr
      by_cases hc : a.Admissible σ k P ∧ 0 < a.thr θ σ k ℓ i
      · rw [if_pos hc]
        dsimp only [η]
        rw [if_pos hc.2]
        exact min_le_left _ _
      · rw [if_neg hc]
        linarith
    obtain ⟨l, hl, hstop⟩ := exists_threshold_greedy_exhaustion (a.candSet θ σ k ℓ i)
      (candSet_measurable ha θ σ k ℓ i) (a.greedyThr θ σ k ℓ i) (a.plankMeasure k ℓ i)
      hη hfloor
    exact ⟨l, hl, hstop⟩
  unfold greedy
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem cov_measurable (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) : MeasurableSet (a.cov θ σ k ℓ i) := by
  unfold cov
  exact MeasurableSet.biUnion (a.greedy θ σ k ℓ i).finite_toSet.countable
    (fun P _ => candSet_measurable ha θ σ k ℓ i P)

theorem cov_subset_plank (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) : a.cov θ σ k ℓ i ⊆ a.plank k ℓ i := by
  unfold cov
  exact iUnion₂_subset fun P _ => candSet_subset_plank ha θ σ k ℓ i P

theorem Cov_measurable (θ : ℝ) (σ : Scenario) (k : ℕ) (g : Fin (a.Wk k)) :
    MeasurableSet (a.Cov θ σ k g) := by
  unfold Cov
  refine MeasurableSet.biUnion (Set.to_countable _) (fun ℓ _ => ?_)
  exact MeasurableSet.iUnion fun i =>
    MeasurableSet.iUnion fun _ => cov_measurable ha θ σ k ℓ i

theorem CovJ_measurable (θ : ℝ) (J k : ℕ) (g : Fin (a.Wk k)) :
    MeasurableSet (a.CovJ θ J k g) := by
  unfold CovJ
  exact MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun _ => Cov_measurable ha θ (menu n) k g

/-- The residual mass of a candidate after deleting a family of candidates is its original
mass outside their union. -/
private theorem residual_apply (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) (l : List Poly) (P : Poly) :
    (residualMeasure (a.candSet θ σ k ℓ i) (a.plankMeasure k ℓ i) l)
        (a.candSet θ σ k ℓ i P) =
      a.ρ k ((a.ls k ℓ).world i)
        (a.candSet θ σ k ℓ i P \ ⋃ Q ∈ l, a.candSet θ σ k ℓ i Q) := by
  have hP := candSet_measurable ha θ σ k ℓ i P
  have hU : MeasurableSet (⋃ Q ∈ l, a.candSet θ σ k ℓ i Q) :=
    MeasurableSet.biUnion l.finite_toSet.countable
      (fun Q _ => candSet_measurable ha θ σ k ℓ i Q)
  rw [residualMeasure_eq _ (candSet_measurable ha θ σ k ℓ i), Measure.restrict_apply hP]
  unfold plankMeasure
  rw [Measure.restrict_apply (hP.inter hU.compl)]
  congr 1
  ext z
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2⟩, candSet_subset_plank ha θ σ k ℓ i P h1⟩

/-- Maximality: an admissible candidate with positive floor has less than its floor
outside the covered incidences. -/
theorem greedy_maximal (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) (P : Poly) (hP : a.Admissible σ k P)
    (hthr : 0 < a.thr θ σ k ℓ i) :
    a.ρ k ((a.ls k ℓ).world i) (a.candSet θ σ k ℓ i P \ a.cov θ σ k ℓ i) <
      ENNReal.ofReal (a.thr θ σ k ℓ i) := by
  classical
  haveI := rho_finite ha k ((a.ls k ℓ).world i)
  have hspec := (greedy_spec ha θ σ k ℓ i).2 P
  have hthrP : a.greedyThr θ σ k ℓ i P = a.thr θ σ k ℓ i := by
    unfold greedyThr
    rw [if_pos ⟨hP, hthr⟩]
  rw [hthrP, measureReal_def, residual_apply ha] at hspec
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact (ENNReal.ofReal_lt_ofReal_iff hthr).mpr hspec

/-- Every entry of the greedy list is admissible and carries its floor on incidences
not covered by the earlier entries. -/
theorem greedy_entry (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) (m : Fin (a.greedy θ σ k ℓ i).length) :
    a.Admissible σ k ((a.greedy θ σ k ℓ i).get m) ∧ 0 < a.thr θ σ k ℓ i ∧
      ENNReal.ofReal (a.thr θ σ k ℓ i) ≤
        a.ρ k ((a.ls k ℓ).world i)
          (a.candSet θ σ k ℓ i ((a.greedy θ σ k ℓ i).get m) \
            ⋃ P ∈ (a.greedy θ σ k ℓ i).take m.val, a.candSet θ σ k ℓ i P) := by
  classical
  haveI := rho_finite ha k ((a.ls k ℓ).world i)
  haveI : IsFiniteMeasure (a.plankMeasure k ℓ i) := by
    unfold plankMeasure
    infer_instance
  have hmass := (greedy_spec ha θ σ k ℓ i).1.mass_at m
  have hle : (residualMeasure (a.candSet θ σ k ℓ i) (a.plankMeasure k ℓ i)
      ((a.greedy θ σ k ℓ i).take m.val)).real
        (a.candSet θ σ k ℓ i ((a.greedy θ σ k ℓ i).get m)) ≤
      (a.plankMeasure k ℓ i).real univ := by
    rw [residualMeasure_eq _ (candSet_measurable ha θ σ k ℓ i)]
    calc _ ≤ ((a.plankMeasure k ℓ i).restrict
            (⋃ b ∈ (a.greedy θ σ k ℓ i).take m.val, a.candSet θ σ k ℓ i b)ᶜ).real univ :=
          measureReal_mono (subset_univ _) (measure_ne_top _ _)
      _ ≤ (a.plankMeasure k ℓ i).real univ := by
          simp only [measureReal_def]
          exact ENNReal.toReal_mono (measure_ne_top _ _)
            (Measure.le_iff'.1 Measure.restrict_le_self univ)
  by_cases hadm : a.Admissible σ k ((a.greedy θ σ k ℓ i).get m) ∧ 0 < a.thr θ σ k ℓ i
  · refine ⟨hadm.1, hadm.2, ?_⟩
    have hthrP : a.greedyThr θ σ k ℓ i ((a.greedy θ σ k ℓ i).get m) = a.thr θ σ k ℓ i := by
      unfold greedyThr
      rw [if_pos hadm]
    rw [hthrP, measureReal_def, residual_apply ha] at hmass
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hmass
  · exfalso
    have hthrP : a.greedyThr θ σ k ℓ i ((a.greedy θ σ k ℓ i).get m) =
        (a.plankMeasure k ℓ i).real univ + 1 := by
      unfold greedyThr
      rw [if_neg hadm]
    rw [hthrP] at hmass
    linarith

theorem covJ_zero (θ : ℝ) (k : ℕ) (g : Fin (a.Wk k)) : a.CovJ θ 0 k g = ∅ := by
  unfold CovJ
  simp

theorem covJ_mono (θ : ℝ) {J J' : ℕ} (h : J' ≤ J) (k : ℕ) (g : Fin (a.Wk k)) :
    a.CovJ θ J' k g ⊆ a.CovJ θ J k g := by
  intro z hz
  unfold CovJ at hz ⊢
  obtain ⟨n, hn, hz⟩ := mem_iUnion₂.1 hz
  exact mem_iUnion₂.2 ⟨n, lt_of_lt_of_le hn h, hz⟩

theorem covMass_mono (θ : ℝ) {J J' : ℕ} (h : J' ≤ J) (k : ℕ) :
    a.covMass θ J' k ≤ a.covMass θ J k := by
  unfold covMass
  exact Finset.sum_le_sum fun g _ =>
    mul_le_mul' le_rfl (measure_mono (covJ_mono ha θ h k g))

theorem cov_subset_CovJ (θ : ℝ) {J n : ℕ} (hn : n < J) (k : ℕ) (ℓ : Fin (a.ct k))
    (hs : 0 < (menu n).s₀) (hc : 0 < (menu n).c₀)
    (hℓ : ℓ ∈ a.layersOf θ (menu n) k) (i : Fin (a.ls k ℓ).n) :
    a.cov θ (menu n) k ℓ i ⊆ a.CovJ θ J k ((a.ls k ℓ).world i) := by
  intro z hz
  unfold CovJ Cov
  refine mem_iUnion₂.2 ⟨n, hn, ?_⟩
  refine mem_iUnion₂.2 ⟨hs, hc, ?_⟩
  refine mem_iUnion₂.2 ⟨ℓ, hℓ, ?_⟩
  exact mem_iUnion₂.2 ⟨i, rfl, hz⟩

end PreparedData

end Submission.Obl.k4_scalar_candidate_original_return
