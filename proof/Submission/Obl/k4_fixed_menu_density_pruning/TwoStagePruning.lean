import Submission.Obl.k4_fixed_menu_density_pruning.CandidatePruning
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

namespace Submission.Obl.k4_fixed_menu_density_pruning

open MeasureTheory Set Finset
open scoped ENNReal

/-- A common deletion, followed by relative old-packet and candidate pruning,
is charged to six times the original weighted exceptional mass. -/
theorem two_stage_pruning {X : Type*} [MeasurableSpace X] {W C n : ℕ}
    (μ : Fin W → Measure X) (w : Fin W → ENNReal)
    (γ : Fin C → Fin W) (F : Fin C → Set X)
    (old : Fin n → Fin C) (V : Fin n → Set X) (Good : Fin W → Set X)
    (hF : ∀ b, MeasurableSet (F b)) (hGood : ∀ g, MeasurableSet (Good g))
    (hV : ∀ a, MeasurableSet (V a))
    (hFd : ∀ b b', b ≠ b' → γ b = γ b' → Disjoint (F b) (F b'))
    (hVd : ∀ a a', a ≠ a' → γ (old a) = γ (old a') → Disjoint (V a) (V a'))
    (hsub : ∀ a, V a ⊆ F (old a))
    (hfinF : ∀ b, μ (γ b) (F b) ≠ ⊤)
    (hfinV : ∀ a, μ (γ (old a)) (V a) ≠ ⊤)
    {mass : ℝ} (hmass0 : 0 ≤ mass)
    (hmass : ENNReal.ofReal mass ≤ ∑ a, w (γ (old a)) * μ (γ (old a)) (V a))
    (herr : ∑ g, w g * μ g (Good g)ᶜ ≤ ENNReal.ofReal (mass / 12)) :
    ∃ (S : Finset (Fin n)) (V' : Fin n → Set X),
      (∀ a, MeasurableSet (V' a)) ∧
      (∀ a, V' a ⊆ V a ∩ Good (γ (old a))) ∧
      (∀ a ∉ S, V' a = ∅) ∧
      (∀ a ∈ S, ENNReal.ofReal (1 / 2 : ℝ) * μ (γ (old a)) (V a) ≤
          μ (γ (old a)) (V' a) ∧
        ENNReal.ofReal (1 / 2 : ℝ) * μ (γ (old a)) (F (old a)) ≤
          μ (γ (old a)) (F (old a) ∩ Good (γ (old a)))) ∧
      ENNReal.ofReal (mass / 2) ≤ ∑ a, w (γ (old a)) * μ (γ (old a)) (V' a) := by
  classical
  let bad : Finset (Fin C) := univ.filter
    (fun b => ¬ μ (γ b) (F b) ≤ 2 * μ (γ b) (F b ∩ Good (γ b)))
  let BadOld : Fin W → Set X := fun g => ⋃ b ∈ bad.filter (fun b => γ b = g), F b
  let Bad : Fin W → Set X := fun g => (Good g)ᶜ ∪ BadOld g
  have hbad (b : Fin C) (hb : b ∈ bad) :
      μ (γ b) (F b) ≤ 2 * μ (γ b) (F b ∩ (Good (γ b))ᶜ) := by
    have hn : ¬ μ (γ b) (F b) ≤ 2 * μ (γ b) (F b ∩ Good (γ b)) :=
      (mem_filter.mp hb).2
    apply Submission.Obl.k4_scalar_terminal_chart_packet_extraction.le_two_mul_inter_of_diff_le
      (μ (γ b)) (c := μ (γ b) (F b ∩ Good (γ b)))
      (ne_top_of_le_ne_top (hfinF b) (measure_mono inter_subset_left))
    · simp only [sdiff_compl]
      exact le_rfl
    · exact (lt_of_not_ge hn).le
  have holdloss : (∑ g, w g * μ g (BadOld g)) ≤
      2 * ∑ g, w g * μ g (Good g)ᶜ := by
    calc
      _ ≤ ∑ g, w g * ∑ b ∈ bad.filter (fun b => γ b = g), μ g (F b) := by
        gcongr with g
        exact measure_biUnion_finset_le _ _
      _ = ∑ b ∈ bad, w (γ b) * μ (γ b) (F b) := by
        simp_rw [mul_sum]
        rw [← sum_fiberwise bad γ (fun b => w (γ b) * μ (γ b) (F b))]
        apply sum_congr rfl
        intro g _
        apply sum_congr rfl
        intro b hb
        rw [(mem_filter.mp hb).2]
      _ ≤ _ := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.weighted_bad_le
        w μ γ F (fun g => (Good g)ᶜ) bad hF (fun g => (hGood g).compl)
        (fun b _ b' _ hne hγ => by
          rw [Set.disjoint_iff_inter_eq_empty.mp (hFd b b' hne hγ), measure_empty]) hbad
  have hBadOld (g : Fin W) : MeasurableSet (BadOld g) := by
    apply MeasurableSet.biUnion (Finset.countable_toSet _) (fun b _ => hF b)
  have hBad (g : Fin W) : MeasurableSet (Bad g) := (hGood g).compl.union (hBadOld g)
  have hBadloss : ∑ g, w g * μ g (Bad g) ≤ ENNReal.ofReal (mass / 4) := by
    calc
      _ ≤ ∑ g, w g * (μ g (Good g)ᶜ + μ g (BadOld g)) := by
        gcongr with g
        exact measure_union_le _ _
      _ = (∑ g, w g * μ g (Good g)ᶜ) + ∑ g, w g * μ g (BadOld g) := by
        simp only [mul_add, sum_add_distrib]
      _ ≤ (∑ g, w g * μ g (Good g)ᶜ) + 2 * ∑ g, w g * μ g (Good g)ᶜ :=
        add_le_add le_rfl holdloss
      _ ≤ ENNReal.ofReal (mass / 12) + 2 * ENNReal.ofReal (mass / 12) := by gcongr
      _ = ENNReal.ofReal (mass / 4) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  let V' := prunedCandidate μ (γ ∘ old) V Bad
  let S : Finset (Fin n) := univ.filter (fun a =>
    μ (γ (old a)) (V a ∩ Bad (γ (old a))) ≤
      ENNReal.ofReal ((μ (γ (old a)) (V a)).toReal / 2) ∧ old a ∉ bad)
  have hnotbad (a : Fin n) (ha : old a ∈ bad) : V' a = ∅ := by
    by_cases hk : μ (γ (old a)) (V a ∩ Bad (γ (old a))) ≤
        ENNReal.ofReal ((μ (γ (old a)) (V a)).toReal / 2)
    · rw [show V' a = V a \ Bad (γ (old a)) from ite_eq_left hk]
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      apply hq.2
      exact Or.inr (mem_biUnion (by simp [ha]) (hsub a hq.1))
    · exact ite_eq_right hk
  refine ⟨S, V', (fun a => measurableSet_prunedCandidate μ (γ ∘ old) V Bad a
    (hV a) (hBad _)), ?_, ?_, ?_, ?_⟩
  · intro a q hq
    have hp := prunedCandidate_subset μ (γ ∘ old) V Bad a hq
    exact ⟨hp.1, not_not.mp (fun hn => hp.2 (Or.inl hn))⟩
  · intro a ha
    have hn : ¬ (μ (γ (old a)) (V a ∩ Bad (γ (old a))) ≤
      ENNReal.ofReal ((μ (γ (old a)) (V a)).toReal / 2) ∧ old a ∉ bad) := by
      simpa only [S, mem_filter, Finset.mem_univ, true_and] using ha
    by_cases hb : old a ∈ bad
    · exact hnotbad a hb
    · exact ite_eq_right (fun hk => hn ⟨hk, hb⟩)
  · intro a ha
    obtain ⟨hk, hb⟩ := (mem_filter.mp ha).2
    refine ⟨prunedCandidate_relative_floor μ (γ ∘ old) V Bad a (hfinV a) hk _ le_rfl, ?_⟩
    have hh : μ (γ (old a)) (F (old a)) ≤
        2 * μ (γ (old a)) (F (old a) ∩ Good (γ (old a))) := by
      simpa only [bad, mem_filter, Finset.mem_univ, true_and, not_not] using hb
    calc
      _ ≤ ENNReal.ofReal (1 / 2 : ℝ) *
          (2 * μ (γ (old a)) (F (old a) ∩ Good (γ (old a)))) := by gcongr
      _ = _ := by
        have hc : ENNReal.ofReal (1 / 2 : ℝ) * (2 : ENNReal) = 1 := by
          rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          norm_num
        rw [← mul_assoc, hc, one_mul]
  · exact weighted_prunedCandidate_floor μ w (γ ∘ old) V Bad hV hVd hfinV
      hmass0 hmass hBadloss

end Submission.Obl.k4_fixed_menu_density_pruning
