/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/SelectedBudget.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/-
Shared from this LOT obligation o105, session x0548, branch commit 6d6fdd6,
Submission/Obl/k4_critical_path_framework/SelectedBudget.lean.
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Definitions

/-! Incidence selections in disjoint assignments have no overlap cost.
The possible overlap of adjacent closed time blocks has Lebesgue measure zero.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set
open scoped ENNReal Classical

theorem dyadic_blocks_aedisjoint {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (T : ℕ) {j j' : ℕ} (hne : j ≠ j') :
    AEDisjoint (ν.prod volume)
      (univ ×ˢ Icc ((j : ℝ) / (2 : ℝ) ^ T) ((j + 1 : ℝ) / (2 : ℝ) ^ T))
      (univ ×ˢ Icc ((j' : ℝ) / (2 : ℝ) ^ T) ((j' + 1 : ℝ) / (2 : ℝ) ^ T)) := by
  have hlt (j j' : ℕ) (hjj : j < j') :
      AEDisjoint (ν.prod volume)
        (univ ×ˢ Icc ((j : ℝ) / (2 : ℝ) ^ T) ((j + 1 : ℝ) / (2 : ℝ) ^ T))
        (univ ×ˢ Icc ((j' : ℝ) / (2 : ℝ) ^ T) ((j' + 1 : ℝ) / (2 : ℝ) ^ T)) := by
    apply measure_mono_null (t := univ ×ˢ {((j : ℝ) + 1) / (2 : ℝ) ^ T})
    · rintro ⟨l, t⟩ ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩
      refine ⟨mem_univ _, ?_⟩
      have hjR : (j : ℝ) + 1 ≤ j' := by exact_mod_cast Nat.succ_le_of_lt hjj
      have hdiv := div_le_div_of_nonneg_right hjR (show (0 : ℝ) ≤ 2 ^ T by positivity)
      exact le_antisymm ht.2 (hdiv.trans ht'.1)
    · rw [Measure.prod_prod]
      simp
  rcases lt_or_gt_of_ne hne with h | h
  · exact hlt j j' h
  · exact (hlt j' j h).symm

/-- Pairwise a.e. disjointness holds inside each world, across all time blocks. -/
theorem Atlas.selected_aedisjoint {p : Data} {k M D : ℕ} {r : ℝ} (a : Atlas p k)
    (hsep : a.Separated) (ex : Fin a.C → Prop)
    (hch : ∀ b, Chart (p.N k) M D a.κ a.T (a.j b : ℝ) r (p.B k (a.γ b))
      (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b) (a.F b) (ex b))
    {b b' : Fin a.C} (hne : b ≠ b') (hγ : a.γ b = a.γ b') :
    AEDisjoint ((p.ν k (a.γ b)).prod volume) (a.F b) (a.F b') := by
  have hsub (b : Fin a.C) : a.F b ⊆ a.A b ×ˢ
      Icc ((a.j b : ℝ) / (2 : ℝ) ^ a.T) (((a.j b : ℝ) + 1) / (2 : ℝ) ^ a.T) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩ := hch b
    intro q hq
    exact ⟨(hsel q hq).2.1, (hsel q hq).2.2.1⟩
  by_cases hj : a.j b = a.j b'
  · apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    intro q hq hq'
    exact Set.disjoint_left.mp (hsep b b' hne hγ hj) (hsub b hq).1 (hsub b' hq').1
  · have hne' : (a.j b : ℕ) ≠ (a.j b' : ℕ) := by
      intro h
      exact hj (Fin.ext h)
    apply (dyadic_blocks_aedisjoint (p.ν k (a.γ b)) a.T hne').mono
    · exact fun q hq => ⟨mem_univ _, (hsub b hq).2⟩
    · exact fun q hq => ⟨mem_univ _, (hsub b' hq).2⟩

/-- Restricting all chart selections to one original event costs at most that event's mass. -/
theorem Atlas.selected_world_budget {p : Data} {k M D : ℕ} {r : ℝ} (a : Atlas p k)
    (hsep : a.Separated) (ex : Fin a.C → Prop)
    (hch : ∀ b, Chart (p.N k) M D a.κ a.T (a.j b : ℝ) r (p.B k (a.γ b))
      (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b) (a.F b) (ex b))
    (γ : Fin (p.W k)) (Z : Set Incidence) (hZ : MeasurableSet Z) :
    (∑ b ∈ Finset.univ.filter (fun b => a.γ b = γ),
      ((p.ν k γ).prod volume) (a.F b ∩ Z)) ≤
        (((p.ν k γ).prod volume).restrict (p.E k γ)) Z := by
  classical
  let s := Finset.univ.filter (fun b => a.γ b = γ)
  have hmeas (b : Fin a.C) : MeasurableSet (a.F b) := by
    obtain ⟨_, _, _, _, _, _, _, hF, _⟩ := hch b
    exact hF
  have hd : (↑s : Set (Fin a.C)).Pairwise
      (fun b b' => AEDisjoint ((p.ν k γ).prod volume) (a.F b ∩ Z) (a.F b' ∩ Z)) := by
    intro b hb b' hb' hne
    have hbγ : a.γ b = γ := (Finset.mem_filter.mp hb).2
    have hb'γ : a.γ b' = γ := (Finset.mem_filter.mp hb').2
    have h := a.selected_aedisjoint hsep ex hch hne (hbγ.trans hb'γ.symm)
    rw [hbγ] at h
    exact h.mono inter_subset_left inter_subset_left
  calc
    _ = ((p.ν k γ).prod volume) (⋃ b ∈ s, a.F b ∩ Z) :=
      (measure_biUnion_finset₀ hd (fun b _ => ((hmeas b).inter hZ).nullMeasurableSet)).symm
    _ ≤ ((p.ν k γ).prod volume) (Z ∩ p.E k γ) := by
      apply measure_mono
      intro q hq
      simp only [mem_iUnion] at hq
      obtain ⟨b, hb, hq⟩ := hq
      have hbγ : a.γ b = γ := (Finset.mem_filter.mp hb).2
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩ := hch b
      refine ⟨hq.2, ?_⟩
      simpa only [hbγ] using (hsel q hq.1).1
    _ = _ := (Measure.restrict_apply hZ).symm

/-- The same bound after summing worlds with their unchanged original weights. -/
theorem Atlas.selected_weighted_budget {p : Data} {k M D : ℕ} {r : ℝ} (a : Atlas p k)
    (hsep : a.Separated) (ex : Fin a.C → Prop)
    (hch : ∀ b, Chart (p.N k) M D a.κ a.T (a.j b : ℝ) r (p.B k (a.γ b))
      (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b) (a.F b) (ex b))
    (Z : Fin (p.W k) → Set Incidence) (hZ : ∀ γ, MeasurableSet (Z γ)) :
    (∑ b, ENNReal.ofReal (p.ω k (a.γ b)) *
      ((p.ν k (a.γ b)).prod volume) (a.F b ∩ Z (a.γ b))) ≤
        ∑ γ, ENNReal.ofReal (p.ω k γ) *
          (((p.ν k γ).prod volume).restrict (p.E k γ)) (Z γ) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ a.γ]
  apply Finset.sum_le_sum
  intro γ _
  calc
    _ = ENNReal.ofReal (p.ω k γ) *
        ∑ b ∈ Finset.univ.filter (fun b => a.γ b = γ),
          ((p.ν k γ).prod volume) (a.F b ∩ Z γ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [(Finset.mem_filter.mp hb).2]
    _ ≤ _ := mul_le_mul le_rfl (a.selected_world_budget hsep ex hch γ (Z γ) (hZ γ)) zero_le zero_le

/-- A selected system has mass at most one, with the original world weights. -/
theorem Atlas.mass_le_one {p : Data} {k M D : ℕ} {r : ℝ} (a : Atlas p k)
    (hsep : a.Separated) (ex : Fin a.C → Prop)
    (hch : ∀ b, Chart (p.N k) M D a.κ a.T (a.j b : ℝ) r (p.B k (a.γ b))
      (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b) (a.F b) (ex b))
    (hprob : ∀ γ, IsProbabilityMeasure (p.ν k γ))
    (hw0 : ∀ γ, 0 ≤ p.ω k γ) (hw : ∑ γ, p.ω k γ = 1)
    (hE : ∀ γ, p.E k γ ⊆ univ ×ˢ Icc (0 : ℝ) 1) : a.mass ≤ 1 := by
  have hμ (γ : Fin (p.W k)) :
      (((p.ν k γ).prod volume).restrict (p.E k γ)) univ ≤ 1 := by
    letI := hprob γ
    rw [Measure.restrict_apply_univ]
    calc
      _ ≤ ((p.ν k γ).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono (hE γ)
      _ = 1 := by rw [Measure.prod_prod]; simp
  have hb := a.selected_weighted_budget hsep ex hch (fun _ => univ)
    (fun _ => MeasurableSet.univ)
  simp only [inter_univ] at hb
  calc
    a.mass ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) *
        (((p.ν k γ).prod volume).restrict (p.E k γ)) univ := hb
    _ ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) * 1 := Finset.sum_le_sum fun γ _ =>
      mul_le_mul le_rfl (hμ γ) zero_le zero_le
    _ = 1 := by
      simp only [mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => hw0 γ), hw]
      norm_num

end Submission.Obl.k4_balanced_native_packet_transport.CPF
