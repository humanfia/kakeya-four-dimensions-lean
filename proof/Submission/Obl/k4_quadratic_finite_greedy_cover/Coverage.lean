-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/Coverage.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.GreedyGrains

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set
open scoped ENNReal

/-- A finite positive-increment construction stops with coverage or with its
alternative exit. The candidate set itself need not be finite. -/
theorem finite_selection_or_exit {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (Good Stop : Finset ι → Prop) (Exit : Prop)
    {q B : ℝ} (hq : 0 < q) (hzero : Good ∅)
    (hbound : ∀ s, Good s → (∑ a ∈ s, w a) ≤ B)
    (hstep : ∀ s, Good s → ¬ Stop s →
      Exit ∨ ∃ a, a ∉ s ∧ Good (insert a s) ∧ q ≤ w a) :
    Exit ∨ ∃ s, Good s ∧ Stop s := by
  classical
  by_contra h
  have hExit : ¬ Exit := fun he => h (Or.inl he)
  have hStop : ∀ s, Good s → ¬ Stop s := fun s hs ht => h (Or.inr ⟨s, hs, ht⟩)
  obtain ⟨s, hs, hlarge⟩ :=
    WangZahlLot.Obl.wz_move_two_dense_broad_prisms.finite_greedy_of_mass_increment
      w Good (t := B + 1) hq hzero hbound (by
        intro s hs _
        exact (hstep s hs (hStop s hs)).resolve_left hExit)
  linarith [hbound s hs]

/-- Disjoint pieces consume at most one unit of normalized trajectory mass per
old packet. This supplies a uniform finite budget for candidate selection. -/
theorem normalized_assignment_budget {X ι β : Type*} [MeasurableSpace X]
    [Fintype β] [DecidableEq ι]
    (ν : β → Measure X) (A : β → Set X) (parent : ι → β) (piece : ι → Set X)
    (hApos : ∀ b, 0 < (ν b).real (A b)) (hAfin : ∀ b, ν b (A b) ≠ ∞)
    (s : Finset ι)
    (hpiece : ∀ a ∈ s, MeasurableSet (piece a) ∧ piece a ⊆ A (parent a))
    (hdisj : ∀ a ∈ s, ∀ a' ∈ s, a ≠ a' → parent a = parent a' →
      Disjoint (piece a) (piece a')) :
    (∑ a ∈ s, (ν (parent a)).real (piece a) / (ν (parent a)).real (A (parent a))) ≤
      (Fintype.card β : ℝ) := by
  classical
  let w : ι → ℝ := fun a =>
    (ν (parent a)).real (piece a) / (ν (parent a)).real (A (parent a))
  have hlocal (b : β) : (∑ a ∈ s, if parent a = b then w a else 0) ≤ 1 := by
    let t := s.filter (fun a => parent a = b)
    have hsub : (⋃ a ∈ t, piece a) ⊆ A b := by
      intro p hp
      obtain ⟨a, ha, hpa⟩ := mem_iUnion₂.mp hp
      have has := (Finset.mem_filter.mp ha).1
      have hab := (Finset.mem_filter.mp ha).2
      simpa only [hab] using (hpiece a has).2 hpa
    have hd : (t : Set ι).PairwiseDisjoint piece := by
      intro a ha a' ha' haa'
      have has := (Finset.mem_filter.mp ha).1
      have ha's := (Finset.mem_filter.mp ha').1
      exact hdisj a has a' ha's haa'
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp ha').2.symm)
    have hm : ∀ a ∈ t, MeasurableSet (piece a) :=
      fun a ha => (hpiece a (Finset.mem_filter.mp ha).1).1
    have hf : ∀ a ∈ t, ν b (piece a) ≠ ∞ := by
      intro a ha
      have has := (Finset.mem_filter.mp ha).1
      have hab := (Finset.mem_filter.mp ha).2
      apply measure_ne_top_of_subset _ (hAfin b)
      simpa only [hab] using (hpiece a has).2
    have hμ : (∑ a ∈ t, (ν b).real (piece a)) ≤ (ν b).real (A b) := by
      rw [← measureReal_biUnion_finset hd hm hf]
      exact measureReal_mono hsub (hAfin b)
    calc
      (∑ a ∈ s, if parent a = b then w a else 0) = ∑ a ∈ t, w a := by
        rw [Finset.sum_filter]
      _ = (∑ a ∈ t, (ν b).real (piece a)) / (ν b).real (A b) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a ha
        simp only [w, (Finset.mem_filter.mp ha).2]
      _ ≤ (ν b).real (A b) / (ν b).real (A b) :=
        div_le_div_of_nonneg_right hμ (hApos b).le
      _ = 1 := div_self (hApos b).ne'
  have hsplit : (∑ b : β, ∑ a ∈ s, if parent a = b then w a else 0) = ∑ a ∈ s, w a := by
    rw [Finset.sum_comm]
    simp
  calc
    (∑ a ∈ s, w a) = ∑ b : β, ∑ a ∈ s, if parent a = b then w a else 0 := hsplit.symm
    _ ≤ ∑ _b : β, (1 : ℝ) := Finset.sum_le_sum (fun b _ => hlocal b)
    _ = (Fintype.card β : ℝ) := by simp

/-- A positive relative measure floor is a positive increment of the normalized
trajectory-mass budget. -/
theorem normalized_measure_floor {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (A P : Set X) {θ : ℝ}
    (hApos : 0 < ν.real A) (hAfin : ν A ≠ ∞) (hsub : P ⊆ A)
    (hθ : 0 ≤ θ) (hfloor : ENNReal.ofReal θ * ν A ≤ ν P) :
    θ ≤ ν.real P / ν.real A := by
  have hPfin : ν P ≠ ∞ := measure_ne_top_of_subset hsub hAfin
  have ht := ENNReal.toReal_mono hPfin hfloor
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ] at ht
  exact (le_div_iff₀ hApos).mpr ht

/-- The incidence union selected in each original world. -/
def selectedUnion {X ι κ : Type*} (s : Finset ι) (world : ι → κ)
    (V : ι → Set X) : κ → Set X :=
  fun k => ⋃ a ∈ s, {p | world a = k ∧ p ∈ V a}

/-- Residual discovery with a relative packet-mass floor gives finite coverage.
The incidences are disjoint in each world; all original candidate geometry is
retained in `Good`. Analytical masks need no complexity bound at this stage. -/
theorem weighted_greedy_cover {X ι β κ : Type*} [MeasurableSpace X]
    [Fintype β] [Fintype κ] [DecidableEq ι]
    (μ : κ → Measure X) (ω : κ → ℝ) (H : κ → Set X)
    (U : β → Set X) (γ : β → κ) (parent : ι → β) (V : ι → Set X)
    (Good : ι → Prop) (Exit : Prop) {θ : ℝ} (hθ : 0 < θ)
    (hHm : ∀ k, MeasurableSet (H k)) (hHfin : ∀ k, μ k (H k) ≠ ∞)
    (hUpos : ∀ b, 0 < (μ (γ b)).real (U b))
    (hUfin : ∀ b, μ (γ b) (U b) ≠ ∞)
    (hGood : ∀ a, Good a → MeasurableSet (V a) ∧
      V a ⊆ H (γ (parent a)) ∧ V a ⊆ U (parent a) ∧
      ENNReal.ofReal θ * μ (γ (parent a)) (U (parent a)) ≤ μ (γ (parent a)) (V a))
    (hselect : ∀ R : κ → Set X, (∀ k, MeasurableSet (R k) ∧ R k ⊆ H k) →
      (∑ k, ω k * (μ k).real (H k)) / 2 ≤ ∑ k, ω k * (μ k).real (R k) →
      Exit ∨ ∃ a, Good a ∧ V a ⊆ R (γ (parent a))) :
    Exit ∨ ∃ s : Finset ι,
      (∀ a ∈ s, Good a) ∧
      (∀ a ∈ s, ∀ a' ∈ s, a ≠ a' → γ (parent a) = γ (parent a') →
        Disjoint (V a) (V a')) ∧
      (∑ k, ω k * (μ k).real (H k)) / 2 ≤
        ∑ k, ω k * (μ k).real (selectedUnion s (fun a => γ (parent a)) V k) := by
  classical
  let P : Finset ι → Prop := fun s => (∀ a ∈ s, Good a) ∧
    ∀ a ∈ s, ∀ a' ∈ s, a ≠ a' → γ (parent a) = γ (parent a') →
      Disjoint (V a) (V a')
  let Stop : Finset ι → Prop := fun s =>
    (∑ k, ω k * (μ k).real (H k)) / 2 ≤
      ∑ k, ω k * (μ k).real (selectedUnion s (fun a => γ (parent a)) V k)
  let w : ι → ℝ := fun a =>
    (μ (γ (parent a))).real (V a) / (μ (γ (parent a))).real (U (parent a))
  have hsub (s : Finset ι) (hs : P s) (k : κ) :
      selectedUnion s (fun a => γ (parent a)) V k ⊆ H k := by
    intro p hp
    obtain ⟨a, ha, haw, hp⟩ := mem_iUnion₂.mp hp
    simpa only [haw] using (hGood a (hs.1 a ha)).2.1 hp
  have hmeas (s : Finset ι) (hs : P s) (k : κ) :
      MeasurableSet (selectedUnion s (fun a => γ (parent a)) V k) := by
    apply Finset.measurableSet_biUnion
    intro a ha
    by_cases haw : γ (parent a) = k
    · simpa [haw] using (hGood a (hs.1 a ha)).1
    · simp [haw]
  have hbudget (s : Finset ι) (hs : P s) : (∑ a ∈ s, w a) ≤ (Fintype.card β : ℝ) :=
    normalized_assignment_budget (fun b => μ (γ b)) U parent V hUpos hUfin s
      (fun a ha => ⟨(hGood a (hs.1 a ha)).1, (hGood a (hs.1 a ha)).2.2.1⟩)
      (fun a ha a' ha' hne hp => hs.2 a ha a' ha' hne (congrArg γ hp))
  have hstep (s : Finset ι) (hs : P s) (hstop : ¬ Stop s) :
      Exit ∨ ∃ a, a ∉ s ∧ P (insert a s) ∧ θ ≤ w a := by
    let R : κ → Set X := fun k => H k \ selectedUnion s (fun a => γ (parent a)) V k
    have hRm (k : κ) : MeasurableSet (R k) := (hHm k).diff (hmeas s hs k)
    have hbalance :
        (∑ k, ω k * (μ k).real (R k)) +
          (∑ k, ω k * (μ k).real (selectedUnion s (fun a => γ (parent a)) V k)) =
            ∑ k, ω k * (μ k).real (H k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [← mul_add]
      congr 1
      have hh : H k ∩ selectedUnion s (fun a => γ (parent a)) V k =
          selectedUnion s (fun a => γ (parent a)) V k := inter_eq_right.mpr (hsub s hs k)
      simpa only [R, hh] using
        measureReal_sdiff_add_inter (μ := μ k) (s := H k) (hmeas s hs k) (hHfin k)
    have hRmass : (∑ k, ω k * (μ k).real (H k)) / 2 ≤
        ∑ k, ω k * (μ k).real (R k) := by
      dsimp [Stop] at hstop
      linarith [lt_of_not_ge hstop]
    rcases hselect R (fun k => ⟨hRm k, sdiff_subset⟩) hRmass with hex | ⟨a, haGood, haR⟩
    · exact Or.inl hex
    have hinc : θ ≤ w a := normalized_measure_floor (μ (γ (parent a)))
      (U (parent a)) (V a) (hUpos _) (hUfin _) (hGood a haGood).2.2.1 hθ.le
      (hGood a haGood).2.2.2
    have hnew : a ∉ s := by
      intro ha
      have hempty : V a = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        exact (haR hp).2 (mem_iUnion₂.mpr ⟨a, ha, rfl, hp⟩)
      have hz : w a = 0 := by simp [w, hempty]
      rw [hz] at hinc
      linarith
    have hdis : ∀ a' ∈ s, γ (parent a) = γ (parent a') → Disjoint (V a) (V a') := by
      intro a' ha' haw
      apply Set.disjoint_left.mpr
      intro p hp hp'
      exact (haR hp).2 (mem_iUnion₂.mpr ⟨a', ha', haw.symm, hp'⟩)
    refine Or.inr ⟨a, hnew, ⟨?_, ?_⟩, hinc⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact haGood
      · exact hs.1 b hb
    · intro b hb b' hb' hne hworld
      rcases Finset.mem_insert.mp hb with hba | hbs
      · subst b
        rcases Finset.mem_insert.mp hb' with hb'a | hb's
        · exact (hne hb'a.symm).elim
        · exact hdis b' hb's hworld
      · rcases Finset.mem_insert.mp hb' with hb'a | hb's
        · subst b'
          exact (hdis b hbs hworld.symm).symm
        · exact hs.2 b hbs b' hb's hne hworld
  rcases finite_selection_or_exit w P Stop Exit hθ (by simp [P]) hbudget hstep with hex | ⟨s, hs, hstop⟩
  · exact Or.inl hex
  · exact Or.inr ⟨s, hs.1, hs.2, hstop⟩

/-- Finite weighted masses commute with `ofReal` when the original pieces have
finite mass. -/
theorem ofReal_weighted_mass {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (μ : κ → Measure X) (ω : κ → ℝ) (H : κ → Set X)
    (hω : ∀ k, 0 ≤ ω k) (hHfin : ∀ k, μ k (H k) ≠ ∞) :
    ENNReal.ofReal (∑ k, ω k * (μ k).real (H k)) =
      ∑ k, ENNReal.ofReal (ω k) * μ k (H k) := by
  rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (f := fun k => ω k * (μ k).real (H k))
    (fun k _ => mul_nonneg (hω k) ENNReal.toReal_nonneg)]
  apply Finset.sum_congr rfl
  intro k _
  rw [ENNReal.ofReal_mul (hω k), measureReal_def, ENNReal.ofReal_toReal (hHfin k)]

/-- A relative floor bounds the number of disjoint counted candidates in a
single old packet. -/
theorem card_le_inv_relative_floor {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    (μ : Measure X) (U : Set X) (V : ι → Set X) (s : Finset ι) {θ : ℝ}
    (hθ : 0 < θ) (hUpos : 0 < μ.real U) (hUfin : μ U ≠ ∞)
    (hV : ∀ a ∈ s, MeasurableSet (V a) ∧ V a ⊆ U)
    (hdisj : (s : Set ι).PairwiseDisjoint V)
    (hfloor : ∀ a ∈ s, ENNReal.ofReal θ * μ U ≤ μ (V a)) :
    (s.card : ℝ) ≤ θ⁻¹ := by
  have hbudget : (∑ a ∈ s, μ.real (V a) / μ.real U) ≤ 1 := by
    simpa using normalized_assignment_budget
      (β := Unit) (fun _ => μ) (fun _ => U) (fun _ => ()) V
      (fun _ => hUpos) (fun _ => hUfin) s hV
      (fun a ha a' ha' hne _ => hdisj ha ha' hne)
  have hsum : (s.card : ℝ) * θ ≤ ∑ a ∈ s, μ.real (V a) / μ.real U := by
    calc
      (s.card : ℝ) * θ = ∑ _a ∈ s, θ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun a ha =>
        normalized_measure_floor μ U (V a) hUpos hUfin (hV a ha).2 hθ.le (hfloor a ha))
  simpa only [one_div] using (le_div_iff₀ hθ).mpr (hsum.trans hbudget)

end Submission.Obl.k4_quadratic_finite_greedy_cover
