-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/Terminal.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.Interface

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set

/-- Closing the time block at its right endpoint does not change incidence mass. -/
theorem measure_trim_right {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (F : Set (α × ℝ)) (u : ℝ)
    (hF : ∀ p ∈ F, p.2 ≤ u) :
    (ν.prod volume) (F ∩ {p | p.2 < u}) = (ν.prod volume) F := by
  have hz : (ν.prod volume) {p : α × ℝ | p.2 = u} = 0 := by
    apply measure_mono_null (t := Set.univ ×ˢ ({u} : Set ℝ))
    · intro p hp
      exact ⟨Set.mem_univ _, hp⟩
    · apply le_antisymm _ zero_le
      exact (Measure.prod_prod_le _ _).trans_eq (by simp)
  have hne : ∀ᵐ p : α × ℝ ∂ν.prod volume, p.2 ≠ u := by
    simpa only [ae_iff, not_not] using hz
  apply measure_congr
  filter_upwards [hne] with p hp
  apply propext
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, lt_of_le_of_ne (hF p h) hp⟩

/-- Half-open time packets with disjoint assignments at each time index are disjoint. -/
theorem halfOpen_packets_disjoint {α ι : Type*}
    (A : ι → Set α) (j : ι → ℕ) (q : ℝ) (hq : 0 < q)
    (hA : ∀ b b', b ≠ b' → j b = j b' → Disjoint (A b) (A b')) :
    Pairwise (fun b b' => Disjoint
      (A b ×ˢ Ico ((j b : ℝ) / q) (((j b : ℝ) + 1) / q))
      (A b' ×ˢ Ico ((j b' : ℝ) / q) (((j b' : ℝ) + 1) / q))) := by
  intro b b' hbb'
  apply Set.disjoint_left.mpr
  intro p hp hp'
  rcases lt_trichotomy (j b) (j b') with hj | hj | hj
  · have hjR : (j b : ℝ) + 1 ≤ (j b' : ℝ) := by exact_mod_cast hj
    have hh := div_le_div_of_nonneg_right hjR hq.le
    exact (not_lt_of_ge (le_trans hh hp'.2.1)) hp.2.2
  · exact Set.disjoint_left.mp (hA b b' hbb' hj) hp.1 hp'.1
  · have hjR : (j b' : ℝ) + 1 ≤ (j b : ℝ) := by exact_mod_cast hj
    have hh := div_le_div_of_nonneg_right hjR hq.le
    exact (not_lt_of_ge (le_trans hh hp.2.1)) hp'.2.2

/-- Sum the masses of finitely many assignments separately in each world. -/
theorem weighted_assignment_union {X ι β : Type*} [MeasurableSpace X]
    [Fintype ι] [Fintype β] (μ : β → Measure X) (w : β → ENNReal)
    (P : ι → Prop) [DecidablePred P] (γ : ι → β) (F : ι → Set X)
    (hFm : ∀ b, P b → MeasurableSet (F b))
    (hdisj : ∀ b b', P b → P b' → b ≠ b' → γ b = γ b' →
      Disjoint (F b) (F b')) :
    (∑ a, w a * μ a {p | ∃ b, P b ∧ γ b = a ∧ p ∈ F b}) =
      ∑ b, if P b then w (γ b) * μ (γ b) (F b) else 0 := by
  classical
  have hm (a : β) : μ a {p | ∃ b, P b ∧ γ b = a ∧ p ∈ F b} =
      ∑ b, if P b ∧ γ b = a then μ a (F b) else 0 := by
    let s := Finset.univ.filter (fun b => P b ∧ γ b = a)
    have heq : {p | ∃ b, P b ∧ γ b = a ∧ p ∈ F b} = ⋃ b ∈ s, F b := by
      ext p
      simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_filter, Finset.mem_univ,
        true_and, s]
      aesop
    rw [heq, measure_biUnion_finset, Finset.sum_filter]
    · intro b hb b' hb' hbb'
      have hb := (Finset.mem_filter.mp hb).2
      have hb' := (Finset.mem_filter.mp hb').2
      exact hdisj b b' hb.1 hb'.1 hbb' (hb.2.trans hb'.2.symm)
    · intro b hb
      exact hFm b (Finset.mem_filter.mp hb).2.1
  simp_rw [hm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : P b
  · simp [hb, mul_ite, eq_comm]
  · simp [hb]

/-- The half-open incidence union at a fixed path level, with its world retained. -/
def levelMask {α ι β : Type*} (i T : ℕ) (lev : ι → ℕ) (γ : ι → β)
    (j : ι → ℕ) (F : ι → Set (α × ℝ)) : β → Set (α × ℝ) :=
  fun w => {p | ∃ b, lev b = i ∧ γ b = w ∧ p ∈ F b ∧
    p.2 < ((j b : ℝ) + 1) / (2 : ℝ) ^ T}

theorem levelMask_measurable {α ι β : Type*} [MeasurableSpace α] [Fintype ι]
    (i T : ℕ) (lev : ι → ℕ) (γ : ι → β) (j : ι → ℕ)
    (F : ι → Set (α × ℝ))
    (hFm : ∀ b, lev b = i → MeasurableSet (F b)) (w : β) :
    MeasurableSet (levelMask i T lev γ j F w) := by
  classical
  unfold levelMask
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro b
  by_cases hlev : lev b = i
  · by_cases hγ : γ b = w
    · simpa only [hlev, hγ, true_and, Set.inter_def, Set.mem_ofPred_eq] using
        (hFm b hlev).inter (measurableSet_lt measurable_snd measurable_const)
    · simp [hγ]
  · simp [hlev]

theorem levelMask_subset {α ι β : Type*}
    (i T : ℕ) (lev : ι → ℕ) (γ : ι → β) (j : ι → ℕ)
    (F : ι → Set (α × ℝ)) (w : β) :
    levelMask i T lev γ j F w ⊆ {p | ∃ b, lev b = i ∧ γ b = w ∧ p ∈ F b} := by
  rintro p ⟨b, hb, hγ, hp, _⟩
  exact ⟨b, hb, hγ, hp⟩

/-- The disjoint trajectory assignments and the time partition give exact mass
accounting for a level, even though the frozen charts use closed time blocks. -/
theorem levelMask_mass {α ι β : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype β]
    (ν : β → Measure α) (w : β → ENNReal)
    (i T : ℕ) (lev : ι → ℕ) (γ : ι → β) (j : ι → ℕ)
    (A : ι → Set α) (F : ι → Set (α × ℝ))
    (hFm : ∀ b, lev b = i → MeasurableSet (F b))
    (hF : ∀ b, lev b = i → ∀ p ∈ F b,
      p.1 ∈ A b ∧ p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T)
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T))
    (hA : ∀ b b', lev b = i → lev b' = i → b ≠ b' → γ b = γ b' →
      j b = j b' → Disjoint (A b) (A b')) :
    (∑ a, w a * (ν a).prod volume (levelMask i T lev γ j F a)) =
      ∑ b, if lev b = i then w (γ b) * (ν (γ b)).prod volume (F b) else 0 := by
  classical
  let G : ι → Set (α × ℝ) := fun b => F b ∩
    {p | p.2 < ((j b : ℝ) + 1) / (2 : ℝ) ^ T}
  have hGm (b : ι) (hb : lev b = i) : MeasurableSet (G b) :=
    (hFm b hb).inter (measurableSet_lt measurable_snd measurable_const)
  have hGdisj : ∀ b b', lev b = i → lev b' = i → b ≠ b' → γ b = γ b' →
      Disjoint (G b) (G b') := by
    intro b b' hb hb' hbb' hγ
    apply Set.disjoint_left.mpr
    intro p hp hp'
    have hpb := hF b hb p hp.1
    have hpb' := hF b' hb' p hp'.1
    have hq : 0 < (2 : ℝ) ^ T := by positivity
    rcases lt_trichotomy (j b) (j b') with hj | hj | hj
    · have hjR : (j b : ℝ) + 1 ≤ (j b' : ℝ) := by exact_mod_cast hj
      have hh := div_le_div_of_nonneg_right hjR hq.le
      exact (not_lt_of_ge (le_trans hh hpb'.2.1)) hp.2
    · exact Set.disjoint_left.mp (hA b b' hb hb' hbb' hγ hj) hpb.1 hpb'.1
    · have hjR : (j b' : ℝ) + 1 ≤ (j b : ℝ) := by exact_mod_cast hj
      have hh := div_le_div_of_nonneg_right hjR hq.le
      exact (not_lt_of_ge (le_trans hh hpb.2.1)) hp'.2
  have hmass := weighted_assignment_union (fun a => (ν a).prod volume) w
    (fun b => lev b = i) γ G hGm hGdisj
  change (∑ a, w a * (ν a).prod volume
    {p | ∃ b, lev b = i ∧ γ b = a ∧ p ∈ G b}) = _
  rw [hmass]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : lev b = i
  · simp only [hb, ite_true]
    rw [show (ν (γ b)).prod volume (G b) = (ν (γ b)).prod volume (F b) from
      measure_trim_right (ν (γ b)) (F b) _ (fun p hp => (hF b hb p hp).2.2)]
  · simp only [hb, ite_false]

/-- A supplied saturated path has a measurable terminal residual carrying its
full guaranteed mass. This is the initial residual for candidate discovery. -/
theorem path_terminal_residual
    (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (f : ℝ → ℝ) (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ)
    (Mp Dp : ℕ) (σ : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ)
    (κ : ℝ) (C : ℕ) (lev : Fin C → ℕ) (par : Fin C → Fin C)
    (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C))
    (hm : 0 < m)
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ
      C lev par γ j c u Q R A F lst) :
    ∃ H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (H w) ∧ H w ⊆
        {p | ∃ b : Fin C, lev b = m - 1 ∧ γ b = w ∧ p ∈ F b}) ∧
      ENNReal.ofReal κ⁻¹ ≤ ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w) := by
  classical
  rcases hp with ⟨hκ, hσ, hcount, hend, hlevels, hlists, hdisj, hnodes⟩
  have hFm : ∀ b, lev b = m - 1 → MeasurableSet (F b) := by
    intro b _
    rcases (hnodes b).2.2 with ⟨_, _, _, _, _, _, _, hFm, _⟩
    exact hFm
  have hF : ∀ b, lev b = m - 1 → ∀ p ∈ F b,
      p.1 ∈ A b ∧ p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (m - 1))
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T (m - 1)) := by
    intro b hb p hp
    rcases (hnodes b).2.2 with ⟨_, _, _, _, _, _, _, _, _, _, hF, _⟩
    have ht := (hF p hp).2.2.1
    rw [hb] at ht
    exact ⟨(hF p hp).2.1, ht⟩
  have hA : ∀ b b', lev b = m - 1 → lev b' = m - 1 → b ≠ b' →
      γ b = γ b' → j b = j b' → Disjoint (A b) (A b') := by
    intro b b' hb hb' hbb' hγ hj
    exact hdisj b b' hbb' (hb.trans hb'.symm) hγ hj
  refine ⟨levelMask (m - 1) (T (m - 1)) lev γ j F, ?_, ?_⟩
  · intro w
    exact ⟨levelMask_measurable _ _ _ _ _ _ hFm w,
      levelMask_subset _ _ _ _ _ _ w⟩
  · rw [levelMask_mass ν (fun w => ENNReal.ofReal (ω w))
      (m - 1) (T (m - 1)) lev γ j A F hFm hF hA]
    exact (hlevels (m - 1) (by omega)).2.2.2.2.2

end Submission.Obl.k4_quadratic_finite_greedy_cover
