import Mathlib

-- Adapted from this LOT tree, o119 session x0401, commit e544bb8d510e3a83494159a7c65049709823455a,
-- Submission/Obl/k4_finite_width_critical_contradiction/ForestCombinatorics.lean.

/-! Elementary ancestor and mass facts for a finite layered forest. -/
namespace Submission.Obl.k4_finite_forest_width_selection

open scoped BigOperators

noncomputable def forestAncestor {C : ℕ} (lev : Fin C → ℕ)
    (par : Fin C → Fin C) (b : Fin C) (i : ℕ) : Fin C :=
  par^[lev b - i] b

theorem forest_iterate_level {C : ℕ} {lev : Fin C → ℕ}
    {par : Fin C → Fin C}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (b : Fin C) (n : ℕ) (hn : n ≤ lev b) :
    lev (par^[n] b) = lev b - n := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    have hp := hpar b (by omega)
    rw [Function.iterate_succ_apply, ih (par b) (by omega)]
    omega

theorem forestAncestor_level {C : ℕ} {lev : Fin C → ℕ}
    {par : Fin C → Fin C}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (b : Fin C) (i : ℕ) (hi : i ≤ lev b) :
    lev (forestAncestor lev par b i) = i := by
  rw [forestAncestor, forest_iterate_level hpar b _ (Nat.sub_le _ _)]
  omega

theorem forestAncestor_self {C : ℕ} (lev : Fin C → ℕ)
    (par : Fin C → Fin C) (b : Fin C) :
    forestAncestor lev par b (lev b) = b := by
  simp [forestAncestor]

theorem forestAncestor_parent {C : ℕ} {lev : Fin C → ℕ}
    {par : Fin C → Fin C}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (b : Fin C) (hb : 0 < lev b) (i : ℕ) (hi : i ≤ lev (par b)) :
    forestAncestor lev par (par b) i = forestAncestor lev par b i := by
  have hp := hpar b hb
  have hn : lev b - i = (lev (par b) - i) + 1 := by omega
  simp only [forestAncestor, hn, Function.iterate_succ_apply]

theorem forestAncestor_next {C : ℕ} {lev : Fin C → ℕ}
    {par : Fin C → Fin C} (b : Fin C) (i : ℕ) (hi : i < lev b) :
    par (forestAncestor lev par b (i + 1)) = forestAncestor lev par b i := by
  have hn : lev b - i = (lev b - (i + 1)) + 1 := by omega
  simp only [forestAncestor, hn, Function.iterate_succ_apply']

/-- The losses in the segment widths add along the actual ancestor chain. -/
theorem forest_width_lower {C : ℕ} {lev : Fin C → ℕ}
    {par : Fin C → Fin C} {width : Fin C → ℝ} {r : ℕ → ℝ} {w q : ℝ}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (hw : ∀ b, (lev b = 0 → w * r 0 - q ≤ width b) ∧
      (0 < lev b → width (par b) + w * (r (lev b) - r (lev (par b))) - q ≤ width b))
    (b : Fin C) : w * r (lev b) - ((lev b : ℝ) + 1) * q ≤ width b := by
  have aux : ∀ n (b : Fin C), lev b = n →
      w * r n - ((n : ℝ) + 1) * q ≤ width b := by
    intro n
    induction n with
    | zero =>
      intro b hb
      simpa using (hw b).1 hb
    | succ n ih =>
      intro b hb
      have hp : lev (par b) = n := by have := hpar b (by omega); omega
      have hprev := ih (par b) hp
      have hstep := (hw b).2 (by omega)
      rw [hb, hp] at hstep
      push_cast
      nlinarith only [hprev, hstep]
  exact aux (lev b) b rfl

theorem forest_width_from_ancestor {C : ℕ} {lev : Fin C → ℕ}
    {par : Fin C → Fin C} {width : Fin C → ℝ} {r : ℕ → ℝ} {w q : ℝ}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (hw : ∀ b, 0 < lev b →
      width (par b) + w * (r (lev b) - r (lev (par b))) - q ≤ width b)
    (b : Fin C) (i : ℕ) (hi : i ≤ lev b) :
    width (forestAncestor lev par b i) + w * (r (lev b) - r i) -
      ((lev b - i : ℕ) : ℝ) * q ≤ width b := by
  have aux : ∀ n : ℕ, i + n ≤ lev b →
      width (forestAncestor lev par b i) + w * (r (i + n) - r i) -
        (n : ℝ) * q ≤ width (forestAncestor lev par b (i + n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hl := forestAncestor_level hpar b (i + (n + 1)) hn
      have hs := hw (forestAncestor lev par b (i + (n + 1))) (by omega)
      have hp := forestAncestor_next (lev := lev) (par := par) b (i + n) (by omega)
      have hl' := forestAncestor_level hpar b (i + n) (by omega)
      rw [show i + (n + 1) = (i + n) + 1 by omega, hp, hl'] at hs
      rw [show lev (forestAncestor lev par b ((i + n) + 1)) = i + (n + 1) by
        simpa only [Nat.add_assoc] using hl] at hs
      simp only [Nat.add_assoc] at hs
      push_cast
      nlinarith only [hprev, hs]
  simpa only [Nat.add_sub_of_le hi, forestAncestor_self] using
    aux (lev b - i) (by omega)

/-- The retained mass cannot increase on passing to the next level when the
retained labels include all their parents and the child budgets are valid. -/
theorem forest_layer_mass_step {C : ℕ} (lev : Fin C → ℕ)
    (par : Fin C → Fin C) (mass : Fin C → ENNReal) (P : Fin C → Prop) [DecidablePred P]
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (hclosed : ∀ b, 0 < lev b → P b → P (par b))
    (hbudget : ∀ a, (∑ b, if 0 < lev b ∧ par b = a then mass b else 0) ≤ mass a)
    (i : ℕ) :
    (∑ b, if P b ∧ lev b = i + 1 then mass b else 0) ≤
      ∑ b, if P b ∧ lev b = i then mass b else 0 := by
  classical
  let child := Finset.univ.filter (fun b => P b ∧ lev b = i + 1)
  let parent := Finset.univ.filter (fun b => P b ∧ lev b = i)
  have hm : ∀ b ∈ child, par b ∈ parent := by
    intro b hb
    obtain ⟨hPb, hb⟩ := (Finset.mem_filter.mp hb).2
    have hp := hpar b (by omega)
    simp only [parent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hclosed b (by omega) hPb, by omega⟩
  have hf := Finset.sum_fiberwise_of_maps_to hm mass
  calc
    _ = ∑ b ∈ child, mass b := by simp [child, Finset.sum_filter]
    _ = ∑ a ∈ parent, ∑ b ∈ child with par b = a, mass b := hf.symm
    _ ≤ ∑ a ∈ parent, mass a := by
      apply Finset.sum_le_sum
      intro a _
      apply le_trans _ (hbudget a)
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset
      intro b hb
      obtain ⟨hb, hba⟩ := Finset.mem_filter.mp hb
      have hl := (Finset.mem_filter.mp hb).2.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by omega, hba⟩
    _ = _ := by simp [parent, Finset.sum_filter]

theorem forest_layer_mass_antitone {C : ℕ} (lev : Fin C → ℕ)
    (par : Fin C → Fin C) (mass : Fin C → ENNReal) (P : Fin C → Prop) [DecidablePred P]
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (hclosed : ∀ b, 0 < lev b → P b → P (par b))
    (hbudget : ∀ a, (∑ b, if 0 < lev b ∧ par b = a then mass b else 0) ≤ mass a) :
    Antitone (fun i => ∑ b, if P b ∧ lev b = i then mass b else 0) := by
  exact antitone_nat_of_succ_le (forest_layer_mass_step lev par mass P hpar hclosed hbudget)

/-- Bounded widths have a finite collection of common bins independent of
the number of labels and of their masses. -/
theorem finite_forest_width_bins (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ (c : Fin n → ℝ) (bin : ℝ → Fin n),
      ∀ v : ℝ, |v| ≤ M → |v - c (bin v)| ≤ ε := by
  classical
  obtain ⟨t, _, ht, hcover⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-(M : ℝ)) M)).finite_cover_balls hε
  let s := ht.toFinset
  let c := s.orderEmbOfFin rfl
  have hc : ∀ v : ℝ, |v| ≤ M → ∃ i : Fin s.card, |v - c i| ≤ ε := by
    intro v hv
    obtain ⟨x, hx, hvx⟩ := Set.mem_iUnion₂.mp (hcover (abs_le.mp hv))
    have hx' : x ∈ (s : Set ℝ) := by simpa [s] using hx
    rw [← s.range_orderEmbOfFin rfl] at hx'
    obtain ⟨i, rfl⟩ := hx'
    exact ⟨i, (by simpa only [Metric.mem_ball, Real.dist_eq] using hvx : |v - c i| < ε).le⟩
  obtain ⟨i0, _⟩ := hc 0 (by simp)
  let bin : ℝ → Fin s.card := fun v =>
    if hv : |v| ≤ M then Classical.choose (hc v hv) else i0
  refine ⟨s.card, Nat.zero_lt_of_lt i0.isLt, c, bin, ?_⟩
  intro v hv
  simpa only [bin, dif_pos hv] using Classical.choose_spec (hc v hv)

end Submission.Obl.k4_finite_forest_width_selection
