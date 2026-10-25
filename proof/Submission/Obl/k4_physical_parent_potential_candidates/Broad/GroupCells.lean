-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/GroupCells.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.PrunedCompletion

/-!
# Group cells of one sign and their counted mass

This is the mass part of the broad completion, in a form the sampled exit can use.

* `core_cube_count`: the base cubes of side `p` carrying positive counted mass of the core
  group number at least the MK3 bound `β (w/p)³ / ((64 C)² K⁹)`
  (`occupied_cells_lower_bound`, with the cubes, tubes and time-in-cell of the completion).
* `exists_sign_group_cells`: above each such cube some observation cell carries positive core
  mass, so (no light cells) counted mass at least `mcell`. Its core incidences have a hidden
  derivative of some sign `σ`. One sign class of these cells carries at least half of
  `#cubes · mcell`.

A cell is in the class `σ` when it contains a counted core incidence (retained line in the
block, in `F_b`) with `σ ∂₃R_b > 0`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ContinuousKakeya Submission.Lib.K4ChartLifting
open scoped NNReal ENNReal

noncomputable section

/-- **Core cubes.**  The cubes carrying positive core mass number at least the MK3 bound. -/
theorem core_cube_count {Nk : ℝ} {W : ℕ} {ν : Fin W → Measure Ln}
    {B : Fin W → ℝ} {Mp Dp : ℕ} {κ : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {A : Fin C → Set Ln}
    {H : Fin W → Set Ev}
    (b : Fin C) {Evs : Set Ev} {c u : P2} {Qf : Matrix (Fin 2) (Fin 2) ℝ} {Rb : Po}
    {Fb : Set Ev} {ex : Prop}
    (hch : ch Nk Mp Dp κ (T (lev b)) (j b : ℝ) (r (lev b)) (B (γ b)) Evs c u Qf Rb (A b) Fb ex)
    (hN : 1 ≤ Nk) (hκ1 : 1 ≤ κ)
    (inc : Measure Ev) [IsFiniteMeasure inc] [IsFiniteMeasure (ν (γ b))]
    (hinc : inc ≤ (((ν (γ b)).prod volume).restrict {p | p ∈ H (γ b) ∧ p ∈ Fb}))
    (Λ : Set Ln) (hΛm : MeasurableSet Λ) (hΛA : ∀ l ∈ Λ, l ∈ A b)
    (p : ℝ) (hp : 0 < p)
    (Ck ρb cb K w : ℝ) (hCk : 0 ≤ Ck) (hMK : FiniteMK 3 Ck) (hρb : 0 < ρb) (hcb : 0 ≤ cb)
    (hK : 1 ≤ K) (hw : 0 < w)
    (hbroad : ∀ n : Fin 3 → ℤ, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      cb * inc.real {ω | ω.1 ∈ Λ ∧ cubeIdx p ω = n} ≤
        (inc.restrict {ω | ω.1 ∈ Λ ∧ cubeIdx p ω = n}).real
          {ω | ρb ≤ Metric.infDist (baseDir ω.1) (V : Set _)})
    (Mg : ℝ) (hMg : 0 < Mg) (hcover : Mg ≤ inc.real {ω | ω.1 ∈ Λ})
    (hprior : (ν (γ b)).real Λ ≤ K * Mg / w) :
    ∃ Ncore : Finset (Fin 3 → ℤ),
      (∀ n ∈ Ncore, inc {ω | ω.1 ∈ Λ ∧ cubeIdx p ω = n} ≠ 0) ∧
      ((ρb / 2) ^ 3 / 2 * cb ^ 3) * (w / p) ^ 3 / ((8 * Ck * 2 ^ 3) ^ 2 * K ^ 9) ≤
        (Ncore.card : ℝ) := by
  classical
  have hκ0 : 0 ≤ κ := by linarith
  have hNM : 1 ≤ Nk ^ Mp := one_le_pow₀ hN
  have hch' := hch
  obtain ⟨_, _, _, _, _, _, _, hFbm, _, hAch, hFch, _⟩ := hch'
  -- the counted measure lives on the packet's incidences
  have hnullFb : inc Fbᶜ = 0 := by
    refine le_antisymm ?_ zero_le
    calc inc Fbᶜ ≤ (((ν (γ b)).prod volume).restrict {p | p ∈ H (γ b) ∧ p ∈ Fb}) Fbᶜ :=
          hinc _
      _ = ((ν (γ b)).prod volume) (Fbᶜ ∩ {p | p ∈ H (γ b) ∧ p ∈ Fb}) :=
          Measure.restrict_apply hFbm.compl
      _ = 0 := by
          rw [show Fbᶜ ∩ {p | p ∈ H (γ b) ∧ p ∈ Fb} = ∅ by
            ext q; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq,
              Set.mem_empty_iff_false, iff_false, not_and]
            intro h1 _ h2; exact h1 h2]
          exact measure_empty
  -- the cubes met by the packet and the core cubes
  obtain ⟨Sc, hSc, -⟩ := exists_cube_finset_of_chart hch hκ0 hp
  set core : (Fin 3 → ℤ) → Set Ev := fun n => {ω | ω.1 ∈ Λ ∧ cubeIdx p ω = n} with hcore
  set Ncore := Sc.filter (fun n => inc (core n) ≠ 0) with hNcore
  refine ⟨Ncore, fun n hn => (Finset.mem_filter.mp hn).2, ?_⟩
  set e := Ncore.equivFin with he
  set nOf : Fin Ncore.card → (Fin 3 → ℤ) := fun i => (e.symm i : Fin 3 → ℤ) with hnOf
  have hnOf_inj : Function.Injective nOf := fun i i' h => e.symm.injective (Subtype.ext h)
  have hnOf_mem : ∀ i, nOf i ∈ Ncore := fun i => (e.symm i).2
  set E : Fin Ncore.card → Set (EuclideanSpace ℝ (Fin 3)) := fun i => cubeSet p (nOf i)
    with hE
  have hset : ∀ i, {ω : Ev | ω.1 ∈ Λ ∧ basePoint ω ∈ E i} = core (nOf i) := by
    intro i; ext ω
    simp only [hE, hcore, Set.mem_ofPred_eq, basePoint_mem_cubeSet_iff]
  set boxBound : ℝ := ∑ n ∈ Sc, (|(n 0 : ℝ)| + |(n 1 : ℝ)| + |(n 2 : ℝ)| + 3) * p
    with hboxBound
  have hboxE : ∀ i, E i ⊆ Metric.closedBall 0 boxBound := by
    intro i z hz
    rw [mem_closedBall_zero_iff]
    refine (norm_le_of_mem_cubeSet hp hz).trans ?_
    exact Finset.single_le_sum (f := fun n : Fin 3 → ℤ =>
        (|(n 0 : ℝ)| + |(n 1 : ℝ)| + |(n 2 : ℝ)| + 3) * p)
      (fun n _ => by positivity) (Finset.mem_filter.mp (hnOf_mem i)).1
  have hdisjE : Pairwise (Function.onFun Disjoint E) := fun i i' hii' =>
    disjoint_cubeSet (fun h => hii' (hnOf_inj h))
  -- the core group's counted mass is spread over the core cubes
  have hcoverE : Mg ≤ ∑ i, inc.real {ω | ω.1 ∈ Λ ∧ basePoint ω ∈ E i} := by
    simp only [hset]
    refine hcover.trans ?_
    have hle : inc {ω : Ev | ω.1 ∈ Λ} ≤ ∑ n ∈ Ncore, inc (core n) := by
      have hsub : {ω : Ev | ω.1 ∈ Λ} ⊆ (⋃ n ∈ Sc, core n) ∪ Fbᶜ := by
        intro q hq
        by_cases hqF : q ∈ Fb
        · left
          exact Set.mem_iUnion₂.mpr ⟨cubeIdx p q, hSc q hqF, hq, rfl⟩
        · right; exact hqF
      calc inc {ω : Ev | ω.1 ∈ Λ} ≤ inc ((⋃ n ∈ Sc, core n) ∪ Fbᶜ) := measure_mono hsub
        _ ≤ inc (⋃ n ∈ Sc, core n) + inc Fbᶜ := measure_union_le _ _
        _ = inc (⋃ n ∈ Sc, core n) := by rw [hnullFb, add_zero]
        _ ≤ ∑ n ∈ Sc, inc (core n) := measure_biUnion_finset_le _ _
        _ = ∑ n ∈ Ncore, inc (core n) := (Finset.sum_filter_ne_zero _).symm
    have hreal : inc.real {ω : Ev | ω.1 ∈ Λ} ≤ ∑ n ∈ Ncore, inc.real (core n) := by
      rw [measureReal_def]
      simp only [measureReal_def]
      rw [← ENNReal.toReal_sum (fun n _ => measure_ne_top inc _)]
      exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun n _ => measure_ne_top inc _) hle
    refine hreal.trans (le_of_eq ?_)
    rw [← Finset.sum_coe_sort Ncore]
    exact (Equiv.sum_comp e.symm (fun x : Ncore => inc.real (core (x : Fin 3 → ℤ)))).symm
  have hbroadE : ∀ i, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      cb * inc.real {ω | ω.1 ∈ Λ ∧ basePoint ω ∈ E i} ≤
        (inc.restrict {ω | ω.1 ∈ Λ ∧ basePoint ω ∈ E i}).real
          {ω | ρb ≤ Metric.infDist (baseDir ω.1) (V : Set _)} := by
    intro i V hV
    rw [hset i]
    exact hbroad (nOf i) V hV
  -- anchors of the core group
  set Bd : ℝ := 2 * Nk ^ Mp with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  have hΛanchor : ∀ l ∈ Λ, ‖baseAnchor0 l‖ ≤ Bd := by
    intro l hl
    have hlA := (hAch l (hΛA l hl)).2.1
    refine (norm_le_sum_abs_three _).trans ?_
    have h0 : (baseAnchor0 l) 0 = 0 := by simp [baseAnchor0]
    have h1 : (baseAnchor0 l) 1 = l.2 0 := by simp [baseAnchor0]
    have h2 : (baseAnchor0 l) 2 = l.2 1 := by simp [baseAnchor0]
    rw [h0, h1, h2, abs_zero]
    linarith [hlA 0, hlA 1]
  -- tubes and time in a cube
  have htube : ∀ i, ∀ q : Ev, q.1 ∈ Λ → basePoint q ∈ E i → ∀ x ∈ E i,
      x ∈ tube (2 * p) (baseAnchor Bd q.1) (baseDir q.1) := by
    intro i q hq hqE x hx
    obtain ⟨l, t⟩ := q
    exact mem_tube_of_cell (hΛanchor l hq) hqE
      (fun x hx y hy => dist_lt_of_mem_cubeSet hp hx hy) x hx
  have hinc' : inc ≤ (ν (γ b)).prod volume := hinc.trans Measure.restrict_le_self
  have hpush : ∀ i, (inc.restrict {ω | ω.1 ∈ Λ ∧ basePoint ω ∈ E i}).map Prod.fst ≤
      (K * p).toNNReal • (ν (γ b)).restrict Λ := by
    intro i
    refine (push_le_of_time_extent (ν (γ b)) inc hinc' Λ hΛm (E i)
      (measurableSet_cubeSet p (nOf i)) p ((nOf i 0 : ℝ) * p)
      (time_mem_of_mem_cubeSet hp (nOf i))).trans ?_
    have hle : p.toNNReal ≤ (K * p).toNNReal :=
      Real.toNNReal_le_toNNReal (le_mul_of_one_le_left hp.le hK)
    intro s
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    gcongr
  have hcells := occupied_cells_lower_bound (ν (γ b)) inc basePoint measurable_basePoint
    (baseAnchor Bd) baseDir (measurable_baseAnchor Bd) measurable_baseDir norm_baseDir Bd
    (norm_baseAnchor_le hBd0) Λ hΛm E (fun i => measurableSet_cubeSet p (nOf i)) hdisjE
    boxBound hboxE p 2 Ck ρb cb K w hp (by norm_num) hCk hMK hρb hcb hK hw
    (fun i => volume_cubeSet hp (nOf i)) hpush htube hbroadE Mg hMg hcoverE hprior
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ (8 * Ck * 2 ^ 3) ^ 2 * K ^ 9 by positivity) with h | h
  · rw [← h, div_zero]; positivity
  · rw [div_le_iff₀ h]
    linarith [hcells]

open Classical in
/-- The observation cells of sign class `σ`: those containing a counted core incidence of a
retained line in the block where `σ ∂₃R_b > 0`. -/
def signCells (p Bv a : ℝ) (Λ Aret : Set Ln) (blk : Set ℝ) (Fb : Set Ev) (Rb : Po) (σ : ℝ) :
    Set ((Fin 3 → ℤ) × ℤ) :=
  {k | ∃ q : Ev, cellIdx p Bv a q = k ∧ q.1 ∈ Λ ∧ q.1 ∈ Aret ∧ q.2 ∈ blk ∧ q ∈ Fb ∧
    0 < σ * MvPolynomial.eval (xp q.1 q.2) (pderiv 3 Rb)}

/-- **A sign class of group cells carrying half the mass.** -/
theorem exists_sign_group_cells {Nk : ℝ} {W : ℕ} {ν : Fin W → Measure Ln}
    {B : Fin W → ℝ} {Mp Dp : ℕ} {κ : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {A : Fin C → Set Ln}
    {H : Fin W → Set Ev}
    (b : Fin C) {Evs : Set Ev} {c u : P2} {Qf : Matrix (Fin 2) (Fin 2) ℝ} {Rb : Po}
    {Fb : Set Ev} {ex : Prop}
    (hch : ch Nk Mp Dp κ (T (lev b)) (j b : ℝ) (r (lev b)) (B (γ b)) Evs c u Qf Rb (A b) Fb ex)
    (hN : 1 ≤ Nk) (hκ1 : 1 ≤ κ) (hB : 0 < B (γ b))
    (Aret : Set Ln) (hAret : Aret ⊆ A b)
    (inc : Measure Ev) [IsFiniteMeasure inc] [IsFiniteMeasure (ν (γ b))]
    (hinc : inc ≤ (((ν (γ b)).prod volume).restrict {p | p ∈ H (γ b) ∧ p ∈ Fb}))
    (hincA : inc {q | q.1 ∉ Aret} = 0)
    (p a : ℝ) (hp : 0 < p) (mcell : ℝ≥0∞)
    (hlight : ∀ k, inc (cellIdx p (B (γ b)) a ⁻¹' {k}) = 0 ∨
      mcell ≤ inc (cellIdx p (B (γ b)) a ⁻¹' {k}))
    (Λ : Set Ln) (hΛm : MeasurableSet Λ) (hΛA : ∀ l ∈ Λ, l ∈ Aret)
    (Ck ρb cb K w : ℝ) (hCk : 0 ≤ Ck) (hMK : FiniteMK 3 Ck) (hρb : 0 < ρb) (hcb : 0 ≤ cb)
    (hK : 1 ≤ K) (hw : 0 < w)
    (hbroad : ∀ n : Fin 3 → ℤ, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      cb * inc.real {ω | ω.1 ∈ Λ ∧ cubeIdx p ω = n} ≤
        (inc.restrict {ω | ω.1 ∈ Λ ∧ cubeIdx p ω = n}).real
          {ω | ρb ≤ Metric.infDist (baseDir ω.1) (V : Set _)})
    (Mg : ℝ) (hMg : 0 < Mg) (hcover : Mg ≤ inc.real {ω | ω.1 ∈ Λ})
    (hprior : (ν (γ b)).real Λ ≤ K * Mg / w) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧
      ENNReal.ofReal (((ρb / 2) ^ 3 / 2 * cb ^ 3) * (w / p) ^ 3 /
          ((8 * Ck * 2 ^ 3) ^ 2 * K ^ 9)) * mcell ≤
        2 * inc (cellIdx p (B (γ b)) a ⁻¹' signCells p (B (γ b)) a Λ Aret
          (Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b))) Fb Rb σ) := by
  classical
  set Bv := B (γ b) with hBv
  set blk : Set ℝ := Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b))
    with hblk
  have hch' := hch
  obtain ⟨_, _, _, _, _, _, _, hFbm, _, _, hFch, _⟩ := hch'
  obtain ⟨Ncore, hNpos, hNcard⟩ := core_cube_count b hch hN hκ1 inc hinc Λ hΛm
    (fun l hl => hAret (hΛA l hl)) p hp Ck ρb cb K w hCk hMK hρb hcb hK hw hbroad Mg hMg hcover
    hprior
  set idx := cellIdx p Bv a with hidx
  -- the counted measure lives on retained incidences of the block in `F_b`
  have hnullFb : inc Fbᶜ = 0 := by
    refine le_antisymm ?_ zero_le
    calc inc Fbᶜ ≤ (((ν (γ b)).prod volume).restrict {p | p ∈ H (γ b) ∧ p ∈ Fb}) Fbᶜ :=
          hinc _
      _ = ((ν (γ b)).prod volume) (Fbᶜ ∩ {p | p ∈ H (γ b) ∧ p ∈ Fb}) :=
          Measure.restrict_apply hFbm.compl
      _ = 0 := by
          rw [show Fbᶜ ∩ {p | p ∈ H (γ b) ∧ p ∈ Fb} = ∅ by
            ext q; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq,
              Set.mem_empty_iff_false, iff_false, not_and]
            intro h1 _ h2; exact h1 h2]
          exact measure_empty
  set good : Set Ev := {q | q.1 ∈ Aret ∧ q.2 ∈ blk ∧ q ∈ Fb} with hgood
  have hnullgood : inc goodᶜ = 0 := by
    refine measure_mono_null (t := {q : Ev | q.1 ∉ Aret} ∪ Fbᶜ) ?_
      (measure_union_null hincA hnullFb)
    intro q hq
    by_cases h1 : q.1 ∈ Aret
    · right
      intro hqF
      exact hq ⟨h1, (hFch q hqF).2.2.1, hqF⟩
    · left; exact h1
  -- above each core cube, a bin of positive core mass
  set core : (Fin 3 → ℤ) → Set Ev := fun n => {ω | ω.1 ∈ Λ ∧ cubeIdx p ω = n} with hcore
  have hbin : ∀ n ∈ Ncore, ∃ k : ℤ, inc (core n ∩ {q | binIdx Bv a q = k}) ≠ 0 := by
    intro n hn
    by_contra hcon
    push Not at hcon
    apply hNpos n hn
    change inc (core n) = 0
    have : core n = ⋃ k : ℤ, (core n ∩ {q | binIdx Bv a q = k}) := by
      ext q; simp
    rw [this]
    exact measure_iUnion_null hcon
  choose! kOf hkOf using hbin
  -- the chosen cells have a core incidence of a definite sign, and mass at least `mcell`
  have hsign : ∀ n ∈ Ncore, ∃ σ : ℝ, σ ^ 2 = 1 ∧ (n, kOf n) ∈ signCells p Bv a Λ Aret blk Fb Rb σ := by
    intro n hn
    have hne : (core n ∩ {q | binIdx Bv a q = kOf n} ∩ good).Nonempty := by
      apply nonempty_of_measure_ne_zero (μ := inc)
      rw [measure_inter_conull hnullgood]
      exact hkOf n hn
    obtain ⟨q, ⟨⟨hqΛ, hqn⟩, hqk⟩, hqA, hqt, hqF⟩ := hne
    have hder := (hFch q hqF).2.2.2
    have hd0 : MvPolynomial.eval (xp q.1 q.2) (pderiv 3 Rb) ≠ 0 := by
      intro h0
      rw [xp_eq_x] at h0
      rw [h0, abs_zero] at hder
      have : 0 < Bv / κ := by positivity
      linarith
    rcases lt_or_gt_of_ne hd0 with hlt | hgt
    · refine ⟨-1, by norm_num, q, ?_, hqΛ, hqA, hqt, hqF, by linarith⟩
      simp only [cellIdx, Prod.mk.injEq]; exact ⟨hqn, hqk⟩
    · refine ⟨1, by norm_num, q, ?_, hqΛ, hqA, hqt, hqF, by linarith⟩
      simp only [cellIdx, Prod.mk.injEq]; exact ⟨hqn, hqk⟩
  have hmass : ∀ n ∈ Ncore, mcell ≤ inc (idx ⁻¹' {(n, kOf n)}) := by
    intro n hn
    have hpos : inc (idx ⁻¹' {(n, kOf n)}) ≠ 0 := by
      intro h0
      apply hkOf n hn
      refine measure_mono_null (fun q hq => ?_) h0
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hidx, cellIdx]
      exact Prod.ext hq.1.2 hq.2
    rcases hlight (n, kOf n) with h0 | hge
    · exact absurd h0 hpos
    · exact hge
  -- the two sign classes together carry `#cubes * mcell`
  set Gs : ℝ → Set Ev := fun σ => idx ⁻¹' signCells p Bv a Λ Aret blk Fb Rb σ with hGs
  have hsum : (Ncore.card : ℝ≥0∞) * mcell ≤ inc (Gs 1) + inc (Gs (-1)) := by
    have hcells_sub : (⋃ n ∈ Ncore, idx ⁻¹' {(n, kOf n)}) ⊆ Gs 1 ∪ Gs (-1) := by
      intro q hq
      obtain ⟨n, hn, hqn⟩ := Set.mem_iUnion₂.mp hq
      obtain ⟨σ, hσ, hmem⟩ := hsign n hn
      have hq' : idx q = (n, kOf n) := hqn
      have hσ' : σ = 1 ∨ σ = -1 := by
        have : (σ - 1) * (σ + 1) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h | h
        · left; linarith
        · right; linarith
      rcases hσ' with rfl | rfl
      · left; rw [hGs]; simp only [Set.mem_preimage]; rw [hq']; exact hmem
      · right; rw [hGs]; simp only [Set.mem_preimage]; rw [hq']; exact hmem
    calc (Ncore.card : ℝ≥0∞) * mcell = ∑ _n ∈ Ncore, mcell := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Ncore, inc (idx ⁻¹' {(n, kOf n)}) := Finset.sum_le_sum hmass
      _ = inc (⋃ n ∈ Ncore, idx ⁻¹' {(n, kOf n)}) := by
          rw [measure_biUnion_finset]
          · intro n₁ _ n₂ _ hne
            refine Set.disjoint_left.mpr fun q h1 h2 => hne ?_
            have e1 : idx q = (n₁, kOf n₁) := h1
            have e2 : idx q = (n₂, kOf n₂) := h2
            exact congrArg Prod.fst (e1.symm.trans e2)
          · intro n _
            exact measurable_cellIdx p Bv a (measurableSet_singleton _)
      _ ≤ inc (Gs 1 ∪ Gs (-1)) := measure_mono hcells_sub
      _ ≤ inc (Gs 1) + inc (Gs (-1)) := measure_union_le _ _
  -- one sign class carries half
  set β₀ : ℝ := ((ρb / 2) ^ 3 / 2 * cb ^ 3) * (w / p) ^ 3 / ((8 * Ck * 2 ^ 3) ^ 2 * K ^ 9)
    with hβ₀
  have hβ₀le : ENNReal.ofReal β₀ ≤ (Ncore.card : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hNcard
  have hbase : ENNReal.ofReal β₀ * mcell ≤ inc (Gs 1) + inc (Gs (-1)) :=
    le_trans (by gcongr) hsum
  by_cases h1 : inc (Gs (-1)) ≤ inc (Gs 1)
  · refine ⟨1, by norm_num, ?_⟩
    calc ENNReal.ofReal β₀ * mcell ≤ inc (Gs 1) + inc (Gs (-1)) := hbase
      _ ≤ inc (Gs 1) + inc (Gs 1) := add_le_add le_rfl h1
      _ = 2 * inc (Gs 1) := by rw [two_mul]
  · push Not at h1
    refine ⟨-1, by norm_num, ?_⟩
    calc ENNReal.ofReal β₀ * mcell ≤ inc (Gs 1) + inc (Gs (-1)) := hbase
      _ ≤ inc (Gs (-1)) + inc (Gs (-1)) := add_le_add h1.le le_rfl
      _ = 2 * inc (Gs (-1)) := by rw [two_mul]

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
