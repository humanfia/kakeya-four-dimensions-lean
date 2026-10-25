-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/PrunedCompletion.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.ConcreteCompletion
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.CountedPruning
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.BaseCubes

/-!
# Broad completion from a pruned counted measure

`direct_of_actual_filled_group` asked for base cells `E i` and observation cells `O i` of mass at
least `mcell` inside the enlarged group.  Here both are built from the observation grid, for a
counted measure without light cells (`counted_pruning` produces one):

* `E i` are the base cubes of side `p` in which the core group `Λ` has positive counted mass
  (finitely many: the packet's incidences meet finitely many cubes, `exists_cube_finset_of_chart`);
* above each such cube some hidden bin carries positive core mass; its observation cell, cut to
  the retained lines and the block, has counted mass at least `mcell` (no light cells), and every
  incidence in it has its own intercept within `ω` of `c₀`: it shares cube and bin with a core
  incidence, whose intercept is within `ω₀` (`intercept_close_of_cell`).

The remaining inputs are those of the source: the potential with its own-intercept fits, the
quadratic replacement, per-cube breadth and the prior ceiling of the core group (on the pruned
measure), the window and the budget.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ContinuousKakeya Submission.Lib.K4ChartLifting
open scoped NNReal ENNReal

noncomputable section

/-- **Broad completion from a pruned counted measure.** -/
theorem direct_of_pruned_group {Nk L : ℝ} {W : ℕ} {ν : Fin W → Measure Ln}
    {B : Fin W → ℝ} {Mp Dp Mc : ℕ} {d₁ ρ gain ε κ : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {A : Fin C → Set Ln}
    {H : Fin W → Set Ev}
    -- the old packet and its frozen chart
    (b : Fin C) {Evs : Set Ev} {c u : P2} {Qf : Matrix (Fin 2) (Fin 2) ℝ} {Rb : Po}
    {Fb : Set Ev} {ex : Prop}
    (hch : ch Nk Mp Dp κ (T (lev b)) (j b : ℝ) (r (lev b)) (B (γ b)) Evs c u Qf Rb (A b) Fb ex)
    (hjb : j b < 2 ^ T (lev b))
    (hN : 1 ≤ Nk) (hB : 0 < B (γ b)) (hκ1 : 1 ≤ κ) (hκ : κ ≤ Nk ^ (ρ * gain * L + ε))
    (ag : ℝ) (hag : gain ≤ ag) (hag8 : ag ≤ 1 / 8) (hdepth : r (lev b) + 2 * ag * L ≤ L)
    (hagL : 0 ≤ ag * L)
    -- the potential, its own intercepts and the quadratic replacement
    (P Q₂ : MvPolynomial (Fin 3) ℝ) (hQ₂ : Q₂.totalDegree ≤ 2) (cpt : Ln → ℝ)
    (hcpt : Measurable cpt) (εfit Erep c₀ ω : ℝ)
    (Aret : Set Ln) (hAretm : MeasurableSet Aret) (hAret : Aret ⊆ A b)
    (hfit : ∀ l ∈ Aret, ∀ t ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)),
      |MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (fun i => xp l t i.castSucc) P -
        cpt l| ≤ εfit)
    (hrep : ∀ l ∈ Aret, |cpt l - c₀| ≤ ω → ∀ t ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)),
      |MvPolynomial.eval (fun i => xp l t i.castSucc) P -
        MvPolynomial.eval (fun i => xp l t i.castSucc) Q₂| ≤ Erep)
    (hcoeff : ∀ e, |(groupTest Rb Q₂ c₀).coeff e| ≤ Nk ^ Mc)
    (hvalue : εfit + ω + Erep ≤ Nk ^ (ρ * gain * L + ε) * δ Nk (r (lev b) + ag * L))
    -- the pruned counted measure: carried by retained lines, no light observation cells
    (inc : Measure Ev) [IsFiniteMeasure inc] [IsFiniteMeasure (ν (γ b))]
    (hinc : inc ≤ (((ν (γ b)).prod volume).restrict {p | p ∈ H (γ b) ∧ p ∈ Fb}))
    (hincA : inc {q | q.1 ∉ Aret} = 0)
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (mcell : ℝ≥0∞)
    (hlight : ∀ k, inc (cellIdx p (B (γ b)) a ⁻¹' {k}) = 0 ∨
      mcell ≤ inc (cellIdx p (B (γ b)) a ⁻¹' {k}))
    -- the core group
    (Λ : Set Ln) (hΛm : MeasurableSet Λ) (ω₀ : ℝ)
    (hΛ : ∀ l ∈ Λ, l ∈ Aret ∧ |cpt l - c₀| ≤ ω₀)
    (Ck ρb cb K w : ℝ) (hCk : 0 ≤ Ck) (hMK : FiniteMK 3 Ck) (hρb : 0 < ρb) (hcb : 0 ≤ cb)
    (hK : 1 ≤ K) (hw : 0 < w)
    (hbroad : ∀ n : Fin 3 → ℤ, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      cb * inc.real {ω | ω.1 ∈ Λ ∧ cubeIdx p ω = n} ≤
        (inc.restrict {ω | ω.1 ∈ Λ ∧ cubeIdx p ω = n}).real
          {ω | ρb ≤ Metric.infDist (baseDir ω.1) (V : Set _)})
    (Mg : ℝ) (hMg : 0 < Mg) (hcover : Mg ≤ inc.real {ω | ω.1 ∈ Λ})
    (hprior : (ν (γ b)).real Λ ≤ K * Mg / w)
    -- the window of the enlarged group
    (hω : ω₀ + 2 * εfit + lipBox (Rb - liftBase P) (2 * Nk ^ Mp) * (3 * p) +
      (κ * B (γ b) + lipBox (pderiv 3 Rb) (2 * Nk ^ Mp) * (3 * p)) * (a / B (γ b)) ≤ ω)
    -- the mass budget
    (hmass : ENNReal.ofReal (Nk ^ (-((d₁ * ag + ρ * gain) * L) - ε) / (2:ℝ) ^ T (lev b)) *
        ν (γ b) (A b) ≤
      ENNReal.ofReal (((ρb / 2) ^ 3 / 2 * cb ^ 3) * (w / p) ^ 3 /
        ((8 * Ck * 2 ^ 3) ^ 2 * K ^ 9)) * mcell) :
    direct Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  classical
  have hκ0 : 0 ≤ κ := by linarith
  have hNM : 1 ≤ Nk ^ Mp := one_le_pow₀ hN
  have hBx1 : (1:ℝ) ≤ 2 * Nk ^ Mp := by linarith
  set Bv := B (γ b) with hBv
  set blk : Set ℝ := Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b))
    with hblk
  have hch' := hch
  obtain ⟨_, _, _, _, hdeg, _, _, hFbm, _, hAch, hFch, _⟩ := hch'
  -- the block lies in the unit interval
  have hunit : ∀ t ∈ blk, t ∈ Icc (0:ℝ) 1 := by
    intro t ht
    have h2T : (0:ℝ) < (2:ℝ) ^ T (lev b) := by positivity
    have hj : ((j b : ℝ) + 1) ≤ (2:ℝ) ^ T (lev b) := by exact_mod_cast hjb
    refine ⟨le_trans (by positivity) ht.1, ht.2.trans ?_⟩
    rw [div_le_one h2T]; exact hj
  -- chart facts along retained lines
  have hbox : ∀ q : Ev, q.1 ∈ Aret → q.2 ∈ blk → ∀ i, |xp q.1 q.2 i| ≤ 2 * Nk ^ Mp := by
    intro q hq1 hq2 i
    rw [xp_eq_x]
    exact abs_x_le hNM (hAch q.1 (hAret hq1)).2.1 (hunit q.2 hq2) i
  have hder : ∀ q : Ev, q.1 ∈ Aret → q.2 ∈ blk →
      |MvPolynomial.eval (xp q.1 q.2) (pderiv 3 Rb)| ≤ κ * Bv := by
    intro q hq1 hq2
    rw [xp_eq_x]
    exact ((hAch q.1 (hAret hq1)).2.2 q.2 hq2).2.2.1
  -- the counted measure lives on retained incidences of the block
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
  set good : Set Ev := {q | q.1 ∈ Aret ∧ q.2 ∈ blk} with hgood
  have hgoodm : MeasurableSet good :=
    (hAretm.preimage measurable_fst).inter (measurableSet_Icc.preimage measurable_snd)
  have hnullgood : inc goodᶜ = 0 := by
    refine measure_mono_null (t := {q : Ev | q.1 ∉ Aret} ∪ Fbᶜ) ?_
      (measure_union_null hincA hnullFb)
    intro q hq
    by_cases h1 : q.1 ∈ Aret
    · right
      intro hqF
      exact hq ⟨h1, (hFch q hqF).2.2.1⟩
    · left; exact h1
  -- the cubes met by the packet and the core cubes
  obtain ⟨Sc, hSc, -⟩ := exists_cube_finset_of_chart hch hκ0 hp
  set core : (Fin 3 → ℤ) → Set Ev := fun n => {ω | ω.1 ∈ Λ ∧ cubeIdx p ω = n} with hcore
  set Ncore := Sc.filter (fun n => inc (core n) ≠ 0) with hNcore
  set e := Ncore.equivFin with he
  set nOf : Fin Ncore.card → (Fin 3 → ℤ) := fun i => (e.symm i : Fin 3 → ℤ) with hnOf
  have hnOf_inj : Function.Injective nOf := fun i i' h => e.symm.injective (Subtype.ext h)
  have hnOf_mem : ∀ i, nOf i ∈ Ncore := fun i => (e.symm i).2
  have hcore_pos : ∀ i, inc (core (nOf i)) ≠ 0 := fun i => (Finset.mem_filter.mp (hnOf_mem i)).2
  -- a hidden bin of positive core mass above each core cube
  have hbin : ∀ i, ∃ k : ℤ, inc (core (nOf i) ∩ {q | binIdx Bv a q = k}) ≠ 0 := by
    intro i
    by_contra hcon
    push Not at hcon
    apply hcore_pos i
    have : core (nOf i) = ⋃ k : ℤ, (core (nOf i) ∩ {q | binIdx Bv a q = k}) := by
      ext q; simp
    rw [this]
    exact measure_iUnion_null hcon
  choose kOf hkOf using hbin
  -- the observation cells
  set O : Fin Ncore.card → Set Ev :=
    fun i => cellIdx p Bv a ⁻¹' {(nOf i, kOf i)} ∩ good with hO
  have hcore_sub : ∀ i, core (nOf i) ∩ {q | binIdx Bv a q = kOf i} ⊆
      cellIdx p Bv a ⁻¹' {(nOf i, kOf i)} := by
    intro i q hq
    simp only [Set.mem_preimage, Set.mem_singleton_iff, cellIdx]
    exact Prod.ext hq.1.2 hq.2
  have hOm : ∀ i, MeasurableSet (O i) := fun i =>
    (measurable_cellIdx p Bv a (measurableSet_singleton _)).inter hgoodm
  have hOmass : ∀ i, mcell ≤ inc (O i) := by
    intro i
    have hpos : inc (cellIdx p Bv a ⁻¹' {(nOf i, kOf i)}) ≠ 0 := by
      intro h0
      exact hkOf i (measure_mono_null (hcore_sub i) h0)
    rcases hlight (nOf i, kOf i) with h0 | hge
    · exact absurd h0 hpos
    · rw [hO]
      simp only
      rw [measure_inter_conull hnullgood]
      exact hge
  have hOdisj : Pairwise (Function.onFun Disjoint O) := by
    intro i i' hii'
    have hn : nOf i ≠ nOf i' := fun h => hii' (hnOf_inj h)
    refine Set.disjoint_left.mpr fun q hq hq' => hn ?_
    have h1 : cellIdx p Bv a q = (nOf i, kOf i) := hq.1
    have h2 : cellIdx p Bv a q = (nOf i', kOf i') := hq'.1
    exact congrArg Prod.fst (h1.symm.trans h2)
  have hOgroup : ∀ i, ∀ q ∈ O i, q.1 ∈ Aret ∧ |cpt q.1 - c₀| ≤ ω ∧ q.2 ∈ blk := by
    intro i q hq
    obtain ⟨hqcell, hq1, hq2⟩ := hq
    refine ⟨hq1, ?_, hq2⟩
    -- a core incidence of the same cell
    have hne : (core (nOf i) ∩ {q | binIdx Bv a q = kOf i} ∩ good).Nonempty := by
      apply nonempty_of_measure_ne_zero (μ := inc)
      rw [measure_inter_conull hnullgood]
      exact hkOf i
    obtain ⟨q₀, ⟨⟨hq₀Λ, hq₀n⟩, hq₀k⟩, hq₀1, hq₀2⟩ := hne
    have hqc : cubeIdx p q = nOf i := congrArg Prod.fst hqcell
    have hqk : binIdx Bv a q = kOf i := congrArg Prod.snd hqcell
    have hcube : cubeIdx p q = cubeIdx p q₀ := hqc.trans hq₀n.symm
    have hbase : |xp q.1 q.2 0 - xp q₀.1 q₀.2 0| + |xp q.1 q.2 1 - xp q₀.1 q₀.2 1| +
        |xp q.1 q.2 2 - xp q₀.1 q₀.2 2| ≤ 3 * p := by
      have h0 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 0
      have h1 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 1
      have h2 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 2
      rw [basePoint_apply_zero, basePoint_apply_zero] at h0
      rw [basePoint_apply_one, basePoint_apply_one] at h1
      rw [basePoint_apply_two, basePoint_apply_two] at h2
      have hx0 : ∀ q : Ev, xp q.1 q.2 0 = q.2 := fun q => by simp [xp]
      rw [hx0, hx0]
      linarith
    have hhidden : |xp q.1 q.2 3 - xp q₀.1 q₀.2 3| ≤ a / Bv := by
      have hk : ⌊Bv * xp q.1 q.2 3 / a⌋ = ⌊Bv * xp q₀.1 q₀.2 3 / a⌋ := hqk.trans hq₀k.symm
      have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hk
      rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hB] at h1
      rw [div_lt_one ha] at h1
      rw [le_div_iff₀ hB]
      linarith
    have hclose := intercept_close_of_cell hdeg P cpt hBx1 (hfit q.1 hq1 q.2 hq2)
      (hfit q₀.1 hq₀1 q₀.2 hq₀2) (hbox q hq1 hq2) (hbox q₀ hq₀1 hq₀2) hbase hhidden
      (hder q hq1 hq2) (hder q₀ hq₀1 hq₀2)
    have hq₀c := (hΛ q₀.1 hq₀Λ).2
    calc |cpt q.1 - c₀| ≤ |cpt q.1 - cpt q₀.1| + |cpt q₀.1 - c₀| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hclose hq₀c
      _ ≤ ω := by
          have : lipBox (Rb - liftBase P) (2 * Nk ^ Mp) =
              (Rb - liftBase P).totalDegree * coeffL1 (Rb - liftBase P) *
                (2 * Nk ^ Mp) ^ (Rb - liftBase P).totalDegree := rfl
          have h' : lipBox (pderiv 3 Rb) (2 * Nk ^ Mp) =
              (pderiv 3 Rb).totalDegree * coeffL1 (pderiv 3 Rb) *
                (2 * Nk ^ Mp) ^ (pderiv 3 Rb).totalDegree := rfl
          rw [← this, ← h']
          linarith
  -- the base cubes
  set E : Fin Ncore.card → Set (EuclideanSpace ℝ (Fin 3)) := fun i => cubeSet p (nOf i) with hE
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
  have hΛanchor : ∀ l ∈ Λ, ‖baseAnchor0 l‖ ≤ 2 * Nk ^ Mp := by
    intro l hl
    have hlA := (hAch l (hAret (hΛ l hl).1)).2.1
    refine (norm_le_sum_abs_three _).trans ?_
    have h0 : (baseAnchor0 l) 0 = 0 := by simp [baseAnchor0]
    have h1 : (baseAnchor0 l) 1 = l.2 0 := by simp [baseAnchor0]
    have h2 : (baseAnchor0 l) 2 = l.2 1 := by simp [baseAnchor0]
    rw [h0, h1, h2, abs_zero]
    linarith [hlA 0, hlA 1]
  exact direct_of_actual_filled_group b hch hN hB hκ1 hκ ag hag hag8 hdepth hagL P Q₂ hQ₂ cpt
    hcpt εfit Erep c₀ ω Aret hAretm hAret hfit hrep hcoeff hvalue inc hinc Λ hΛm
    (2 * Nk ^ Mp) (by positivity) hΛanchor E (fun i => measurableSet_cubeSet p (nOf i)) hdisjE
    boxBound hboxE p 2 Ck ρb cb K w hp (by norm_num) hCk hMK hρb hcb hK hw
    (fun i => volume_cubeSet hp (nOf i))
    (fun i x hx y hy => dist_lt_of_mem_cubeSet hp hx hy)
    (fun i => ⟨(nOf i 0 : ℝ) * p, time_mem_of_mem_cubeSet hp (nOf i)⟩)
    hbroadE Mg hMg hcoverE hprior O hOm hOdisj mcell hOmass hOgroup hmass

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
