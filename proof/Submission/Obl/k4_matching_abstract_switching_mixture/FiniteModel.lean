import Mathlib
import Submission.Obl.k4_matching_abstract_switching_mixture.TimeCells
import Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/- The finite model below adapts, from this LOT tree, o015, session x0051, branch x0051-o070,
   Submission/Obl/k4_matching_switching_target_certificate/Model.lean (own code of that session,
   no outside code): `sum_wt_filter`, `condOwn_eq_post`, `sum_bad_le`, `coarse_of_fine` are
   restated for the abstract records `F₀ F₁ Z` of o081 instead of o070's history records. -/

/-!
# The finite model of o081

`Data n₁ n₂` bundles the hypotheses of o081 that concern the event law: the arm priors,
the law `μ` on `(Fin n₁ × Fin n₂) × ℝ` with its marginal bounds, the conull set `S` of
times in `[0, 1)`, and the records `F₀ F₁ Z`, constant on the level-`H'` dyadic cells of
a fixed arm pair, with `F₁` refining `F₀` and `F₀` fixing the level-`H` interval.

At any cell depth `G ≥ H'` the finite event type is `Om n₁ n₂ G = Fin n₁ × Fin n₂ × Fin (2^G)`
with weights `D.wt G` (a probability weight).  Every cell has a representative `D.rep G ω ∈ S`,
inside its atom when its weight is positive.  The records and the palette descend to
`D.fine G`, `D.coarse G`, `D.pal G`; sums of weights over a cell-invariant predicate are
`μ`-masses (`sum_wt_filter`), so the finite conditional palette likelihoods are the frozen
ones (`condOwn_coarse`, `condOwn_fine`) and the finite bad palette mass is at most the frozen
bad mass (`sum_bad_le`).
-/

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open MeasureTheory Finset
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-- Events: an index pair and a time. -/
abbrev Ev (n₁ n₂ : ℕ) := (Fin n₁ × Fin n₂) × ℝ

/-- The finite event type at cell depth `G`. -/
abbrev Om (n₁ n₂ G : ℕ) := Fin n₁ × Fin n₂ × Fin (2 ^ G)

/-- The hypotheses of o081 on the event law and the records. -/
structure Data (n₁ n₂ : ℕ) where
  π₁ : Fin n₁ → ℝ
  π₂ : Fin n₂ → ℝ
  μ : Measure (Ev n₁ n₂)
  H : ℕ
  F₀ : Ev n₁ n₂ → ℕ
  F₁ : Ev n₁ n₂ → ℕ
  Z : Ev n₁ n₂ → ℤ × ℤ
  S : Set (Ev n₁ n₂)
  B : ℝ
  H' : ℕ
  hB : 0 ≤ B
  hπ₁ : ∀ i, 0 ≤ π₁ i
  hπ₂ : ∀ i, 0 ≤ π₂ i
  hs₁ : ∑ i, π₁ i = 1
  hs₂ : ∑ i, π₂ i = 1
  hμ : IsProbabilityMeasure μ
  hm₁ : ∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E →
    μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (B * π₁ i) * volume E
  hm₂ : ∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E →
    μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (B * π₂ i) * volume E
  hSm : MeasurableSet S
  hSc : μ Sᶜ = 0
  hSt : ∀ e ∈ S, e.2 ∈ Set.Ico (0 : ℝ) 1
  hF₁₀ : ∀ x ∈ S, ∀ y ∈ S, F₁ x = F₁ y → F₀ x = F₀ y
  hF₀H : ∀ x ∈ S, ∀ y ∈ S, F₀ x = F₀ y →
    Int.floor (x.2 * (2 : ℝ) ^ H) = Int.floor (y.2 * (2 : ℝ) ^ H)
  hHH' : H ≤ H'
  hconst : ∀ x ∈ S, ∀ y ∈ S, x.1 = y.1 →
    Int.floor (x.2 * (2 : ℝ) ^ H') = Int.floor (y.2 * (2 : ℝ) ^ H') →
      F₀ x = F₀ y ∧ F₁ x = F₁ y ∧ Z x = Z y

namespace Data

variable {n₁ n₂ : ℕ} (D : Data n₁ n₂)

/-- The frozen conditional likelihood `P F x` of the palette given the record `F`. -/
noncomputable def post (F : Ev n₁ n₂ → ℕ) (x : Ev n₁ n₂) : ℝ :=
  (D.μ {y | y ∈ D.S ∧ F y = F x ∧ D.Z y = D.Z x}).toReal /
    (D.μ {y | y ∈ D.S ∧ F y = F x}).toReal

lemma S_nonempty : D.S.Nonempty := by
  have := D.hμ
  apply nonempty_of_measure_ne_zero (μ := D.μ)
  have h1 : D.μ D.S = 1 := by
    rw [← Set.univ_inter D.S, measure_inter_conull D.hSc, measure_univ]
  rw [h1]
  exact one_ne_zero

/-- A base point of `S`. -/
noncomputable def x₀ : Ev n₁ n₂ := D.S_nonempty.some

lemma x₀_mem : D.x₀ ∈ D.S := D.S_nonempty.some_mem

/-- The weight of a cell. -/
noncomputable def wt (G : ℕ) (ω : Om n₁ n₂ G) : ℝ := cellWeight D.μ G ω

/-- The representative event of a cell. -/
noncomputable def rep (G : ℕ) (ω : Om n₁ n₂ G) : Ev n₁ n₂ := cellRep G D.S D.x₀ ω

/-- The fine record of a cell. -/
noncomputable def fine (G : ℕ) (ω : Om n₁ n₂ G) : ℕ := D.F₁ (D.rep G ω)

/-- The coarse record of a cell. -/
noncomputable def coarse (G : ℕ) (ω : Om n₁ n₂ G) : ℕ := D.F₀ (D.rep G ω)

/-- The palette of a cell. -/
noncomputable def pal (G : ℕ) (ω : Om n₁ n₂ G) : ℤ × ℤ := D.Z (D.rep G ω)

/-- The index of the level-`H` interval containing a cell. -/
def ival (G : ℕ) (ω : Om n₁ n₂ G) : ℕ := (ω.2.2 : ℕ) / 2 ^ (G - D.H)

lemma wt_nonneg (G : ℕ) (ω : Om n₁ n₂ G) : 0 ≤ D.wt G ω := cellWeight_nonneg _ _ _

lemma sum_wt (G : ℕ) : ∑ ω : Om n₁ n₂ G, D.wt G ω = 1 := by
  have := D.hμ
  exact sum_cellWeight D.μ G D.hSc D.hSt

lemma rep_mem (G : ℕ) (ω : Om n₁ n₂ G) : D.rep G ω ∈ D.S := cellRep_mem D.x₀_mem ω

lemma rep_mem_atom (G : ℕ) {ω : Om n₁ n₂ G} (hω : 0 < D.wt G ω) :
    D.rep G ω ∈ atomSet G ω :=
  cellRep_mem_atomSet D.hSc D.x₀ hω

/-- A positive cell's representative has the cell's index pair. -/
lemma rep_fst (G : ℕ) {ω : Om n₁ n₂ G} (hω : 0 < D.wt G ω) : (D.rep G ω).1 = (ω.1, ω.2.1) :=
  (D.rep_mem_atom G hω).1

lemma rep_fst_fst (G : ℕ) {ω : Om n₁ n₂ G} (hω : 0 < D.wt G ω) : (D.rep G ω).1.1 = ω.1 := by
  rw [D.rep_fst G hω]

lemma rep_fst_snd (G : ℕ) {ω : Om n₁ n₂ G} (hω : 0 < D.wt G ω) : (D.rep G ω).1.2 = ω.2.1 := by
  rw [D.rep_fst G hω]

/-- A positive cell's representative has its time in the cell. -/
lemma rep_time_mem (G : ℕ) {ω : Om n₁ n₂ G} (hω : 0 < D.wt G ω) :
    (D.rep G ω).2 ∈ cellSet G ω.2.2 :=
  (D.rep_mem_atom G hω).2

lemma rep_floor (G : ℕ) {ω : Om n₁ n₂ G} (hω : 0 < D.wt G ω) :
    Int.floor ((D.rep G ω).2 * (2 : ℝ) ^ G) = ((ω.2.2 : ℕ) : ℤ) :=
  mem_cellSet_iff.mp (D.rep_time_mem G hω)

/-- The level-`H` interval of a positive cell's representative is the cell's interval. -/
lemma rep_floor_H {G : ℕ} (hG : D.H ≤ G) {ω : Om n₁ n₂ G} (hω : 0 < D.wt G ω) :
    Int.floor ((D.rep G ω).2 * (2 : ℝ) ^ D.H) = ((D.ival G ω : ℕ) : ℤ) :=
  floor_mul_pow_of_mem_cellSet (D.rep_time_mem G hω) hG

/-- Two positive cells of the same interval index have representatives in the same
level-`H` interval. -/
lemma rep_floor_H_eq {G : ℕ} (hG : D.H ≤ G) {ω ω' : Om n₁ n₂ G} (hω : 0 < D.wt G ω)
    (hω' : 0 < D.wt G ω') (h : D.ival G ω = D.ival G ω') :
    Int.floor ((D.rep G ω).2 * (2 : ℝ) ^ D.H) = Int.floor ((D.rep G ω').2 * (2 : ℝ) ^ D.H) := by
  rw [D.rep_floor_H hG hω, D.rep_floor_H hG hω', h]

/-- On `S`, the records and the palette are constant on the level-`G` cells of an arm pair
for `G ≥ H'`. -/
lemma const_of_floor {G : ℕ} (hG : D.H' ≤ G) {x y : Ev n₁ n₂} (hx : x ∈ D.S) (hy : y ∈ D.S)
    (h1 : x.1 = y.1) (h2 : Int.floor (x.2 * (2 : ℝ) ^ G) = Int.floor (y.2 * (2 : ℝ) ^ G)) :
    D.F₀ x = D.F₀ y ∧ D.F₁ x = D.F₁ y ∧ D.Z x = D.Z y :=
  D.hconst x hx y hy h1 (floor_eq_of_floor_eq hG h2)

/-- The coarse record of a positive cell fixes its interval index. -/
lemma ival_eq_of_coarse_eq {G : ℕ} (hG : D.H ≤ G) {ω ω' : Om n₁ n₂ G} (hω : 0 < D.wt G ω)
    (hω' : 0 < D.wt G ω') (h : D.coarse G ω = D.coarse G ω') : D.ival G ω = D.ival G ω' := by
  have := D.hF₀H _ (D.rep_mem G ω) _ (D.rep_mem G ω') h
  rw [D.rep_floor_H hG hω, D.rep_floor_H hG hω'] at this
  exact_mod_cast this

/-- The coarse record is a function of the fine record on the finite model. -/
lemma coarse_of_fine (G : ℕ) : ∃ g : ℕ → ℕ, ∀ ω : Om n₁ n₂ G, D.coarse G ω = g (D.fine G ω) := by
  classical
  refine ⟨fun y => if h : ∃ x ∈ D.S, D.F₁ x = y then D.F₀ h.choose else 0, fun ω => ?_⟩
  have hex : ∃ x ∈ D.S, D.F₁ x = D.fine G ω := ⟨D.rep G ω, D.rep_mem G ω, rfl⟩
  simp only [dif_pos hex]
  obtain ⟨hxS, hxF⟩ := hex.choose_spec
  exact (D.hF₁₀ _ hxS _ (D.rep_mem G ω) hxF).symm

/-- A predicate on events is cell-invariant on `S` at depth `G`. -/
def CellInv (G : ℕ) (A : Ev n₁ n₂ → Prop) : Prop :=
  ∀ x ∈ D.S, ∀ y ∈ D.S, x.1 = y.1 →
    Int.floor (x.2 * (2 : ℝ) ^ G) = Int.floor (y.2 * (2 : ℝ) ^ G) → (A x ↔ A y)

lemma atom_null (G : ℕ) {ω : Om n₁ n₂ G} (h0 : D.wt G ω = 0) : D.μ (atomSet G ω) = 0 := by
  have := D.hμ
  rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

/-- Sums of cell weights over a cell-invariant predicate are `μ`-masses. -/
theorem sum_wt_filter (G : ℕ) (A : Ev n₁ n₂ → Prop) [DecidablePred A] (hA : D.CellInv G A) :
    ∑ ω ∈ univ.filter (fun ω : Om n₁ n₂ G => A (D.rep G ω)), D.wt G ω
      = (D.μ {y | y ∈ D.S ∧ A y}).toReal := by
  have := D.hμ
  classical
  set Gs := univ.filter (fun ω : Om n₁ n₂ G => A (D.rep G ω) ∧ 0 < D.wt G ω) with hGs
  set Z0 := univ.filter (fun ω : Om n₁ n₂ G => D.wt G ω = 0) with hZ0
  -- the weights outside `Gs` in the filter vanish
  have hsum : ∑ ω ∈ univ.filter (fun ω : Om n₁ n₂ G => A (D.rep G ω)), D.wt G ω
      = ∑ ω ∈ Gs, D.wt G ω := by
    refine (sum_subset (fun ω hω => ?_) (fun ω hω hnot => ?_)).symm
    · rw [hGs, mem_filter] at hω
      rw [mem_filter]; exact ⟨mem_univ _, hω.2.1⟩
    · rw [mem_filter] at hω
      rw [hGs, mem_filter] at hnot
      push Not at hnot
      exact le_antisymm (hnot (mem_univ _) hω.2) (D.wt_nonneg G ω)
  rw [hsum]
  -- inside a positive atom, `A` holds on `S` exactly when it holds at the representative
  have hin : ∀ ω ∈ Gs, atomSet G ω ∩ D.S ⊆ {y | y ∈ D.S ∧ A y} := by
    intro ω hω y ⟨hy1, hy2⟩
    rw [hGs, mem_filter] at hω
    have hrep := D.rep_mem_atom G hω.2.2
    exact ⟨hy2, (hA y hy2 (D.rep G ω) (D.rep_mem G ω) (hy1.1.trans hrep.1.symm)
      ((mem_cellSet_iff.mp hy1.2).trans (mem_cellSet_iff.mp hrep.2).symm)).mpr hω.2.1⟩
  have hout : {y | y ∈ D.S ∧ A y}
      ⊆ (⋃ ω ∈ Gs, atomSet G ω) ∪ ⋃ ω ∈ Z0, atomSet G ω := by
    rintro y ⟨hyS, hyA⟩
    have hcov : y ∈ ⋃ ω ∈ (univ : Finset (Om n₁ n₂ G)), atomSet G ω := by
      rw [iUnion_atomSet]; exact D.hSt y hyS
    simp only [mem_univ, Set.iUnion_true, Set.mem_iUnion] at hcov
    obtain ⟨ω, hω⟩ := hcov
    rcases (D.wt_nonneg G ω).eq_or_lt with h0 | hpos
    · right
      simp only [Set.mem_iUnion]
      exact ⟨ω, by rw [hZ0, mem_filter]; exact ⟨mem_univ _, h0.symm⟩, hω⟩
    · left
      simp only [Set.mem_iUnion]
      have hrep := D.rep_mem_atom G hpos
      refine ⟨ω, ?_, hω⟩
      rw [hGs, mem_filter]
      exact ⟨mem_univ _, (hA y hyS (D.rep G ω) (D.rep_mem G ω) (hω.1.trans hrep.1.symm)
        ((mem_cellSet_iff.mp hω.2).trans (mem_cellSet_iff.mp hrep.2).symm)).mp hyA, hpos⟩
  have hdisj : (↑Gs : Set (Om n₁ n₂ G)).PairwiseDisjoint (fun ω => atomSet G ω) :=
    fun ω _ ω' _ hne => atomSet_disjoint G hne
  have hmeasG : D.μ (⋃ ω ∈ Gs, atomSet G ω) = ∑ ω ∈ Gs, D.μ (atomSet G ω) :=
    measure_biUnion_finset hdisj fun ω _ => measurableSet_atomSet G ω
  have hnullZ : D.μ (⋃ ω ∈ Z0, atomSet G ω) = 0 := by
    refine (measure_biUnion_null_iff (Finset.countable_toSet Z0)).mpr fun ω hω => ?_
    rw [hZ0, Finset.mem_coe, mem_filter] at hω
    exact D.atom_null G hω.2
  have hup : D.μ {y | y ∈ D.S ∧ A y} ≤ ∑ ω ∈ Gs, D.μ (atomSet G ω) := by
    calc D.μ {y | y ∈ D.S ∧ A y}
        ≤ D.μ ((⋃ ω ∈ Gs, atomSet G ω) ∪ ⋃ ω ∈ Z0, atomSet G ω) := measure_mono hout
      _ ≤ D.μ (⋃ ω ∈ Gs, atomSet G ω) + D.μ (⋃ ω ∈ Z0, atomSet G ω) := measure_union_le _ _
      _ = ∑ ω ∈ Gs, D.μ (atomSet G ω) := by rw [hnullZ, add_zero, hmeasG]
  have hlow : ∑ ω ∈ Gs, D.μ (atomSet G ω) ≤ D.μ {y | y ∈ D.S ∧ A y} := by
    have hdisj' : (↑Gs : Set (Om n₁ n₂ G)).PairwiseDisjoint (fun ω => atomSet G ω ∩ D.S) :=
      fun ω _ ω' _ hne => (atomSet_disjoint G hne).mono Set.inter_subset_left
        Set.inter_subset_left
    calc ∑ ω ∈ Gs, D.μ (atomSet G ω) = ∑ ω ∈ Gs, D.μ (atomSet G ω ∩ D.S) := by
          refine sum_congr rfl fun ω _ => ?_
          rw [measure_inter_conull D.hSc]
      _ = D.μ (⋃ ω ∈ Gs, atomSet G ω ∩ D.S) :=
          (measure_biUnion_finset hdisj' fun ω _ =>
            (measurableSet_atomSet G ω).inter D.hSm).symm
      _ ≤ D.μ {y | y ∈ D.S ∧ A y} := measure_mono (Set.iUnion₂_subset hin)
  rw [le_antisymm hup hlow, ENNReal.toReal_sum (fun ω _ => measure_ne_top _ _)]
  rfl

/-- Equalities of records and palettes with a fixed value are cell-invariant. -/
lemma cellInv_record {G : ℕ} (hG : D.H' ≤ G) (x : Ev n₁ n₂) :
    D.CellInv G (fun y => D.F₀ y = D.F₀ x) ∧ D.CellInv G (fun y => D.F₁ y = D.F₁ x) ∧
      D.CellInv G (fun y => D.F₀ y = D.F₀ x ∧ D.Z y = D.Z x) ∧
      D.CellInv G (fun y => D.F₁ y = D.F₁ x ∧ D.Z y = D.Z x) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · intro y₁ hy₁ y₂ hy₂ h1 h2
    obtain ⟨e0, e1, e2⟩ := D.const_of_floor hG hy₁ hy₂ h1 h2
    simp only [e0, e1, e2]

/-- The finite conditional palette likelihood given the coarse record is the frozen one at
the representative. -/
lemma condOwn_coarse {G : ℕ} (hG : D.H' ≤ G) (ω : Om n₁ n₂ G) :
    condOwn (D.wt G) (D.pal G) (D.coarse G) ω = D.post D.F₀ (D.rep G ω) := by
  classical
  unfold condOwn atomMass fiberMass Data.post
  obtain ⟨h0, -, h2, -⟩ := D.cellInv_record hG (D.rep G ω)
  rw [← D.sum_wt_filter G _ h0, ← D.sum_wt_filter G _ h2]
  congr 1

/-- The finite conditional palette likelihood given the fine record is the frozen one at
the representative. -/
lemma condOwn_fine {G : ℕ} (hG : D.H' ≤ G) (ω : Om n₁ n₂ G) :
    condOwn (D.wt G) (D.pal G) (D.fine G) ω = D.post D.F₁ (D.rep G ω) := by
  classical
  unfold condOwn atomMass fiberMass Data.post
  obtain ⟨-, h1, -, h3⟩ := D.cellInv_record hG (D.rep G ω)
  rw [← D.sum_wt_filter G _ h1, ← D.sum_wt_filter G _ h3]
  congr 1

open Classical in
/-- **Bad palette mass.** The weight of the cells whose fine palette likelihood exceeds `c`
times the coarse one is at most the frozen exceptional mass. -/
theorem sum_bad_le {G : ℕ} (hG : D.H' ≤ G) (c : ℝ) :
    ∑ ω : Om n₁ n₂ G, D.wt G ω *
        (if condOwn (D.wt G) (D.pal G) (D.fine G) ω ≤
            c * condOwn (D.wt G) (D.pal G) (D.coarse G) ω then 0 else 1)
      ≤ (D.μ {x | x ∈ D.S ∧ c * D.post D.F₀ x < D.post D.F₁ x}).toReal := by
  have := D.hμ
  set Bad := {x | x ∈ D.S ∧ c * D.post D.F₀ x < D.post D.F₁ x} with hBad
  have hinvB : D.CellInv G (fun y => y ∈ Bad) := by
    intro y₁ hy₁ y₂ hy₂ h1 h2
    obtain ⟨e0, e1, e2⟩ := D.const_of_floor hG hy₁ hy₂ h1 h2
    have hp0 : D.post D.F₀ y₁ = D.post D.F₀ y₂ := by unfold Data.post; rw [e0, e2]
    have hp1 : D.post D.F₁ y₁ = D.post D.F₁ y₂ := by unfold Data.post; rw [e1, e2]
    simp only [hBad, Set.mem_ofPred_eq, hp0, hp1]
    exact ⟨fun h => ⟨hy₂, h.2⟩, fun h => ⟨hy₁, h.2⟩⟩
  have hterm : ∀ ω : Om n₁ n₂ G,
      D.wt G ω * (if condOwn (D.wt G) (D.pal G) (D.fine G) ω ≤
          c * condOwn (D.wt G) (D.pal G) (D.coarse G) ω then 0 else 1)
        ≤ if D.rep G ω ∈ Bad then D.wt G ω else 0 := by
    intro ω
    by_cases hg : condOwn (D.wt G) (D.pal G) (D.fine G) ω ≤
        c * condOwn (D.wt G) (D.pal G) (D.coarse G) ω
    · rw [if_pos hg, mul_zero]
      split_ifs <;> simp [D.wt_nonneg G ω]
    · rw [if_neg hg, mul_one]
      have hmem : D.rep G ω ∈ Bad := by
        refine ⟨D.rep_mem G ω, ?_⟩
        push Not at hg
        rwa [D.condOwn_coarse hG, D.condOwn_fine hG] at hg
      rw [if_pos hmem]
  calc ∑ ω : Om n₁ n₂ G, D.wt G ω *
        (if condOwn (D.wt G) (D.pal G) (D.fine G) ω ≤
            c * condOwn (D.wt G) (D.pal G) (D.coarse G) ω then 0 else 1)
      ≤ ∑ ω : Om n₁ n₂ G, (if D.rep G ω ∈ Bad then D.wt G ω else 0) :=
        sum_le_sum fun ω _ => hterm ω
    _ = ∑ ω ∈ univ.filter (fun ω : Om n₁ n₂ G => D.rep G ω ∈ Bad), D.wt G ω :=
        (sum_filter _ _).symm
    _ = (D.μ {y | y ∈ D.S ∧ y ∈ Bad}).toReal := D.sum_wt_filter G (fun y => y ∈ Bad) hinvB
    _ ≤ (D.μ Bad).toReal := ENNReal.toReal_mono (measure_ne_top _ _)
          (measure_mono fun y hy => hy.2)

/-! ### Marginals -/

/-- Per-arm time marginals bound the weights of the cells of one first index inside a
measurable time set of finite volume. -/
lemma sum_wt_fst_le_of_subset (G : ℕ) (s : Finset (Om n₁ n₂ G)) (i : Fin n₁) {E : Set ℝ}
    (hE : MeasurableSet E) (hEf : volume E ≠ ⊤) (hs : ∀ ω ∈ s, ω.1 = i ∧ cellSet G ω.2.2 ⊆ E) :
    ∑ ω ∈ s, D.wt G ω ≤ D.B * D.π₁ i * (volume E).toReal := by
  have := D.hμ
  exact sum_cellWeight_fst_le_of_subset D.μ G D.hB D.hπ₁ D.hm₁ s i hE hEf hs

/-- Per-arm time marginals bound the weights of the cells of one second index inside a
measurable time set of finite volume. -/
lemma sum_wt_snd_le_of_subset (G : ℕ) (s : Finset (Om n₁ n₂ G)) (i : Fin n₂) {E : Set ℝ}
    (hE : MeasurableSet E) (hEf : volume E ≠ ⊤)
    (hs : ∀ ω ∈ s, ω.2.1 = i ∧ cellSet G ω.2.2 ⊆ E) :
    ∑ ω ∈ s, D.wt G ω ≤ D.B * D.π₂ i * (volume E).toReal := by
  have := D.hμ
  exact sum_cellWeight_snd_le_of_subset D.μ G D.hB D.hπ₂ D.hm₂ s i hE hEf hs

lemma sum_wt_fst_le (G : ℕ) (i : Fin n₁) (c : Fin (2 ^ G)) :
    ∑ i₂ : Fin n₂, D.wt G (i, i₂, c) ≤ D.B * D.π₁ i / 2 ^ G := by
  have := D.hμ
  exact sum_cellWeight_fst_le D.μ G D.hB D.hπ₁ D.hm₁ i c

lemma sum_wt_snd_le (G : ℕ) (i : Fin n₂) (c : Fin (2 ^ G)) :
    ∑ i₁ : Fin n₁, D.wt G (i₁, i, c) ≤ D.B * D.π₂ i / 2 ^ G := by
  have := D.hμ
  exact sum_cellWeight_snd_le D.μ G D.hB D.hπ₂ D.hm₂ i c

end Data

/-- A cell meeting the `r`-neighbourhood of `t` lies in the `r + 2^-G`-neighbourhood. -/
lemma cellSet_subset_Icc {G c : ℕ} {s t r : ℝ} (hs : s ∈ cellSet G c) (h : |s - t| ≤ r) :
    cellSet G c ⊆ Set.Icc (t - (r + 1 / 2 ^ G)) (t + (r + 1 / 2 ^ G)) := by
  intro x hx
  rw [cellSet, Set.mem_Ico] at hs hx
  rw [abs_le] at h
  have e : ((c : ℝ) + 1) / 2 ^ G = (c : ℝ) / 2 ^ G + 1 / 2 ^ G := by ring
  rw [e] at hs hx
  constructor <;> linarith [hs.1, hs.2, hx.1, hx.2, h.1, h.2]

lemma volume_Icc_nbhd (t r : ℝ) (hr : 0 ≤ r) :
    (volume (Set.Icc (t - r) (t + r))).toReal = 2 * r := by
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

namespace Data

variable {n₁ n₂ : ℕ} (D : Data n₁ n₂)

/-- **Near cells, first arm.** The positive cells of a fixed first index whose
representative time is within `r` of `t` have total weight at most
`B π₁ i (2 (r + 2^-G))`. -/
lemma sum_wt_near_fst_le (G : ℕ) (s : Finset (Om n₁ n₂ G)) (i : Fin n₁) (t r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ ω ∈ s, ω.1 = i ∧ 0 < D.wt G ω ∧ |(D.rep G ω).2 - t| ≤ r) :
    ∑ ω ∈ s, D.wt G ω ≤ D.B * D.π₁ i * (2 * (r + 1 / 2 ^ G)) := by
  have hr' : 0 ≤ r + 1 / 2 ^ G := by positivity
  have h := D.sum_wt_fst_le_of_subset G s i (E := Set.Icc (t - (r + 1 / 2 ^ G))
    (t + (r + 1 / 2 ^ G))) measurableSet_Icc (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (fun ω hω => by
      obtain ⟨h1, h2, h3⟩ := hs ω hω
      exact ⟨h1, cellSet_subset_Icc (D.rep_time_mem G h2) h3⟩)
  rwa [volume_Icc_nbhd _ _ hr'] at h

/-- **Near cells, second arm.** The positive cells of a fixed second index whose
representative time is within `r` of `t` have total weight at most
`B π₂ i (2 (r + 2^-G))`. -/
lemma sum_wt_near_snd_le (G : ℕ) (s : Finset (Om n₁ n₂ G)) (i : Fin n₂) (t r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ ω ∈ s, ω.2.1 = i ∧ 0 < D.wt G ω ∧ |(D.rep G ω).2 - t| ≤ r) :
    ∑ ω ∈ s, D.wt G ω ≤ D.B * D.π₂ i * (2 * (r + 1 / 2 ^ G)) := by
  have hr' : 0 ≤ r + 1 / 2 ^ G := by positivity
  have h := D.sum_wt_snd_le_of_subset G s i (E := Set.Icc (t - (r + 1 / 2 ^ G))
    (t + (r + 1 / 2 ^ G))) measurableSet_Icc (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (fun ω hω => by
      obtain ⟨h1, h2, h3⟩ := hs ω hω
      exact ⟨h1, cellSet_subset_Icc (D.rep_time_mem G h2) h3⟩)
  rwa [volume_Icc_nbhd _ _ hr'] at h

end Data

end Submission.Obl.k4_matching_abstract_switching_mixture
