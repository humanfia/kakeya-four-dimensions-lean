-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.DegreeRegular.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Dyadic degree regularization of a bipartite relation

Any finite bipartite relation contains a sub-relation, on vertex sets `A' ⊆ α`,
`B' ⊆ β`, that keeps a `1/(L_A L_B)` share of the edges (`L_A = log₂ #β + 1`,
`L_B = log₂ #α + 1`) and is regular up to the factor `2 L_B` on the red side and `2`
on the blue side: every red degree times `#A'` is at most `2 L_B E'`, every blue
degree times `#B'` is at most `2 E'`. This is the extraction needed to feed degree
bounds `m dA ≤ G I`, `n dB ≤ G I` into the unbalanced four-cycle estimate.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Finset

section DegreeRegular

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (R : α → β → Prop) [DecidableRel R]

/-- Degree of a red vertex into a set of blue vertices. -/
def degInto (S : Finset β) (a : α) : ℕ := (S.filter (R a)).card

/-- Degree of a blue vertex from a set of red vertices. -/
def degFrom (T : Finset α) (b : β) : ℕ := (T.filter (fun a => R a b)).card

/-- Number of edges between a red set and a blue set. -/
def edgesBetween (T : Finset α) (S : Finset β) : ℕ := ∑ a ∈ T, degInto R S a

theorem edgesBetween_eq_sum_degFrom (T : Finset α) (S : Finset β) :
    edgesBetween R T S = ∑ b ∈ S, degFrom R T b := by
  unfold edgesBetween degInto degFrom
  simp_rw [Finset.card_filter]
  exact Finset.sum_comm

theorem degInto_mono {S S' : Finset β} (h : S ⊆ S') (a : α) :
    degInto R S a ≤ degInto R S' a :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem degInto_le_card (S : Finset β) (a : α) : degInto R S a ≤ Fintype.card β :=
  (Finset.card_le_univ _)

theorem degFrom_le_card (T : Finset α) (b : β) : degFrom R T b ≤ T.card :=
  Finset.card_filter_le _ _

/-- Dyadic pigeonhole for a weight that equals a natural-number degree: some dyadic
class of positive degrees carries a `1/(log₂ N + 1)` share of the total. -/
private theorem exists_dyadic_class {ι : Type*} (s : Finset ι) (d : ι → ℕ) (N : ℕ)
    (hd : ∀ x ∈ s, d x ≤ N) :
    ∃ k, ((∑ x ∈ s, (d x : ℝ)) / (Nat.log 2 N + 1 : ℕ)) ≤
      ∑ x ∈ s.filter (fun x => 0 < d x ∧ Nat.log 2 (d x) = k), (d x : ℝ) := by
  set s₀ := s.filter (fun x => 0 < d x)
  have hsum : (∑ x ∈ s, (d x : ℝ)) = ∑ x ∈ s₀, (d x : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : 0 < d x
    · simp [h]
    · have : d x = 0 := by omega
      simp [this]
  set t := Finset.range (Nat.log 2 N + 1)
  have hmaps : ∀ x ∈ s₀, Nat.log 2 (d x) ∈ t := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).1
    simp only [t, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (hd x hx'))
  have ht : t.Nonempty := ⟨0, by simp [t]⟩
  have hb : t.card • ((∑ x ∈ s, (d x : ℝ)) / (Nat.log 2 N + 1 : ℕ)) ≤
      ∑ x ∈ s₀, (d x : ℝ) := by
    rw [nsmul_eq_mul, Finset.card_range, ← hsum]
    have hpos : (0 : ℝ) < (Nat.log 2 N + 1 : ℕ) := by positivity
    rw [mul_div_cancel₀ _ hpos.ne']
  obtain ⟨k, -, hk⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hmaps ht hb
  refine ⟨k, hk.trans (le_of_eq ?_)⟩
  rw [Finset.filter_filter]

/-- Members of a dyadic class have degree in `[2^k, 2^(k+1))`. -/
private theorem dyadic_bounds {n k : ℕ} (hn : 0 < n) (hk : Nat.log 2 n = k) :
    2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  subst hk
  exact ⟨Nat.pow_log_le_self 2 hn.ne', Nat.lt_pow_succ_log_self (by norm_num) n⟩

/-- **Dyadic degree regularization.** -/
theorem exists_degree_regular_subgraph :
    ∃ (A' : Finset α) (B' : Finset β),
      (edgesBetween R Finset.univ Finset.univ : ℝ) ≤
        ((Nat.log 2 (Fintype.card β) + 1 : ℕ) : ℝ) *
          ((Nat.log 2 (Fintype.card α) + 1 : ℕ) : ℝ) * (edgesBetween R A' B' : ℝ) ∧
      (∀ a ∈ A', (degInto R B' a : ℝ) * (A'.card : ℝ) ≤
        2 * ((Nat.log 2 (Fintype.card α) + 1 : ℕ) : ℝ) * (edgesBetween R A' B' : ℝ)) ∧
      (∀ b ∈ B', (degFrom R A' b : ℝ) * (B'.card : ℝ) ≤ 2 * (edgesBetween R A' B' : ℝ)) := by
  set LA : ℕ := Nat.log 2 (Fintype.card β) + 1
  set LB : ℕ := Nat.log 2 (Fintype.card α) + 1
  have hLA : (0 : ℝ) < LA := by positivity
  have hLB : (0 : ℝ) < LB := by positivity
  -- red dyadic class
  obtain ⟨k, hk⟩ := exists_dyadic_class (Finset.univ : Finset α) (degInto R Finset.univ)
    (Fintype.card β) (fun a _ => degInto_le_card R _ a)
  set A₁ := (Finset.univ : Finset α).filter
    (fun a => 0 < degInto R Finset.univ a ∧ Nat.log 2 (degInto R Finset.univ a) = k)
  set E₁ : ℕ := edgesBetween R A₁ Finset.univ
  have hE₁ : (edgesBetween R Finset.univ Finset.univ : ℝ) / LA ≤ (E₁ : ℝ) := by
    have : (E₁ : ℝ) = ∑ a ∈ A₁, (degInto R Finset.univ a : ℝ) := by
      simp [E₁, edgesBetween]
    rw [this]
    have h0 : (edgesBetween R Finset.univ Finset.univ : ℝ) =
        ∑ a ∈ (Finset.univ : Finset α), (degInto R Finset.univ a : ℝ) := by
      simp [edgesBetween]
    rw [h0]
    exact hk
  have hA₁deg : ∀ a ∈ A₁, 2 ^ k ≤ degInto R Finset.univ a ∧
      degInto R Finset.univ a < 2 ^ (k + 1) := by
    intro a ha
    obtain ⟨-, hpos, hlog⟩ := Finset.mem_filter.mp ha
    exact dyadic_bounds hpos hlog
  have hA₁card : (A₁.card : ℝ) * 2 ^ k ≤ E₁ := by
    have : A₁.card * 2 ^ k ≤ E₁ := by
      calc
        A₁.card * 2 ^ k = ∑ _a ∈ A₁, 2 ^ k := by simp
        _ ≤ ∑ a ∈ A₁, degInto R Finset.univ a :=
          Finset.sum_le_sum (fun a ha => (hA₁deg a ha).1)
        _ = E₁ := rfl
    exact_mod_cast this
  -- blue dyadic class relative to A₁
  obtain ⟨j, hj⟩ := exists_dyadic_class (Finset.univ : Finset β) (degFrom R A₁)
    (Fintype.card α) (fun b _ => (degFrom_le_card R A₁ b).trans (Finset.card_le_univ _))
  set B' := (Finset.univ : Finset β).filter
    (fun b => 0 < degFrom R A₁ b ∧ Nat.log 2 (degFrom R A₁ b) = j)
  set E' : ℕ := edgesBetween R A₁ B'
  have hE'sum : (E' : ℝ) = ∑ b ∈ B', (degFrom R A₁ b : ℝ) := by
    simp only [E', edgesBetween_eq_sum_degFrom, Nat.cast_sum]
  have hE' : (E₁ : ℝ) / LB ≤ (E' : ℝ) := by
    rw [hE'sum]
    have h0 : (E₁ : ℝ) = ∑ b ∈ (Finset.univ : Finset β), (degFrom R A₁ b : ℝ) := by
      simp only [E₁, edgesBetween_eq_sum_degFrom, Nat.cast_sum]
    rw [h0]
    exact hj
  have hB'deg : ∀ b ∈ B', 2 ^ j ≤ degFrom R A₁ b ∧ degFrom R A₁ b < 2 ^ (j + 1) := by
    intro b hb
    obtain ⟨-, hpos, hlog⟩ := Finset.mem_filter.mp hb
    exact dyadic_bounds hpos hlog
  have hB'card : (B'.card : ℝ) * 2 ^ j ≤ E' := by
    rw [hE'sum]
    have : (B'.card : ℝ) * 2 ^ j = ∑ _b ∈ B', (2 : ℝ) ^ j := by simp
    rw [this]
    exact Finset.sum_le_sum (fun b hb => by exact_mod_cast (hB'deg b hb).1)
  refine ⟨A₁, B', ?_, ?_, ?_⟩
  · -- edge share
    have h1 : (edgesBetween R Finset.univ Finset.univ : ℝ) ≤ LA * E₁ := by
      rw [div_le_iff₀ hLA] at hE₁; linarith
    have h2 : (E₁ : ℝ) ≤ LB * E' := by
      rw [div_le_iff₀ hLB] at hE'; linarith
    calc
      _ ≤ (LA : ℝ) * E₁ := h1
      _ ≤ (LA : ℝ) * (LB * E') := by gcongr
      _ = _ := by ring
  · -- red side
    intro a ha
    have hdeg : (degInto R B' a : ℝ) < 2 ^ (k + 1) := by
      have := (degInto_mono R (Finset.subset_univ B') a).trans_lt (hA₁deg a ha).2
      exact_mod_cast this
    have h2 : (E₁ : ℝ) ≤ LB * E' := by
      rw [div_le_iff₀ hLB] at hE'; linarith
    have hcard0 : (0 : ℝ) ≤ A₁.card := by positivity
    calc
      (degInto R B' a : ℝ) * A₁.card ≤ 2 ^ (k + 1) * A₁.card := by gcongr
      _ = 2 * ((A₁.card : ℝ) * 2 ^ k) := by ring
      _ ≤ 2 * E₁ := by gcongr
      _ ≤ 2 * (LB * E') := by gcongr
      _ = _ := by ring
  · -- blue side
    intro b hb
    have hdeg : (degFrom R A₁ b : ℝ) < 2 ^ (j + 1) := by exact_mod_cast (hB'deg b hb).2
    calc
      (degFrom R A₁ b : ℝ) * B'.card ≤ 2 ^ (j + 1) * B'.card := by gcongr
      _ = 2 * ((B'.card : ℝ) * 2 ^ j) := by ring
      _ ≤ 2 * E' := by gcongr

/-! ### Bridges to `Fintype`-indexed relations on the extracted vertex sets -/

theorem card_subtype_rel_eq_degInto (S : Finset β) (a : α) :
    Fintype.card {b : S // R a b} = degInto R S a := by
  rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun b => b ∈ S) (R a)),
    Fintype.card_subtype]
  unfold degInto
  congr 1
  ext b
  simp

theorem card_subtype_rel_eq_degFrom (T : Finset α) (b : β) :
    Fintype.card {a : T // R a b} = degFrom R T b := by
  rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun a => a ∈ T)
    (fun a => R a b)), Fintype.card_subtype]
  unfold degFrom
  congr 1
  ext a
  simp

theorem sum_card_subtype_eq_edgesBetween (T : Finset α) (S : Finset β) :
    (∑ a : T, Fintype.card {b : S // R a b}) = edgesBetween R T S := by
  simp_rw [card_subtype_rel_eq_degInto]
  unfold edgesBetween
  exact Finset.sum_coe_sort T (degInto R S)

theorem edgesBetween_univ_eq_sum_card :
    edgesBetween R Finset.univ Finset.univ = ∑ a, Fintype.card {b // R a b} := by
  unfold edgesBetween degInto
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.card_subtype]

/-- **Regular sub-relation in the `RankedIncidence` format.** With
`L = log₂ (#α + #β) + 1`, there are vertex sets `A', B'` and natural degree bounds
`ΔA, ΔB` for the relation restricted to `A' × B'` (as finite subtypes) such that the
restricted edge count `E'` keeps a `1/L²` share of all edges and
`#A' ΔA ≤ 2 L E'`, `#B' ΔB ≤ 2 L E'`. -/
theorem exists_regular_subrelation :
    ∃ (A' : Finset α) (B' : Finset β) (ΔA ΔB : ℕ),
      (∑ a, (Fintype.card {b // R a b} : ℝ)) ≤
        ((Nat.log 2 (Fintype.card α + Fintype.card β) + 1 : ℕ) : ℝ) ^ 2 *
          (∑ a : A', (Fintype.card {b : B' // R a b} : ℝ)) ∧
      (∀ a : A', Fintype.card {b : B' // R a b} ≤ ΔA) ∧
      (∀ b : B', Fintype.card {a : A' // R a b} ≤ ΔB) ∧
      (Fintype.card A' : ℝ) * ΔA ≤
        2 * ((Nat.log 2 (Fintype.card α + Fintype.card β) + 1 : ℕ) : ℝ) *
          (∑ a : A', (Fintype.card {b : B' // R a b} : ℝ)) ∧
      (Fintype.card B' : ℝ) * ΔB ≤
        2 * ((Nat.log 2 (Fintype.card α + Fintype.card β) + 1 : ℕ) : ℝ) *
          (∑ a : A', (Fintype.card {b : B' // R a b} : ℝ)) := by
  obtain ⟨A', B', hE, hA, hB⟩ := exists_degree_regular_subgraph R
  set L : ℕ := Nat.log 2 (Fintype.card α + Fintype.card β) + 1
  set LA : ℕ := Nat.log 2 (Fintype.card β) + 1
  set LB : ℕ := Nat.log 2 (Fintype.card α) + 1
  have hLA : (LA : ℝ) ≤ L := by
    have : LA ≤ L := Nat.add_le_add_right (Nat.log_mono_right (Nat.le_add_left _ _)) 1
    exact_mod_cast this
  have hLB : (LB : ℝ) ≤ L := by
    have : LB ≤ L := Nat.add_le_add_right (Nat.log_mono_right (Nat.le_add_right _ _)) 1
    exact_mod_cast this
  have hE'eq : (∑ a : A', (Fintype.card {b : B' // R a b} : ℝ)) = edgesBetween R A' B' := by
    rw [← sum_card_subtype_eq_edgesBetween R A' B']
    push_cast
    rfl
  have hEeq : (∑ a, (Fintype.card {b // R a b} : ℝ)) = edgesBetween R Finset.univ Finset.univ := by
    rw [edgesBetween_univ_eq_sum_card]
    push_cast
    rfl
  have hE'0 : (0 : ℝ) ≤ edgesBetween R A' B' := by positivity
  refine ⟨A', B', A'.sup (degInto R B'), B'.sup (degFrom R A'), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEeq, hE'eq]
    calc
      _ ≤ (LA : ℝ) * LB * edgesBetween R A' B' := hE
      _ ≤ (L : ℝ) * L * edgesBetween R A' B' := by gcongr
      _ = _ := by ring
  · intro a
    rw [card_subtype_rel_eq_degInto]
    exact Finset.le_sup (f := degInto R B') a.2
  · intro b
    rw [card_subtype_rel_eq_degFrom]
    exact Finset.le_sup (f := degFrom R A') b.2
  · rw [hE'eq, Fintype.card_coe]
    rcases A'.eq_empty_or_nonempty with h0 | hne
    · simp [h0]; positivity
    · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup A' hne (degInto R B')
      rw [hsup, mul_comm]
      calc
        _ ≤ 2 * (LB : ℝ) * edgesBetween R A' B' := hA a ha
        _ ≤ 2 * (L : ℝ) * edgesBetween R A' B' := by gcongr
  · rw [hE'eq, Fintype.card_coe]
    rcases B'.eq_empty_or_nonempty with h0 | hne
    · simp [h0]; positivity
    · obtain ⟨b, hb, hsup⟩ := Finset.exists_mem_eq_sup B' hne (degFrom R A')
      rw [hsup, mul_comm]
      have hL1 : (1 : ℝ) ≤ L := by
        have : 1 ≤ L := Nat.le_add_left 1 _
        exact_mod_cast this
      calc
        _ ≤ 2 * (edgesBetween R A' B' : ℝ) := hB b hb
        _ = 2 * 1 * (edgesBetween R A' B' : ℝ) := by ring
        _ ≤ 2 * (L : ℝ) * edgesBetween R A' B' := by gcongr

end DegreeRegular

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
