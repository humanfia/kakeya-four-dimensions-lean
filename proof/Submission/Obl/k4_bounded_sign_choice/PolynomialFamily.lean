import Mathlib

/-!
Finite polynomial families used to pass from qualitative semialgebraic choice
to a uniform bound. Both polynomial coefficients and the accepted sign patterns
will be parameters of a single relation.
-/

namespace Submission.Obl.k4_bounded_sign_choice

open MvPolynomial

/-- A relation given by the accepted signs of a family of real polynomials. -/
def SignRelation {ι κ η : Type} (p : η → MvPolynomial (ι ⊕ κ) ℝ)
    (B : Set (η → SignType)) (x : ι → ℝ) (y : κ → ℝ) : Prop :=
  (fun i => SignType.sign (eval (Sum.elim x y) (p i))) ∈ B

/-- Qualitative choice, with no requirement on the number or degree of the graph
polynomials. Parameter spaces and input families may have arbitrary finite size. -/
def QualitativeChoice : Prop :=
  ∀ (ι η : Type) [Fintype ι] [Fintype η]
    (p : η → MvPolynomial (ι ⊕ Fin 3) ℝ) (B : Set (η → SignType)),
    ∃ (b : (ι → ℝ) → Fin 3 → ℝ) (k : ℕ)
      (g : Fin k → MvPolynomial (ι ⊕ Fin 3) ℝ) (A : Set (Fin k → SignType)),
      (∀ x y, SignRelation g A x y ↔
        (∃ z, SignRelation p B x z) ∧ b x = y) ∧
      ∀ x, (∃ y, SignRelation p B x y) → SignRelation p B x (b x)

/-- Substitution of affine polynomials does not increase total degree. -/
theorem totalDegree_eval₂_le {ι κ : Type}
    (f : ι → MvPolynomial κ ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (p : MvPolynomial ι ℝ) :
    (eval₂ C f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [eval₂_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [eval₂_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc
    ∑ i ∈ d.support, ((f i) ^ d i).totalDegree
        ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ p.totalDegree := le_totalDegree hd

/-- Fix the first block of variables and retain the other two blocks. -/
noncomputable def specialize {α ι κ : Type} (a : α → ℝ)
    (p : MvPolynomial ((α ⊕ ι) ⊕ κ) ℝ) : MvPolynomial (ι ⊕ κ) ℝ :=
  eval₂ C (Sum.elim (Sum.elim (fun j => C (a j)) (fun j => X (Sum.inl j)))
    (fun j => X (Sum.inr j))) p

theorem totalDegree_specialize_le {α ι κ : Type} (a : α → ℝ)
    (p : MvPolynomial ((α ⊕ ι) ⊕ κ) ℝ) :
    (specialize a p).totalDegree ≤ p.totalDegree := by
  apply totalDegree_eval₂_le
  rintro ((j | j) | j) <;> simp

theorem eval_specialize {α ι κ : Type} (a : α → ℝ) (x : ι → ℝ) (y : κ → ℝ)
    (p : MvPolynomial ((α ⊕ ι) ⊕ κ) ℝ) :
    eval (Sum.elim x y) (specialize a p) =
      eval (Sum.elim (Sum.elim a x) y) p := by
  apply MvPolynomial.induction_on p
  · intro r
    simp [specialize]
  · intro p q hp hq
    simpa only [specialize, eval₂_add, eval_add] using congrArg₂ (· + ·) hp hq
  · intro p j hp
    rcases j with ((j | j) | j) <;>
      simp_all [specialize, eval₂_mul, eval_mul]

/-- The bounded-degree vector space for the six geometric coordinates. -/
noncomputable abbrev PolySpace (d : ℕ) :=
  restrictTotalDegree (Fin 3 ⊕ Fin 3) ℝ d

noncomputable abbrev polyDim (d : ℕ) := Module.finrank ℝ (PolySpace d)

noncomputable def polyBasis (d : ℕ) :
    Module.Basis (Fin (polyDim d)) ℝ (PolySpace d) :=
  Module.finBasis ℝ (PolySpace d)

abbrev Pattern (m : ℕ) := Fin m → SignType

/-- Parameters for the coefficients, and for the Boolean sign predicate. -/
noncomputable abbrev Parameter (m d : ℕ) :=
  (Fin m × Fin (polyDim d)) ⊕ Pattern m

noncomputable abbrev UniversalBase (m d : ℕ) := Parameter m d ⊕ Fin 3

abbrev UniversalIndex (m : ℕ) := Fin m ⊕ Pattern m

def geometricIndex {α : Type} : (Fin 3 ⊕ Fin 3) → ((α ⊕ Fin 3) ⊕ Fin 3) :=
  Sum.elim (fun j => Sum.inl (Sum.inr j)) Sum.inr

noncomputable def parameterPolynomial {α : Type} (j : α) :
    MvPolynomial ((α ⊕ Fin 3) ⊕ Fin 3) ℝ :=
  X (Sum.inl (Sum.inl j))

/-- Each original polynomial is represented by its coordinates in a fixed
finite basis of the bounded-degree vector space. -/
noncomputable def universalOriginal (m d : ℕ) (i : Fin m) :
    MvPolynomial (UniversalBase m d ⊕ Fin 3) ℝ :=
  ∑ j : Fin (polyDim d), parameterPolynomial (Sum.inl (i, j)) *
    rename geometricIndex ((polyBasis d j : PolySpace d) : MvPolynomial _ ℝ)

noncomputable def universalPolynomials (m d : ℕ) :
    UniversalIndex m → MvPolynomial (UniversalBase m d ⊕ Fin 3) ℝ :=
  Sum.elim (universalOriginal m d) (fun σ => parameterPolynomial (Sum.inr σ))

/-- The flags for accepted sign patterns are additional polynomial signs. -/
def universalAccepted (m : ℕ) : Set (UniversalIndex m → SignType) :=
  {u | u (Sum.inr (fun i => u (Sum.inl i))) = SignType.pos}

noncomputable def parameterValue {m d : ℕ}
    (p : Fin m → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ d) (B : Set (Pattern m)) : Parameter m d → ℝ := by
  classical
  exact Sum.elim (fun ij => (polyBasis d).equivFun
    ⟨p ij.1, (mem_restrictTotalDegree _ _ _).mpr (hp ij.1)⟩ ij.2)
    (fun σ => if σ ∈ B then 1 else -1)

theorem eval_rename_geometric {α : Type} (a : α → ℝ) (s y : Fin 3 → ℝ)
    (p : MvPolynomial (Fin 3 ⊕ Fin 3) ℝ) :
    eval (Sum.elim (Sum.elim a s) y) (rename geometricIndex p) =
      eval (Sum.elim s y) p := by
  rw [eval_rename]
  apply congrArg (fun f => eval f p)
  funext i
  cases i <;> rfl

theorem eval_universalOriginal {m d : ℕ}
    (p : Fin m → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ d) (B : Set (Pattern m))
    (s y : Fin 3 → ℝ) (i : Fin m) :
    eval (Sum.elim (Sum.elim (parameterValue p hp B) s) y)
      (universalOriginal m d i) = eval (Sum.elim s y) (p i) := by
  classical
  let q : PolySpace d := ⟨p i, (mem_restrictTotalDegree _ _ _).mpr (hp i)⟩
  have h := congrArg
    (fun r : PolySpace d => eval (Sum.elim s y) (r : MvPolynomial _ ℝ))
    ((polyBasis d).sum_equivFun q)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eval] at h
  simpa only [universalOriginal, map_sum, eval_mul, parameterPolynomial, eval_X,
    Sum.elim_inl, parameterValue, eval_rename_geometric] using h

theorem universal_relation_iff {m d : ℕ}
    (p : Fin m → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ d) (B : Set (Pattern m))
    (s y : Fin 3 → ℝ) :
    SignRelation (universalPolynomials m d) (universalAccepted m)
      (Sum.elim (parameterValue p hp B) s) y ↔ SignRelation p B s y := by
  classical
  simp only [SignRelation, universalAccepted, Set.mem_ofPred_eq,
    universalPolynomials, Sum.elim_inl, Sum.elim_inr]
  simp_rw [eval_universalOriginal p hp B s y]
  simp only [parameterPolynomial, eval_X, Sum.elim_inl, parameterValue, Sum.elim_inr]
  by_cases h : (fun i => SignType.sign (eval (Sum.elim s y) (p i))) ∈ B
  · simp [h]
  · simp [h]

/-- Padding a finite polynomial list changes neither the represented relation
nor the degree bound. The added coordinates are zero and are ignored. -/
noncomputable def padFamily {ι κ : Type} {n C : ℕ}
    (g : Fin n → MvPolynomial (ι ⊕ κ) ℝ) : Fin C → MvPolynomial (ι ⊕ κ) ℝ :=
  fun j => if hj : j.val < n then g ⟨j.val, hj⟩ else 0

def padAccepted {n C : ℕ} (h : n ≤ C) (A : Set (Fin n → SignType)) :
    Set (Fin C → SignType) :=
  {u | (fun i => u ⟨i.val, lt_of_lt_of_le i.isLt h⟩) ∈ A}

theorem totalDegree_padFamily_le {ι κ : Type} {n C : ℕ}
    (g : Fin n → MvPolynomial (ι ⊕ κ) ℝ) (hg : ∀ i, (g i).totalDegree ≤ C)
    (j : Fin C) : (padFamily g j).totalDegree ≤ C := by
  classical
  dsimp [padFamily]
  split_ifs with hj
  · exact hg _
  · simp

theorem pad_relation_iff {ι κ : Type} {n C : ℕ} (h : n ≤ C)
    (g : Fin n → MvPolynomial (ι ⊕ κ) ℝ) (A : Set (Fin n → SignType))
    (x : ι → ℝ) (y : κ → ℝ) :
    SignRelation (padFamily (C := C) g) (padAccepted h A) x y ↔
      SignRelation g A x y := by
  simp [SignRelation, padAccepted, padFamily]

/-- Qualitative choice for the universal family gives a complexity bound that
depends only on the original count and degree. -/
theorem uniformChoice_of_qualitative (hchoice : QualitativeChoice) :
    ∀ m d : ℕ, ∃ C : ℕ, 0 < C ∧
      ∀ (p : Fin m → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ)
        (B : Set (Fin m → SignType)),
        (∀ i, (p i).totalDegree ≤ d) →
        ∃ (b : (Fin 3 → ℝ) → Fin 3 → ℝ)
          (g : Fin C → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ)
          (A : Set (Fin C → SignType)),
          (∀ i, (g i).totalDegree ≤ C) ∧
          (∀ s y, SignRelation g A s y ↔
            (∃ z, SignRelation p B s z) ∧ b s = y) ∧
          ∀ s, (∃ y, SignRelation p B s y) → SignRelation p B s (b s) := by
  classical
  intro m d
  obtain ⟨b, k, g, A, hgraph, hselect⟩ := hchoice (UniversalBase m d) (UniversalIndex m)
    (universalPolynomials m d) (universalAccepted m)
  let D := Finset.univ.sup (fun i : Fin k => (g i).totalDegree)
  let C := max 1 (max k D)
  have hC : 0 < C := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hkC : k ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : D ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro p B hp
  let a := parameterValue p hp B
  let b' : (Fin 3 → ℝ) → Fin 3 → ℝ := fun s => b (Sum.elim a s)
  let g' : Fin k → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ := fun i => specialize a (g i)
  have hspec (s y : Fin 3 → ℝ) :
      SignRelation g' A s y ↔ SignRelation g A (Sum.elim a s) y := by
    simp only [SignRelation, g', eval_specialize]
  refine ⟨b', padFamily (C := C) g', padAccepted hkC A, ?_, ?_, ?_⟩
  · apply totalDegree_padFamily_le
    intro i
    exact (totalDegree_specialize_le a (g i)).trans
      ((Finset.le_sup (f := fun j : Fin k => (g j).totalDegree) (Finset.mem_univ i)).trans hDC)
  · intro s y
    rw [pad_relation_iff, hspec, hgraph]
    simp only [a, universal_relation_iff p hp B]
    rfl
  · intro s hs
    have hs' : ∃ y, SignRelation (universalPolynomials m d) (universalAccepted m)
        (Sum.elim a s) y := by
      simpa only [a, universal_relation_iff p hp B] using hs
    simpa only [a, universal_relation_iff p hp B] using hselect (Sum.elim a s) hs'

/-- The uniformity reduction in the Euclidean-space formulation of o029. -/
theorem bounded_sign_choice_of_qualitative (hchoice : QualitativeChoice) :
    ∀ m d : ℕ, ∃ C : ℕ, 0 < C ∧
      ∀ (p : Fin m → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ)
        (B : Set (Fin m → SignType)),
        (∀ i, (p i).totalDegree ≤ d) →
        ∃ (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
          (g : Fin C → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ)
          (A : Set (Fin C → SignType)),
          (∀ i, (g i).totalDegree ≤ C) ∧
          (∀ s y : EuclideanSpace ℝ (Fin 3),
            SignRelation g A (fun k => s k) (fun k => y k) ↔
            (∃ z : EuclideanSpace ℝ (Fin 3),
              SignRelation p B (fun k => s k) (fun k => z k)) ∧ b s = y) ∧
          ∀ s : EuclideanSpace ℝ (Fin 3),
            (∃ y : EuclideanSpace ℝ (Fin 3),
              SignRelation p B (fun k => s k) (fun k => y k)) →
            SignRelation p B (fun k => s k) (fun k => (b s) k) := by
  intro m d
  obtain ⟨C, hC, h⟩ := uniformChoice_of_qualitative hchoice m d
  refine ⟨C, hC, ?_⟩
  intro p B hp
  obtain ⟨b, g, A, hdeg, hgraph, hselect⟩ := h p B hp
  let bE : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun s => WithLp.toLp 2 (b (fun k => s k))
  have hex (s : EuclideanSpace ℝ (Fin 3)) :
      (∃ y : Fin 3 → ℝ, SignRelation p B (fun k => s k) y) ↔
      ∃ y : EuclideanSpace ℝ (Fin 3),
        SignRelation p B (fun k => s k) (fun k => y k) := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨WithLp.toLp 2 y, hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨fun k => y k, hy⟩
  refine ⟨bE, g, A, hdeg, ?_, ?_⟩
  · intro s y
    rw [hgraph, hex]
    apply and_congr_right
    intro _
    constructor
    · intro h
      ext k
      exact congrFun h k
    · intro h
      funext k
      exact congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z k) h
  · intro s hs
    exact hselect (fun k => s k) ((hex s).mpr hs)

end Submission.Obl.k4_bounded_sign_choice
