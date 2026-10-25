/- Adapted from this LOT tree, obligation o029, session x0089, commits
2c6ac76 and 18abde3, file Submission/Obl/k4_bounded_sign_choice/SignDefinable.lean.
Namespace and imports changed to the owned o051 module. -/

import Mathlib

/-!
Elementary closure properties of sets described by finitely many polynomial
signs. Projection is isolated as a separate hypothesis.
-/

namespace Submission.Obl.k4_scalar_sign_choice

open MvPolynomial

/-- A finite polynomial sign description; no complexity bound is imposed. -/
def SignDefinable {ι : Type} (P : (ι → ℝ) → Prop) : Prop :=
  ∃ (n : ℕ) (p : Fin n → MvPolynomial ι ℝ) (B : Set (Fin n → SignType)),
    ∀ x, P x ↔ (fun i => SignType.sign (eval x (p i))) ∈ B

theorem SignDefinable.congr {ι : Type} {P Q : (ι → ℝ) → Prop}
    (hP : SignDefinable P) (h : ∀ x, P x ↔ Q x) : SignDefinable Q := by
  obtain ⟨n, p, B, hp⟩ := hP
  exact ⟨n, p, B, fun x => (h x).symm.trans (hp x)⟩

theorem SignDefinable.of_family {ι η : Type} [Fintype η]
    (p : η → MvPolynomial ι ℝ) (B : Set (η → SignType)) :
    SignDefinable (fun x => (fun i => SignType.sign (eval x (p i))) ∈ B) := by
  classical
  let e := Fintype.equivFin η
  refine ⟨Fintype.card η, (fun i => p (e.symm i)),
    {u | (fun i => u (e i)) ∈ B}, ?_⟩
  intro x
  simp

theorem SignDefinable.true {ι : Type} : SignDefinable (fun _ : ι → ℝ => True) :=
  ⟨0, fun i => Fin.elim0 i, Set.univ, fun _ => by simp⟩

theorem SignDefinable.not {ι : Type} {P : (ι → ℝ) → Prop}
    (hP : SignDefinable P) : SignDefinable (fun x => ¬P x) := by
  obtain ⟨n, p, B, hp⟩ := hP
  exact ⟨n, p, Bᶜ, fun x => (hp x).not⟩

theorem SignDefinable.and {ι : Type} {P Q : (ι → ℝ) → Prop}
    (hP : SignDefinable P) (hQ : SignDefinable Q) :
    SignDefinable (fun x => P x ∧ Q x) := by
  obtain ⟨n, p, A, hp⟩ := hP
  obtain ⟨m, q, B, hq⟩ := hQ
  apply (SignDefinable.of_family (Sum.elim p q)
    {u | (fun i => u (Sum.inl i)) ∈ A ∧ (fun j => u (Sum.inr j)) ∈ B}).congr
  intro x
  exact ((hp x).and (hq x)).symm

theorem SignDefinable.or {ι : Type} {P Q : (ι → ℝ) → Prop}
    (hP : SignDefinable P) (hQ : SignDefinable Q) :
    SignDefinable (fun x => P x ∨ Q x) :=
  (hP.not.and hQ.not).not.congr (fun _ => by tauto)

theorem SignDefinable.imp {ι : Type} {P Q : (ι → ℝ) → Prop}
    (hP : SignDefinable P) (hQ : SignDefinable Q) :
    SignDefinable (fun x => P x → Q x) :=
  (hP.not.or hQ).congr (fun _ => by tauto)

theorem SignDefinable.all_finite {ι η : Type} [Fintype η]
    {P : η → (ι → ℝ) → Prop} (hP : ∀ i, SignDefinable (P i)) :
    SignDefinable (fun x => ∀ i, P i x) := by
  classical
  choose n p B hp using hP
  apply (SignDefinable.of_family (fun j : Σ i, Fin (n i) => p j.1 j.2)
    {u | ∀ i, (fun j => u ⟨i, j⟩) ∈ B i}).congr
  intro x
  exact forall_congr' (fun i => (hp i x).symm)

theorem SignDefinable.ex_finite {ι η : Type} [Fintype η]
    {P : η → (ι → ℝ) → Prop} (hP : ∀ i, SignDefinable (P i)) :
    SignDefinable (fun x => ∃ i, P i x) :=
  (SignDefinable.all_finite (fun i => (hP i).not)).not.congr (fun _ => by simp)

theorem eval_substitution {ι κ : Type} (r : ι → MvPolynomial κ ℝ)
    (p : MvPolynomial ι ℝ) (x : κ → ℝ) :
    eval x (eval₂ C r p) = eval (fun i => eval x (r i)) p := by
  rw [eval_eval₂]
  have hC : (eval x).comp C = RingHom.id ℝ := by ext c; simp
  rw [hC, eval₂_id]

theorem SignDefinable.polynomial_precomp {ι κ : Type} {P : (ι → ℝ) → Prop}
    (hP : SignDefinable P) (r : ι → MvPolynomial κ ℝ) :
    SignDefinable (fun x => P (fun i => eval x (r i))) := by
  obtain ⟨n, p, B, hp⟩ := hP
  refine ⟨n, fun i => eval₂ C r (p i), B, ?_⟩
  intro x
  simpa only [eval_substitution] using hp (fun i => eval x (r i))

theorem SignDefinable.coordinate_precomp {ι κ : Type} {P : (ι → ℝ) → Prop}
    (hP : SignDefinable P) (f : ι → κ) : SignDefinable (fun x => P (x ∘ f)) := by
  simpa only [eval_X, Function.comp_def] using hP.polynomial_precomp (fun i => X (f i))

theorem SignDefinable.polynomial_test {ι : Type} (p : MvPolynomial ι ℝ)
    (T : Set SignType) : SignDefinable (fun x => SignType.sign (eval x p) ∈ T) := by
  simpa only [Set.mem_ofPred_eq] using
    SignDefinable.of_family (fun _ : Unit => p) {u | u () ∈ T}

theorem SignDefinable.polynomial_eq {ι : Type} (p q : MvPolynomial ι ℝ) :
    SignDefinable (fun x => eval x p = eval x q) := by
  simpa only [Set.mem_singleton_iff, sign_eq_zero_iff, eval_sub, sub_eq_zero] using
    SignDefinable.polynomial_test (p - q) {0}

theorem SignDefinable.polynomial_lt {ι : Type} (p q : MvPolynomial ι ℝ) :
    SignDefinable (fun x => eval x p < eval x q) := by
  simpa only [Set.mem_singleton_iff, sign_eq_one_iff, eval_sub, sub_pos] using
    SignDefinable.polynomial_test (q - p) {1}

theorem SignDefinable.polynomial_le {ι : Type} (p q : MvPolynomial ι ℝ) :
    SignDefinable (fun x => eval x p ≤ eval x q) :=
  (SignDefinable.polynomial_lt q p).not.congr (fun _ => not_lt)

/-- Qualitative real projection for finite-dimensional sign sets. -/
def SignProjection : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (P : ((ι ⊕ κ) → ℝ) → Prop),
    SignDefinable P → SignDefinable (fun x => ∃ y : κ → ℝ, P (Sum.elim x y))

/-- A bridge from the fully expanded sign-family projection statement. -/
theorem signProjection_of_family_projection
    (hproj : ∀ (ι κ η : Type) [Fintype ι] [Fintype κ] [Fintype η]
      (p : η → MvPolynomial (ι ⊕ κ) ℝ) (B : Set (η → SignType)),
      ∃ (n : ℕ) (q : Fin n → MvPolynomial ι ℝ) (A : Set (Fin n → SignType)),
        ∀ x : ι → ℝ, (fun i => SignType.sign (eval x (q i))) ∈ A ↔
          ∃ y : κ → ℝ, (fun i => SignType.sign (eval (Sum.elim x y) (p i))) ∈ B) :
    SignProjection := by
  intro ι κ _ _ P hP
  obtain ⟨m, p, B, hp⟩ := hP
  obtain ⟨n, q, A, hq⟩ := hproj ι κ (Fin m) p B
  refine ⟨n, q, A, ?_⟩
  intro x
  exact (exists_congr (fun y => hp (Sum.elim x y))).trans (hq x).symm

theorem SignDefinable.exists_block (hproj : SignProjection) {ι κ : Type}
    [Fintype ι] [Fintype κ] {P : ((ι ⊕ κ) → ℝ) → Prop} (hP : SignDefinable P) :
    SignDefinable (fun x => ∃ y : κ → ℝ, P (Sum.elim x y)) :=
  hproj ι κ P hP

theorem SignDefinable.forall_block (hproj : SignProjection) {ι κ : Type}
    [Fintype ι] [Fintype κ] {P : ((ι ⊕ κ) → ℝ) → Prop} (hP : SignDefinable P) :
    SignDefinable (fun x => ∀ y : κ → ℝ, P (Sum.elim x y)) :=
  (hP.not.exists_block hproj).not.congr (fun _ => by simp)

theorem SignDefinable.exists_real (hproj : SignProjection) {ι : Type} [Fintype ι]
    {P : ((ι ⊕ Unit) → ℝ) → Prop} (hP : SignDefinable P) :
    SignDefinable (fun x => ∃ t : ℝ, P (Sum.elim x (fun _ => t))) := by
  apply (hP.exists_block hproj).congr
  intro x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y (), ?_⟩
    convert hy using 1
  · rintro ⟨t, ht⟩
    exact ⟨fun _ => t, ht⟩

theorem SignDefinable.forall_real (hproj : SignProjection) {ι : Type} [Fintype ι]
    {P : ((ι ⊕ Unit) → ℝ) → Prop} (hP : SignDefinable P) :
    SignDefinable (fun x => ∀ t : ℝ, P (Sum.elim x (fun _ => t))) :=
  (hP.not.exists_real hproj).not.congr (fun _ => by simp)

end Submission.Obl.k4_scalar_sign_choice
