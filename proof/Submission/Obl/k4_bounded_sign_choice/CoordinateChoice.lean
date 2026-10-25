import Submission.Obl.k4_bounded_sign_choice.PolynomialFamily
import Submission.Obl.k4_sign_projection
import Submission.Obl.k4_scalar_sign_choice

/-!
Qualitative vector choice assembled from scalar choice and coordinate projection.
All bookkeeping uses finite polynomial lists; no complexity bound is needed here.
-/

namespace Submission.Obl.k4_bounded_sign_choice.Coordinates

/-- A predicate given by the signs of finitely many real polynomials. -/
def SignDefinable {ι : Type} (S : (ι → ℝ) → Prop) : Prop :=
  ∃ (n : ℕ) (p : Fin n → MvPolynomial ι ℝ) (B : Set (Fin n → SignType)),
    ∀ x, (fun i => SignType.sign (MvPolynomial.eval x (p i))) ∈ B ↔ S x

namespace SignDefinable

theorem of_family {ι η : Type} [Fintype η]
    (p : η → MvPolynomial ι ℝ) (B : Set (η → SignType)) :
    SignDefinable (fun x => (fun i => SignType.sign (MvPolynomial.eval x (p i))) ∈ B) := by
  classical
  let e := Fintype.equivFin η
  refine ⟨Fintype.card η, fun i => p (e.symm i),
    {u | (fun j => u (e j)) ∈ B}, ?_⟩
  intro x
  simp [e]

theorem congr {ι : Type} {S T : (ι → ℝ) → Prop}
    (h : SignDefinable S) (hST : ∀ x, S x ↔ T x) : SignDefinable T := by
  obtain ⟨n, p, B, hp⟩ := h
  exact ⟨n, p, B, fun x => (hp x).trans (hST x)⟩

theorem reindex {ι κ : Type} {S : (ι → ℝ) → Prop}
    (h : SignDefinable S) (f : ι → κ) :
    SignDefinable (fun x : κ → ℝ => S (x ∘ f)) := by
  obtain ⟨n, p, B, hp⟩ := h
  refine ⟨n, fun i => MvPolynomial.rename f (p i), B, ?_⟩
  intro x
  simpa only [MvPolynomial.eval_rename] using hp (x ∘ f)

theorem and {ι : Type} {S T : (ι → ℝ) → Prop}
    (hS : SignDefinable S) (hT : SignDefinable T) :
    SignDefinable (fun x => S x ∧ T x) := by
  obtain ⟨n, p, B, hp⟩ := hS
  obtain ⟨m, q, A, hq⟩ := hT
  let r : Fin n ⊕ Fin m → MvPolynomial ι ℝ := Sum.elim p q
  let D : Set ((Fin n ⊕ Fin m) → SignType) :=
    {u | (u ∘ Sum.inl) ∈ B ∧ (u ∘ Sum.inr) ∈ A}
  apply (of_family r D).congr
  intro x
  simpa only [D, r, Set.mem_ofPred_eq, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr] using and_congr (hp x) (hq x)

theorem project {ι κ : Type} [Fintype ι] [Fintype κ]
    {S : ((ι ⊕ κ) → ℝ) → Prop} (h : SignDefinable S) :
    SignDefinable (fun x : ι → ℝ => ∃ y : κ → ℝ, S (Sum.elim x y)) := by
  obtain ⟨n, p, B, hp⟩ := h
  obtain ⟨m, q, A, hq⟩ := Submission.k4_sign_projection ι κ (Fin n) p B
  refine ⟨m, q, A, ?_⟩
  intro x
  exact (hq x).trans (exists_congr fun y => hp (Sum.elim x y))

end SignDefinable

/-- Qualitative choice for an output coordinate type. -/
def HasSignChoice (κ : Type) : Prop :=
  ∀ (ι : Type) [Fintype ι] (R : (ι → ℝ) → (κ → ℝ) → Prop),
    SignDefinable (fun z : (ι ⊕ κ) → ℝ =>
      R (fun i => z (Sum.inl i)) (fun k => z (Sum.inr k))) →
    ∃ b : (ι → ℝ) → κ → ℝ,
      SignDefinable (fun z : (ι ⊕ κ) → ℝ =>
        (∃ y, R (fun i => z (Sum.inl i)) y) ∧
          b (fun i => z (Sum.inl i)) = (fun k => z (Sum.inr k))) ∧
      ∀ x, (∃ y, R x y) → R x (b x)

theorem sum_elim_eta {ι κ : Type} (z : (ι ⊕ κ) → ℝ) :
    Sum.elim (fun i => z (Sum.inl i)) (fun k => z (Sum.inr k)) = z := by
  funext j
  cases j <;> rfl

theorem hasSignChoice_unit : HasSignChoice Unit := by
  intro ι _ R hR
  obtain ⟨m, p, B, hp⟩ := hR
  obtain ⟨b, n, g, A, hgraph, hselect⟩ :=
    Submission.k4_scalar_sign_choice ι (Fin m) p B
  have hrel (x : ι → ℝ) (t : ℝ) :
      (fun i => SignType.sign
        (MvPolynomial.eval (Sum.elim x (fun _ : Unit => t)) (p i))) ∈ B ↔
        R x (fun _ => t) := by
    simpa only [Sum.elim_inl, Sum.elim_inr] using
      hp (Sum.elim x (fun _ : Unit => t))
  have hex (x : ι → ℝ) :
      (∃ t : ℝ, (fun i => SignType.sign
        (MvPolynomial.eval (Sum.elim x (fun _ : Unit => t)) (p i))) ∈ B) ↔
        ∃ y : Unit → ℝ, R x y := by
    simp_rw [hrel]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨fun _ => t, ht⟩
    · rintro ⟨y, hy⟩
      exact ⟨y (), by simpa only [Unique.forall_iff] using hy⟩
  refine ⟨fun x _ => b x, ⟨n, g, A, ?_⟩, ?_⟩
  · intro z
    have hz : (fun _ : Unit => z (Sum.inr ())) = (fun k => z (Sum.inr k)) := by
      funext k
      cases k
      rfl
    have he : Sum.elim (fun i => z (Sum.inl i))
        (fun _ : Unit => z (Sum.inr ())) = z := by
      rw [hz, sum_elim_eta]
    rw [← he, hgraph, hex]
    simp only [Sum.elim_inl, Sum.elim_inr]
    apply and_congr_right
    intro _
    constructor
    · intro h
      funext k
      exact h
    · intro h
      exact congrFun h ()
  · intro x hx
    exact (hrel x (b x)).mp (hselect x ((hex x).mpr hx))

/-- Choose a first block and then a second block, keeping their graph conditions. -/
theorem HasSignChoice.sum {κ ν : Type} [Fintype κ] [Fintype ν]
    (hκ : HasSignChoice κ) (hν : HasSignChoice ν) : HasSignChoice (κ ⊕ ν) := by
  intro ι _ R hR
  let R' : ((ι ⊕ κ) → ℝ) → (ν → ℝ) → Prop := fun z v =>
    R (fun i => z (Sum.inl i)) (Sum.elim (fun k => z (Sum.inr k)) v)
  let assoc : (ι ⊕ (κ ⊕ ν)) → ((ι ⊕ κ) ⊕ ν) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i))
      (Sum.elim (fun k => Sum.inl (Sum.inr k)) Sum.inr)
  have hR' : SignDefinable (fun z : ((ι ⊕ κ) ⊕ ν) → ℝ =>
      R' (fun j => z (Sum.inl j)) (fun l => z (Sum.inr l))) := by
    apply (hR.reindex assoc).congr
    intro z
    dsimp [R', assoc, Function.comp_def]
    apply Iff.of_eq
    congr 1
    funext j
    cases j <;> rfl
  let U : (ι → ℝ) → (κ → ℝ) → Prop := fun x u => ∃ v, R x (Sum.elim u v)
  have hU : SignDefinable (fun z : (ι ⊕ κ) → ℝ =>
      U (fun i => z (Sum.inl i)) (fun k => z (Sum.inr k))) := hR'.project
  obtain ⟨b₁, hG₁, hs₁⟩ := hκ ι U hU
  obtain ⟨b₂, hG₂, hs₂⟩ := hν (ι ⊕ κ) R' hR'
  let b : (ι → ℝ) → (κ ⊕ ν) → ℝ := fun x =>
    Sum.elim (b₁ x) (b₂ (Sum.elim x (b₁ x)))
  have hdom (x : ι → ℝ) : (∃ u, U x u) ↔ ∃ y, R x y := by
    constructor
    · rintro ⟨u, v, hv⟩
      exact ⟨Sum.elim u v, hv⟩
    · rintro ⟨y, hy⟩
      refine ⟨fun k => y (Sum.inl k), fun l => y (Sum.inr l), ?_⟩
      simpa only [sum_elim_eta] using hy
  let forget : (ι ⊕ κ) → (ι ⊕ (κ ⊕ ν)) :=
    Sum.elim Sum.inl (fun k => Sum.inr (Sum.inl k))
  let unassoc : ((ι ⊕ κ) ⊕ ν) → (ι ⊕ (κ ⊕ ν)) :=
    Sum.elim (Sum.elim Sum.inl (fun k => Sum.inr (Sum.inl k)))
      (fun l => Sum.inr (Sum.inr l))
  refine ⟨b, ?_, ?_⟩
  · apply ((hG₁.reindex forget).and (hG₂.reindex unassoc)).congr
    intro z
    let x : ι → ℝ := fun i => z (Sum.inl i)
    let u : κ → ℝ := fun k => z (Sum.inr (Sum.inl k))
    let v : ν → ℝ := fun l => z (Sum.inr (Sum.inr l))
    have hbase : (fun j => (z ∘ unassoc) (Sum.inl j)) = Sum.elim x u := by
      funext j
      cases j <;> rfl
    rw [hbase]
    change ((∃ u', U x u') ∧ b₁ x = u) ∧
      ((∃ v', R' (Sum.elim x u) v') ∧ b₂ (Sum.elim x u) = v) ↔
      (∃ y, R x y) ∧ b x = (fun k => z (Sum.inr k))
    constructor
    · rintro ⟨⟨hx, hu⟩, ⟨_, hv⟩⟩
      refine ⟨(hdom x).mp hx, ?_⟩
      funext j
      cases j with
      | inl k => exact congrFun hu k
      | inr l =>
        change b₂ (Sum.elim x (b₁ x)) l = v l
        rw [hu]
        exact congrFun hv l
    · rintro ⟨hx, hb⟩
      have hu : b₁ x = u := by
        funext k
        exact congrFun hb (Sum.inl k)
      have hv : b₂ (Sum.elim x u) = v := by
        funext l
        have h := congrFun hb (Sum.inr l)
        change b₂ (Sum.elim x (b₁ x)) l = v l at h
        simpa only [hu] using h
      refine ⟨⟨(hdom x).mpr hx, hu⟩, ?_, hv⟩
      have hs := hs₁ x ((hdom x).mpr hx)
      rw [hu] at hs
      exact hs
  · intro x hx
    have h₁ := hs₁ x ((hdom x).mpr hx)
    have h₂ := hs₂ (Sum.elim x (b₁ x)) h₁
    exact h₂

/-- Choice is unchanged by a bijective relabeling of the output coordinates. -/
theorem HasSignChoice.equiv {κ ν : Type} (hκ : HasSignChoice κ) (e : ν ≃ κ) :
    HasSignChoice ν := by
  intro ι _ R hR
  let R' : (ι → ℝ) → (κ → ℝ) → Prop := fun x y => R x (y ∘ e)
  have hR' : SignDefinable (fun z : (ι ⊕ κ) → ℝ =>
      R' (fun i => z (Sum.inl i)) (fun k => z (Sum.inr k))) := by
    exact hR.reindex (Sum.map id e)
  obtain ⟨b, hG, hs⟩ := hκ ι R' hR'
  have hdom (x : ι → ℝ) : (∃ y, R' x y) ↔ ∃ y, R x y := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y ∘ e, hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y ∘ e.symm, by simpa [R', Function.comp_def] using hy⟩
  refine ⟨fun x => b x ∘ e, ?_, ?_⟩
  · apply (hG.reindex (Sum.map id e.symm)).congr
    intro z
    change ((∃ y, R' (fun i => z (Sum.inl i)) y) ∧
      b (fun i => z (Sum.inl i)) = (fun k => z (Sum.inr (e.symm k)))) ↔
      (∃ y, R (fun i => z (Sum.inl i)) y) ∧
        b (fun i => z (Sum.inl i)) ∘ e = (fun l => z (Sum.inr l))
    rw [hdom]
    apply and_congr_right
    intro _
    constructor
    · intro h
      funext l
      simpa only [Function.comp_def, e.symm_apply_apply] using congrFun h (e l)
    · intro h
      funext k
      simpa only [Function.comp_def, e.apply_symm_apply] using congrFun h (e.symm k)
  · intro x hx
    exact hs x ((hdom x).mpr hx)

/-- The two children suffice for the qualitative choice interface used by the
universal-coefficient family. -/
theorem qualitativeChoice_of_projection_scalar : QualitativeChoice := by
  have hthree : HasSignChoice (Unit ⊕ (Unit ⊕ Unit)) :=
    hasSignChoice_unit.sum (hasSignChoice_unit.sum hasSignChoice_unit)
  have hfin : HasSignChoice (Fin 3) :=
    hthree.equiv (Fintype.equivOfCardEq (by simp))
  intro ι η _ _ p B
  let R : (ι → ℝ) → (Fin 3 → ℝ) → Prop := SignRelation p B
  have hR : SignDefinable (fun z : (ι ⊕ Fin 3) → ℝ =>
      R (fun i => z (Sum.inl i)) (fun k => z (Sum.inr k))) := by
    apply (SignDefinable.of_family p B).congr
    intro z
    simp only [R, SignRelation, sum_elim_eta]
  obtain ⟨b, ⟨n, g, A, hgraph⟩, hs⟩ := hfin ι R hR
  refine ⟨b, n, g, A, ?_, hs⟩
  intro x y
  simpa only [Sum.elim_inl, Sum.elim_inr, SignRelation, R] using
    hgraph (Sum.elim x y)

end Submission.Obl.k4_bounded_sign_choice.Coordinates
