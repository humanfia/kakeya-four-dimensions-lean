import Mathlib

namespace Submission.Obl.k4_sign_projection

/-- A finite family of polynomial signs determines the value of a function. -/
def SignDetermined {ι α : Type} (f : (ι → ℝ) → α) : Prop :=
  ∃ (η : Type) (_ : Fintype η) (p : η → MvPolynomial ι ℝ),
    ∀ x y, (∀ i, SignType.sign (MvPolynomial.eval x (p i)) =
      SignType.sign (MvPolynomial.eval y (p i))) → f x = f y

/-- On every cell of a finite polynomial sign partition, a scalar function is rational,
with a denominator that never vanishes on that cell. -/
def RationalCells {ι : Type} (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ (η : Type) (_ : Fintype η) (p : η → MvPolynomial ι ℝ),
    ∀ s : η → SignType, ∃ N D : MvPolynomial ι ℝ,
      ∀ x, (∀ i, SignType.sign (MvPolynomial.eval x (p i)) = s i) →
        MvPolynomial.eval x D ≠ 0 ∧ f x = MvPolynomial.eval x N / MvPolynomial.eval x D

variable {ι α β : Type}

lemma RationalCells.polynomial (p : MvPolynomial ι ℝ) :
    RationalCells (fun x => MvPolynomial.eval x p) := by
  refine ⟨Empty, inferInstance, Empty.elim, fun _ => ⟨p, 1, ?_⟩⟩
  intro x _
  simp

lemma RationalCells.add {f g : (ι → ℝ) → ℝ} (hf : RationalCells f) (hg : RationalCells g) :
    RationalCells (fun x => f x + g x) := by
  classical
  obtain ⟨η, hη, p, hp⟩ := hf
  obtain ⟨κ, hκ, q, hq⟩ := hg
  let := hη
  let := hκ
  refine ⟨η ⊕ κ, inferInstance, Sum.elim p q, ?_⟩
  intro s
  obtain ⟨N, D, hN⟩ := hp (fun i => s (Sum.inl i))
  obtain ⟨M, E, hM⟩ := hq (fun i => s (Sum.inr i))
  refine ⟨N * E + M * D, D * E, ?_⟩
  intro x hx
  obtain ⟨hD, hf⟩ := hN x (fun i => hx (Sum.inl i))
  obtain ⟨hE, hg⟩ := hM x (fun i => hx (Sum.inr i))
  refine ⟨by simpa only [map_mul] using mul_ne_zero hD hE, ?_⟩
  dsimp only
  rw [hf, hg, map_add, map_mul, map_mul, map_mul]
  simpa only [mul_comm (MvPolynomial.eval x D) (MvPolynomial.eval x M)] using
    div_add_div (MvPolynomial.eval x N) (MvPolynomial.eval x M) hD hE

lemma RationalCells.mul {f g : (ι → ℝ) → ℝ} (hf : RationalCells f) (hg : RationalCells g) :
    RationalCells (fun x => f x * g x) := by
  classical
  obtain ⟨η, hη, p, hp⟩ := hf
  obtain ⟨κ, hκ, q, hq⟩ := hg
  let := hη
  let := hκ
  refine ⟨η ⊕ κ, inferInstance, Sum.elim p q, ?_⟩
  intro s
  obtain ⟨N, D, hN⟩ := hp (fun i => s (Sum.inl i))
  obtain ⟨M, E, hM⟩ := hq (fun i => s (Sum.inr i))
  refine ⟨N * M, D * E, ?_⟩
  intro x hx
  obtain ⟨hD, hf⟩ := hN x (fun i => hx (Sum.inl i))
  obtain ⟨hE, hg⟩ := hM x (fun i => hx (Sum.inr i))
  refine ⟨by simpa only [map_mul] using mul_ne_zero hD hE, ?_⟩
  dsimp only
  rw [hf, hg, map_mul, map_mul, div_mul_div_comm]

lemma RationalCells.neg {f : (ι → ℝ) → ℝ} (hf : RationalCells f) :
    RationalCells (fun x => -f x) := by
  obtain ⟨η, hη, p, hp⟩ := hf
  refine ⟨η, hη, p, ?_⟩
  intro s
  obtain ⟨N, D, hN⟩ := hp s
  refine ⟨-N, D, ?_⟩
  intro x hx
  obtain ⟨hD, hf⟩ := hN x hx
  exact ⟨hD, by dsimp only; rw [hf, map_neg, neg_div]⟩

lemma RationalCells.inv {f : (ι → ℝ) → ℝ} (hf : RationalCells f) :
    RationalCells (fun x => (f x)⁻¹) := by
  classical
  obtain ⟨η, hη, p, hp⟩ := hf
  let := hη
  choose N D hN using hp
  refine ⟨η ⊕ (η → SignType), inferInstance, Sum.elim p N, ?_⟩
  intro s
  let t : η → SignType := fun i => s (Sum.inl i)
  by_cases ht : s (Sum.inr t) = 0
  · refine ⟨0, 1, ?_⟩
    intro x hx
    obtain ⟨hD, hf⟩ := hN t x (fun i => hx (Sum.inl i))
    have hzero : MvPolynomial.eval x (N t) = 0 :=
      sign_eq_zero_iff.mp ((hx (Sum.inr t)).trans ht)
    simp [hf, hzero]
  · refine ⟨D t, N t, ?_⟩
    intro x hx
    obtain ⟨hD, hf⟩ := hN t x (fun i => hx (Sum.inl i))
    have hnonzero : MvPolynomial.eval x (N t) ≠ 0 := by
      intro hzero
      apply ht
      simpa only [Sum.elim_inr, hzero, sign_zero] using (hx (Sum.inr t)).symm
    exact ⟨hnonzero, by dsimp only; rw [hf, inv_div]⟩

lemma RationalCells.const (c : ℝ) : RationalCells (fun _ : ι → ℝ => c) := by
  simpa using RationalCells.polynomial (MvPolynomial.C c : MvPolynomial ι ℝ)

lemma SignDetermined.const (c : α) : SignDetermined (fun _ : ι → ℝ => c) :=
  ⟨Empty, inferInstance, Empty.elim, fun _ _ _ => rfl⟩

lemma SignDetermined.comp {f : (ι → ℝ) → α} (hf : SignDetermined f) (g : α → β) :
    SignDetermined (fun x => g (f x)) := by
  obtain ⟨η, hη, p, hp⟩ := hf
  exact ⟨η, hη, p, fun x y hxy => congrArg g (hp x y hxy)⟩

lemma SignDetermined.prod {f : (ι → ℝ) → α} {g : (ι → ℝ) → β}
    (hf : SignDetermined f) (hg : SignDetermined g) :
    SignDetermined (fun x => (f x, g x)) := by
  obtain ⟨η, hη, p, hp⟩ := hf
  obtain ⟨κ, hκ, q, hq⟩ := hg
  let := hη
  let := hκ
  refine ⟨η ⊕ κ, inferInstance, Sum.elim p q, ?_⟩
  intro x y hxy
  exact Prod.ext (hp x y (fun i => hxy (Sum.inl i)))
    (hq x y (fun i => hxy (Sum.inr i)))

lemma SignDetermined.pi {κ : Type} [Fintype κ] {β : κ → Type}
    (f : (i : κ) → (ι → ℝ) → β i) (hf : ∀ i, SignDetermined (f i)) :
    SignDetermined (fun x i => f i x) := by
  classical
  choose η hη p hp using hf
  let (i : κ) := hη i
  refine ⟨(i : κ) × η i, inferInstance, fun z => p z.1 z.2, ?_⟩
  intro x y hxy
  funext i
  exact hp i x y (fun j => hxy ⟨i, j⟩)

lemma SignDetermined.of_fibers {f : (ι → ℝ) → α} {g : (ι → ℝ) → β}
    (hg : SignDetermined g) (h : ∀ x y, g x = g y → f x = f y) : SignDetermined f := by
  obtain ⟨η, hη, p, hp⟩ := hg
  exact ⟨η, hη, p, fun x y hxy => h x y (hp x y hxy)⟩

lemma sign_div_real (a b : ℝ) :
    SignType.sign (a / b) = SignType.sign a * SignType.sign b := by
  exact map_div₀ (signHom : ℝ →*₀ SignType) a b

/-- The sign of a rational-on-cells function is determined by finitely many polynomial signs. -/
lemma RationalCells.sign {f : (ι → ℝ) → ℝ} (hf : RationalCells f) :
    SignDetermined (fun x => SignType.sign (f x)) := by
  classical
  obtain ⟨η, hη, p, hp⟩ := hf
  let := hη
  choose N D hN using hp
  let q : η ⊕ ((η → SignType) × Bool) → MvPolynomial ι ℝ :=
    Sum.elim p (fun z => if z.2 then N z.1 else D z.1)
  refine ⟨η ⊕ ((η → SignType) × Bool), inferInstance, q, ?_⟩
  intro x y hxy
  let s : η → SignType := fun i => SignType.sign (MvPolynomial.eval x (p i))
  obtain ⟨hDx, hx⟩ := hN s x (fun _ => rfl)
  obtain ⟨hDy, hy⟩ := hN s y (fun i => (hxy (Sum.inl i)).symm)
  have hnum : SignType.sign (MvPolynomial.eval x (N s)) =
      SignType.sign (MvPolynomial.eval y (N s)) := hxy (Sum.inr (s, true))
  have hden : SignType.sign (MvPolynomial.eval x (D s)) =
      SignType.sign (MvPolynomial.eval y (D s)) := hxy (Sum.inr (s, false))
  change SignType.sign (f x) = SignType.sign (f y)
  rw [hx, hy, sign_div_real, sign_div_real, hnum, hden]

/-- Parameter functions obtained by rational operations on polynomial functions. -/
def rationalSubring (ι : Type) : Subring ((ι → ℝ) → ℝ) where
  carrier := RationalCells
  zero_mem' := RationalCells.const 0
  one_mem' := RationalCells.const 1
  add_mem' := RationalCells.add
  mul_mem' := RationalCells.mul
  neg_mem' := RationalCells.neg

abbrev RFun (ι : Type) := rationalSubring ι

noncomputable section

scoped instance (ι : Type) : Inv (RFun ι) where
  inv f := ⟨fun x => (f.1 x)⁻¹, RationalCells.inv f.2⟩

end

noncomputable def RFun.polynomial (p : MvPolynomial ι ℝ) : RFun ι :=
  ⟨fun x => MvPolynomial.eval x p, RationalCells.polynomial p⟩

/-- Evaluation of parameter functions at a fixed parameter. -/
def RFun.at (x : ι → ℝ) : RFun ι →+* ℝ where
  toFun f := f.1 x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] lemma RFun.at_inv (x : ι → ℝ) (f : RFun ι) :
    RFun.at x f⁻¹ = (RFun.at x f)⁻¹ := rfl

lemma RFun.sign (f : RFun ι) :
    SignDetermined (fun x => SignType.sign (RFun.at x f)) := RationalCells.sign f.2

end Submission.Obl.k4_sign_projection
