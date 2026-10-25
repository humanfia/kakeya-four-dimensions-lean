import Mathlib
import Submission.Obl.k4_scalar_true_terminal_lifting.Interface

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MvPolynomial
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-!
# Coefficient norms of real polynomials and the polynomial sign format

`cnorm p` is the `ℓ¹` norm of the coefficients of `p`. It is subadditive and submultiplicative,
so substitution of polynomials of bounded `cnorm` into `p` has controlled `cnorm`. Together with
degree bounds for substitution, this gives closure properties of the frozen sign format
`Format` (monotonicity, intersection, and preimages under polynomial maps).
-/

/-! ### The `ℓ¹` norm of the coefficients -/

/-- ℓ¹ norm of the coefficients. -/
noncomputable def cnorm {σ : Type*} (p : MvPolynomial σ ℝ) : ℝ := ∑ m ∈ p.support, |p.coeff m|

lemma cnorm_nonneg {σ : Type*} (p : MvPolynomial σ ℝ) : 0 ≤ cnorm p :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- `cnorm` is the sum of the absolute coefficients over any finset containing the support. -/
lemma cnorm_eq_sum_of_subset {σ : Type*} (p : MvPolynomial σ ℝ) {s : Finset (σ →₀ ℕ)}
    (hs : p.support ⊆ s) : cnorm p = ∑ m ∈ s, |p.coeff m| := by
  unfold cnorm
  refine Finset.sum_subset hs (fun m _ hm => ?_)
  rw [notMem_support_iff.mp hm, abs_zero]

lemma abs_coeff_le_cnorm {σ : Type*} (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |p.coeff m| ≤ cnorm p := by
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (f := fun m => |p.coeff m|) (fun _ _ => abs_nonneg _) hm
  · rw [notMem_support_iff.mp hm, abs_zero]
    exact cnorm_nonneg p

lemma cnorm_zero {σ : Type*} : cnorm (0 : MvPolynomial σ ℝ) = 0 := by
  simp [cnorm]

lemma cnorm_add_le {σ : Type*} (p q : MvPolynomial σ ℝ) : cnorm (p + q) ≤ cnorm p + cnorm q := by
  classical
  rw [cnorm_eq_sum_of_subset (p + q) support_add,
    cnorm_eq_sum_of_subset p (Finset.subset_union_left (s₂ := q.support)),
    cnorm_eq_sum_of_subset q (Finset.subset_union_right (s₁ := p.support)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun m _ => ?_)
  have h : (p + q).coeff m = p.coeff m + q.coeff m := by simp
  rw [h]
  exact abs_add_le _ _

lemma cnorm_neg {σ : Type*} (p : MvPolynomial σ ℝ) : cnorm (-p) = cnorm p := by
  unfold cnorm
  rw [support_neg]
  exact Finset.sum_congr rfl (fun m _ => by rw [coeff_neg, abs_neg])

lemma cnorm_sub_le {σ : Type*} (p q : MvPolynomial σ ℝ) : cnorm (p - q) ≤ cnorm p + cnorm q := by
  rw [sub_eq_add_neg, ← cnorm_neg q]
  exact cnorm_add_le p (-q)

lemma cnorm_monomial {σ : Type*} (m : σ →₀ ℕ) (a : ℝ) :
    cnorm (monomial m a : MvPolynomial σ ℝ) = |a| := by
  classical
  rw [cnorm_eq_sum_of_subset _ support_monomial_subset, Finset.sum_singleton, coeff_monomial]
  simp

lemma cnorm_C {σ : Type*} (a : ℝ) : cnorm (C a : MvPolynomial σ ℝ) = |a| := by
  rw [C_apply, cnorm_monomial]

lemma cnorm_X {σ : Type*} (i : σ) : cnorm (X i : MvPolynomial σ ℝ) = 1 := by
  rw [X, cnorm_monomial, abs_one]

lemma cnorm_one {σ : Type*} : cnorm (1 : MvPolynomial σ ℝ) = 1 := by
  rw [← C_1, cnorm_C, abs_one]

lemma cnorm_sum_le {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    cnorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, cnorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cnorm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (cnorm_add_le _ _).trans (add_le_add le_rfl ih)

lemma cnorm_mul_le {σ : Type*} (p q : MvPolynomial σ ℝ) : cnorm (p * q) ≤ cnorm p * cnorm q := by
  have h : p * q = ∑ m ∈ p.support, ∑ m' ∈ q.support,
      monomial (m + m') (p.coeff m * q.coeff m') := by
    calc p * q = (∑ m ∈ p.support, monomial m (p.coeff m)) *
          (∑ m' ∈ q.support, monomial m' (q.coeff m')) := by rw [← p.as_sum, ← q.as_sum]
      _ = _ := by rw [Finset.sum_mul_sum]; simp only [monomial_mul_monomial]
  rw [h]
  calc cnorm (∑ m ∈ p.support, ∑ m' ∈ q.support, monomial (m + m') (p.coeff m * q.coeff m'))
      ≤ ∑ m ∈ p.support, cnorm (∑ m' ∈ q.support, monomial (m + m') (p.coeff m * q.coeff m')) :=
        cnorm_sum_le _ _
    _ ≤ ∑ m ∈ p.support, ∑ m' ∈ q.support, cnorm (monomial (m + m') (p.coeff m * q.coeff m')) :=
        Finset.sum_le_sum (fun m _ => cnorm_sum_le _ _)
    _ = ∑ m ∈ p.support, ∑ m' ∈ q.support, |p.coeff m| * |q.coeff m'| := by
        simp only [cnorm_monomial, abs_mul]
    _ = cnorm p * cnorm q := by
        rw [cnorm, cnorm, Finset.sum_mul_sum]

lemma cnorm_C_mul_le {σ : Type*} (a : ℝ) (p : MvPolynomial σ ℝ) :
    cnorm (C a * p) ≤ |a| * cnorm p := by
  have h := cnorm_mul_le (C a) p
  rwa [cnorm_C] at h

lemma cnorm_pow_le {σ : Type*} (p : MvPolynomial σ ℝ) (n : ℕ) : cnorm (p ^ n) ≤ cnorm p ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, cnorm_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (cnorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (cnorm_nonneg p))

lemma cnorm_prod_le {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    cnorm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, cnorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cnorm_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (cnorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (cnorm_nonneg _))

/-- Substitution, written out monomial by monomial. -/
lemma bind₁_eq_sum {σ τ : Type*} (f : σ → MvPolynomial τ ℝ) (p : MvPolynomial σ ℝ) :
    bind₁ f p = ∑ m ∈ p.support, C (p.coeff m) * ∏ i ∈ m.support, f i ^ m i := by
  calc bind₁ f p = bind₁ f (∑ m ∈ p.support, monomial m (p.coeff m)) := by rw [← p.as_sum]
    _ = _ := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun m _ => bind₁_monomial f m (p.coeff m))

lemma cnorm_bind₁_le {σ τ : Type*} (f : σ → MvPolynomial τ ℝ) {R : ℝ} (hR : 1 ≤ R)
    (hf : ∀ i, cnorm (f i) ≤ R) (p : MvPolynomial σ ℝ) :
    cnorm (bind₁ f p) ≤ cnorm p * R ^ p.totalDegree := by
  calc cnorm (bind₁ f p)
      = cnorm (∑ m ∈ p.support, C (p.coeff m) * ∏ i ∈ m.support, f i ^ m i) := by
        rw [bind₁_eq_sum]
    _ ≤ ∑ m ∈ p.support, cnorm (C (p.coeff m) * ∏ i ∈ m.support, f i ^ m i) :=
        cnorm_sum_le _ _
    _ ≤ ∑ m ∈ p.support, |p.coeff m| * R ^ p.totalDegree := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        refine (cnorm_C_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
        calc cnorm (∏ i ∈ m.support, f i ^ m i)
            ≤ ∏ i ∈ m.support, cnorm (f i ^ m i) := cnorm_prod_le _ _
          _ ≤ ∏ i ∈ m.support, R ^ m i := by
              refine Finset.prod_le_prod₀ (fun i _ => cnorm_nonneg _) (fun i _ => ?_)
              exact (cnorm_pow_le _ _).trans (pow_le_pow_left₀ (cnorm_nonneg _) (hf i) _)
          _ = R ^ (∑ i ∈ m.support, m i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ R ^ p.totalDegree := pow_le_pow_right₀ hR (le_totalDegree hm)
    _ = cnorm p * R ^ p.totalDegree := by
        rw [cnorm, Finset.sum_mul]

lemma cnorm_le_card_mul {σ : Type*} (p : MvPolynomial σ ℝ) {B : ℝ}
    (hB : ∀ m, |p.coeff m| ≤ B) : cnorm p ≤ p.support.card * B := by
  unfold cnorm
  calc ∑ m ∈ p.support, |p.coeff m| ≤ ∑ _m ∈ p.support, B :=
        Finset.sum_le_sum (fun m _ => hB m)
    _ = p.support.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

lemma card_support_le {n D : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ D) :
    p.support.card ≤ (D + 1) ^ n := by
  classical
  have hle : ∀ m ∈ p.support, ∀ i, m i ≤ D := by
    intro m hm i
    refine le_trans ?_ ((le_totalDegree hm).trans hp)
    by_cases hi : i ∈ m.support
    · exact Finset.single_le_sum (f := fun j => m j) (fun _ _ => Nat.zero_le _) hi
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact Nat.zero_le _
  let g : (Fin n →₀ ℕ) → (Fin n → Fin (D + 1)) :=
    fun m i => ⟨min (m i) D, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hcard : p.support.card ≤ (Finset.univ : Finset (Fin n → Fin (D + 1))).card := by
    refine Finset.card_le_card_of_injOn g (fun m _ => by simp) ?_
    intro m hm m' hm' hmm'
    ext i
    have h1 : min (m i) D = min (m' i) D := congrArg (fun φ => (φ i : ℕ)) hmm'
    rwa [min_eq_left (hle m hm i), min_eq_left (hle m' hm' i)] at h1
  simpa using hcard

lemma cnorm_le_of_coeff {n D : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ D) {B : ℝ}
    (hB : ∀ m, |p.coeff m| ≤ B) : cnorm p ≤ ((D + 1) ^ n : ℕ) * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine (cnorm_le_card_mul p hB).trans (mul_le_mul_of_nonneg_right ?_ hB0)
  exact_mod_cast card_support_le p hp

lemma totalDegree_bind₁_le {σ τ : Type*} (f : σ → MvPolynomial τ ℝ) {e : ℕ}
    (hf : ∀ i, (f i).totalDegree ≤ e) (p : MvPolynomial σ ℝ) :
    (bind₁ f p).totalDegree ≤ p.totalDegree * e := by
  rw [bind₁_eq_sum]
  refine totalDegree_finsetSum_le (fun m hm => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ m.support, (f i ^ m i).totalDegree ≤ ∑ i ∈ m.support, m i * e :=
        Finset.sum_le_sum (fun i _ => (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i)))
    _ = (∑ i ∈ m.support, m i) * e := by rw [Finset.sum_mul]
    _ ≤ p.totalDegree * e := Nat.mul_le_mul_right _ (le_totalDegree hm)

/-- Evaluation of a substitution. -/
lemma eval_bind₁_eq {σ τ : Type*} (x : τ → ℝ) (Q : σ → MvPolynomial τ ℝ)
    (p : MvPolynomial σ ℝ) : eval x (bind₁ Q p) = eval (fun i => eval x (Q i)) p :=
  eval₂Hom_bind₁ _ _ _ _

/-! ### The sign format -/

-- adapted from Submission/Obl/k4_scalar_conditional_crop_worlds/FormatLemmas.lean
lemma Format.nonneg {n D : ℕ} {R : ℝ} {A : Set (Fin n → ℝ)} (h : Format n R D A) : 0 ≤ R := by
  obtain ⟨k, hk, -⟩ := h
  exact (Nat.cast_nonneg k).trans hk

-- adapted from Submission/Obl/k4_scalar_conditional_crop_worlds/Formats.lean
lemma Format.mono {n D D' : ℕ} {R R' : ℝ} {A : Set (Fin n → ℝ)} (h : Format n R D A)
    (hR : R ≤ R') (hD : D ≤ D') : Format n R' D' A := by
  obtain ⟨k, hk, p, hp, S, hS⟩ := h
  exact ⟨k, hk.trans hR, p, fun j => ⟨(hp j).1.trans hD, fun b => ((hp j).2 b).trans hR⟩, S, hS⟩

-- adapted from Submission/Obl/k4_scalar_conditional_crop_worlds/FormatLemmas.lean
lemma Format.inter {n D : ℕ} {R₁ R₂ : ℝ} {A₁ A₂ : Set (Fin n → ℝ)} (h₁ : Format n R₁ D A₁)
    (h₂ : Format n R₂ D A₂) : Format n (R₁ + R₂) D (A₁ ∩ A₂) := by
  have hR₁ := Format.nonneg h₁
  have hR₂ := Format.nonneg h₂
  obtain ⟨k₁, hk₁, p₁, hp₁, S₁, rfl⟩ := h₁
  obtain ⟨k₂, hk₂, p₂, hp₂, S₂, rfl⟩ := h₂
  refine ⟨k₁ + k₂, by push_cast; linarith, Fin.append p₁ p₂, ?_,
    {s | (fun i => s (Fin.castAdd k₂ i)) ∈ S₁ ∧ (fun i => s (Fin.natAdd k₁ i)) ∈ S₂}, ?_⟩
  · intro j
    induction j using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      exact ⟨(hp₁ i).1, fun b => ((hp₁ i).2 b).trans (by linarith)⟩
    | right i =>
      rw [Fin.append_right]
      exact ⟨(hp₂ i).1, fun b => ((hp₂ i).2 b).trans (by linarith)⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]

-- adapted from Submission/Obl/k4_scalar_conditional_crop_worlds/FormatLemmas.lean
lemma Format.congr {n D : ℕ} {R : ℝ} {A A' : Set (Fin n → ℝ)} (h : Format n R D A)
    (hA : A = A') : Format n R D A' :=
  hA ▸ h

/-- Preimage under a polynomial map. Coefficient bounds of the composed tests are restored by
positive rescaling of each test (which keeps its sign), so only degrees matter. -/
lemma Format.preimage {n m D e : ℕ} {R : ℝ} {A : Set (Fin n → ℝ)} (hA : Format n R D A)
    (hR : 1 ≤ R) (Q : Fin n → MvPolynomial (Fin m) ℝ) (hQ : ∀ i, (Q i).totalDegree ≤ e) :
    Format m R (D * e) {x | (fun i => MvPolynomial.eval x (Q i)) ∈ A} := by
  obtain ⟨k, hk, p, hp, S, rfl⟩ := hA
  obtain ⟨c, hc_pos, hc_ge⟩ : ∃ c : Fin k → ℝ, (∀ j, 0 < c j) ∧
      ∀ j, cnorm (bind₁ Q (p j)) ≤ c j :=
    ⟨fun j => 1 + cnorm (bind₁ Q (p j)),
      fun j => add_pos_of_pos_of_nonneg one_pos (cnorm_nonneg _), fun j => by linarith⟩
  refine ⟨k, hk, fun j => C (c j)⁻¹ * bind₁ Q (p j), fun j => ⟨?_, fun b => ?_⟩, S, ?_⟩
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_bind₁_le Q hQ (p j)).trans (Nat.mul_le_mul_right _ (hp j).1)
  · rw [coeff_C_mul, abs_mul, abs_inv, abs_of_pos (hc_pos j)]
    calc (c j)⁻¹ * |(bind₁ Q (p j)).coeff b| ≤ (c j)⁻¹ * c j :=
          mul_le_mul_of_nonneg_left ((abs_coeff_le_cnorm _ b).trans (hc_ge j))
            (inv_nonneg.mpr (hc_pos j).le)
      _ = 1 := inv_mul_cancel₀ (hc_pos j).ne'
      _ ≤ R := hR
  · ext x
    simp only [Set.mem_ofPred_eq]
    have hfun : (fun j => SignType.sign (eval x (C (c j)⁻¹ * bind₁ Q (p j)))) =
        (fun j => SignType.sign (eval (fun i => eval x (Q i)) (p j))) := by
      funext j
      rw [map_mul, eval_C, eval_bind₁_eq, sign_mul, sign_pos (inv_pos.mpr (hc_pos j)), one_mul]
    rw [hfun]

end Submission.Obl.k4_scalar_true_terminal_lifting
