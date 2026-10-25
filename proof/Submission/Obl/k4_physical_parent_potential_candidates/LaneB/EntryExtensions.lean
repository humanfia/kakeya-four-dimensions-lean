-- Lane B: algebraic extensions of the Hessian and cleared-cubic entries of a quadratic-extension branch.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.QuadraticRealJets
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniHessian
import Submission.Obl.k4_physical_parent_potential_candidates.ConicTensor

/-!
# Algebraic extensions of Hessian and cleared-cubic entries

Let `F` be holomorphic on the complex ball of radius four, with a rational presentation
`W F = U + V s` in a square root `s` of a polynomial `Δ`, and let `f` be its real slice.
For a real affine function `c + L` and a scale `s0 ≠ 0`, every Hessian entry of
`(f - c - L) / s0`, and every entry of the cleared cubic defect of this Hessian against the
third derivatives of a real polynomial potential, has an algebraic real extension
(`HasRealExtension`) of a degree depending only on the degree bounds of the data.

The functions with a rational presentation in `s` (`SqrtRep`) are closed under the ring
operations, with explicit degree bounds, and under mixed directional complex jets
(the rational square-root update of `FrechetRational.lean`, iterated along arbitrary
directions). A presentation gives a polynomial relation by `exists_sqrt_rational_relation`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial Metric
open scoped ContDiff

section SqrtRepSection

variable {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))} {s : EuclideanSpace ℂ (Fin n) → ℂ}

/-- `φ` is holomorphic on `Ω`, where it is a rational expression `(U + V s) / W` in the square
root `s`, with numerators and a nonzero denominator of total degree at most `d`. -/
def SqrtRep (Ω : Set (EuclideanSpace ℂ (Fin n))) (s : EuclideanSpace ℂ (Fin n) → ℂ) (d : ℕ)
    (φ : EuclideanSpace ℂ (Fin n) → ℂ) : Prop :=
  ContDiffOn ℂ ⊤ φ Ω ∧ ∃ U V W : MvPolynomial (Fin n) ℂ, W ≠ 0 ∧ U.totalDegree ≤ d ∧
    V.totalDegree ≤ d ∧ W.totalDegree ≤ d ∧
    ∀ z ∈ Ω, eval (fun i => z i) W * φ z = eval (fun i => z i) U + eval (fun i => z i) V * s z

namespace SqrtRep

theorem mono {d d' : ℕ} {φ : EuclideanSpace ℂ (Fin n) → ℂ} (hd : d ≤ d')
    (h : SqrtRep Ω s d φ) : SqrtRep Ω s d' φ := by
  obtain ⟨hφ, U, V, W, hW, hU, hV, hWd, hrep⟩ := h
  exact ⟨hφ, U, V, W, hW, hU.trans hd, hV.trans hd, hWd.trans hd, hrep⟩

theorem congr {d : ℕ} {φ ψ : EuclideanSpace ℂ (Fin n) → ℂ} (h : SqrtRep Ω s d φ)
    (he : ∀ z ∈ Ω, φ z = ψ z) : SqrtRep Ω s d ψ := by
  obtain ⟨hφ, U, V, W, hW, hU, hV, hWd, hrep⟩ := h
  refine ⟨hφ.congr (fun z hz => (he z hz).symm), U, V, W, hW, hU, hV, hWd, fun z hz => ?_⟩
  rw [← he z hz]
  exact hrep z hz

/-- A polynomial is its own presentation, with denominator one. -/
theorem poly (P : MvPolynomial (Fin n) ℂ) :
    SqrtRep Ω s P.totalDegree (fun z => eval (fun i => z i) P) := by
  refine ⟨?_, P, 0, 1, one_ne_zero, le_rfl, by simp, by simp, fun z _ => by simp⟩
  apply k4_quadratic_sheet_continuation.contDiffOn_polynomial_eval
  intro i
  fun_prop

theorem const (c : ℂ) : SqrtRep Ω s 0 (fun _ => c) :=
  ((poly (Ω := Ω) (s := s) (C c)).mono (by simp)).congr (fun z _ => by simp)

theorem add {d₁ d₂ : ℕ} {φ ψ : EuclideanSpace ℂ (Fin n) → ℂ}
    (h₁ : SqrtRep Ω s d₁ φ) (h₂ : SqrtRep Ω s d₂ ψ) :
    SqrtRep Ω s (d₁ + d₂) (fun z => φ z + ψ z) := by
  obtain ⟨hφ, U₁, V₁, W₁, hW₁, hU₁, hV₁, hWd₁, hrep₁⟩ := h₁
  obtain ⟨hψ, U₂, V₂, W₂, hW₂, hU₂, hV₂, hWd₂, hrep₂⟩ := h₂
  refine ⟨hφ.add hψ, U₁ * W₂ + U₂ * W₁, V₁ * W₂ + V₂ * W₁, W₁ * W₂, mul_ne_zero hW₁ hW₂,
    ?_, ?_, ?_, ?_⟩
  · exact (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans (by omega))
      ((totalDegree_mul _ _).trans (by omega)))
  · exact (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans (by omega))
      ((totalDegree_mul _ _).trans (by omega)))
  · exact (totalDegree_mul _ _).trans (by omega)
  · intro z hz
    simp only [map_add, map_mul]
    linear_combination (eval (fun i => z i) W₂) * hrep₁ z hz +
      (eval (fun i => z i) W₁) * hrep₂ z hz

theorem neg {d : ℕ} {φ : EuclideanSpace ℂ (Fin n) → ℂ} (h : SqrtRep Ω s d φ) :
    SqrtRep Ω s d (fun z => -φ z) := by
  obtain ⟨hφ, U, V, W, hW, hU, hV, hWd, hrep⟩ := h
  refine ⟨hφ.neg, -U, -V, W, hW, by rwa [totalDegree_neg], by rwa [totalDegree_neg], hWd,
    fun z hz => ?_⟩
  simp only [map_neg]
  linear_combination -hrep z hz

theorem sub {d₁ d₂ : ℕ} {φ ψ : EuclideanSpace ℂ (Fin n) → ℂ}
    (h₁ : SqrtRep Ω s d₁ φ) (h₂ : SqrtRep Ω s d₂ ψ) :
    SqrtRep Ω s (d₁ + d₂) (fun z => φ z - ψ z) :=
  (h₁.add h₂.neg).congr (fun _ _ => (sub_eq_add_neg _ _).symm)

theorem const_mul {d : ℕ} {φ : EuclideanSpace ℂ (Fin n) → ℂ} (c : ℂ) (h : SqrtRep Ω s d φ) :
    SqrtRep Ω s d (fun z => c * φ z) := by
  obtain ⟨hφ, U, V, W, hW, hU, hV, hWd, hrep⟩ := h
  refine ⟨contDiffOn_const.mul hφ, C c * U, C c * V, W, hW, ?_, ?_, hWd, fun z hz => ?_⟩
  · exact (totalDegree_mul _ _).trans (by simpa using hU)
  · exact (totalDegree_mul _ _).trans (by simpa using hV)
  · simp only [map_mul, eval_C]
    linear_combination c * hrep z hz

theorem div_const {d : ℕ} {φ : EuclideanSpace ℂ (Fin n) → ℂ} (c : ℂ) (h : SqrtRep Ω s d φ) :
    SqrtRep Ω s d (fun z => φ z / c) :=
  (h.const_mul c⁻¹).congr (fun _ _ => by rw [div_eq_mul_inv, mul_comm])

/-- Products stay in the quadratic extension: the square of `s` is the polynomial `Δ`. -/
theorem mul {Δ : MvPolynomial (Fin n) ℂ} {D : ℕ} (hΔ : Δ.totalDegree ≤ D)
    (hroot : ∀ z ∈ Ω, (s z) ^ 2 = eval (fun i => z i) Δ)
    {d₁ d₂ : ℕ} {φ ψ : EuclideanSpace ℂ (Fin n) → ℂ}
    (h₁ : SqrtRep Ω s d₁ φ) (h₂ : SqrtRep Ω s d₂ ψ) :
    SqrtRep Ω s (d₁ + d₂ + D) (fun z => φ z * ψ z) := by
  obtain ⟨hφ, U₁, V₁, W₁, hW₁, hU₁, hV₁, hWd₁, hrep₁⟩ := h₁
  obtain ⟨hψ, U₂, V₂, W₂, hW₂, hU₂, hV₂, hWd₂, hrep₂⟩ := h₂
  refine ⟨hφ.mul hψ, U₁ * U₂ + V₁ * V₂ * Δ, U₁ * V₂ + V₁ * U₂, W₁ * W₂, mul_ne_zero hW₁ hW₂,
    ?_, ?_, ?_, ?_⟩
  · refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans (by omega)) ?_)
    exact (totalDegree_mul _ _).trans
      ((add_le_add ((totalDegree_mul _ _).trans (add_le_add hV₁ hV₂)) hΔ).trans (by omega))
  · exact (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans (by omega))
      ((totalDegree_mul _ _).trans (by omega)))
  · exact (totalDegree_mul _ _).trans (by omega)
  · intro z hz
    simp only [map_add, map_mul]
    linear_combination (eval (fun i => z i) W₂ * ψ z) * hrep₁ z hz +
      (eval (fun i => z i) U₁ + eval (fun i => z i) V₁ * s z) * hrep₂ z hz +
      (eval (fun i => z i) V₁ * eval (fun i => z i) V₂) * hroot z hz

theorem sum_fin3 {d : ℕ} {φ : Fin 3 → EuclideanSpace ℂ (Fin n) → ℂ}
    (h : ∀ a, SqrtRep Ω s d (φ a)) : SqrtRep Ω s (3 * d) (fun z => ∑ a : Fin 3, φ a z) :=
  ((((h 0).add (h 1)).add (h 2)).mono (by omega)).congr
    (fun z _ => by simp [Fin.sum_univ_three])

/-- The determinant of a `3 × 3` matrix of presented functions. -/
theorem det3 {Δ : MvPolynomial (Fin n) ℂ} {D : ℕ} (hΔ : Δ.totalDegree ≤ D)
    (hroot : ∀ z ∈ Ω, (s z) ^ 2 = eval (fun i => z i) Δ)
    {d : ℕ} {M : EuclideanSpace ℂ (Fin n) → Matrix (Fin 3) (Fin 3) ℂ}
    (hM : ∀ a b, SqrtRep Ω s d (fun z => M z a b)) :
    SqrtRep Ω s (6 * (3 * d + 2 * D)) (fun z => (M z).det) := by
  have h3 : ∀ a b c e g h : Fin 3,
      SqrtRep Ω s (3 * d + 2 * D) (fun z => M z a b * M z c e * M z g h) :=
    fun a b c e g h => (((hM a b).mul hΔ hroot (hM c e)).mul hΔ hroot (hM g h)).mono (by omega)
  refine (((((((h3 0 0 1 1 2 2).sub (h3 0 0 1 2 2 1)).sub (h3 0 1 1 0 2 2)).add
    (h3 0 1 1 2 2 0)).add (h3 0 2 1 0 2 1)).sub (h3 0 2 1 1 2 0)).mono (by omega)).congr ?_
  intro z _
  simp only [Matrix.det_fin_three]

/-- The entries of the adjugate of a `3 × 3` matrix of presented functions. -/
theorem adjugate3 {Δ : MvPolynomial (Fin n) ℂ} {D : ℕ} (hΔ : Δ.totalDegree ≤ D)
    (hroot : ∀ z ∈ Ω, (s z) ^ 2 = eval (fun i => z i) Δ)
    {d : ℕ} {M : EuclideanSpace ℂ (Fin n) → Matrix (Fin 3) (Fin 3) ℂ}
    (hM : ∀ a b, SqrtRep Ω s d (fun z => M z a b)) (a b : Fin 3) :
    SqrtRep Ω s (2 * (2 * d + D)) (fun z => (M z).adjugate a b) := by
  have h2 : ∀ a b c e : Fin 3, SqrtRep Ω s (2 * d + D) (fun z => M z a b * M z c e) :=
    fun a b c e => ((hM a b).mul hΔ hroot (hM c e)).mono (by omega)
  have key : ∀ a₁ b₁ c₁ e₁ a₂ b₂ c₂ e₂ : Fin 3, SqrtRep Ω s (2 * (2 * d + D))
      (fun z => M z a₁ b₁ * M z c₁ e₁ - M z a₂ b₂ * M z c₂ e₂) :=
    fun a₁ b₁ c₁ e₁ a₂ b₂ c₂ e₂ => ((h2 a₁ b₁ c₁ e₁).sub (h2 a₂ b₂ c₂ e₂)).mono (by omega)
  have key' : ∀ a₁ b₁ c₁ e₁ a₂ b₂ c₂ e₂ : Fin 3, SqrtRep Ω s (2 * (2 * d + D))
      (fun z => -(M z a₁ b₁ * M z c₁ e₁) + M z a₂ b₂ * M z c₂ e₂) :=
    fun a₁ b₁ c₁ e₁ a₂ b₂ c₂ e₂ => ((h2 a₁ b₁ c₁ e₁).neg.add (h2 a₂ b₂ c₂ e₂)).mono (by omega)
  simp only [Matrix.adjugate_fin_three]
  fin_cases a <;> fin_cases b <;> simp <;>
    first
    | exact key _ _ _ _ _ _ _ _
    | exact key' _ _ _ _ _ _ _ _

end SqrtRep

/-- The cleared cubic defect of `ConicTensor.cleared`, over an arbitrary commutative ring. -/
def clearedFormula {R : Type*} [CommRing R] (H : Matrix (Fin 3) (Fin 3) R)
    (T : Fin 3 → Fin 3 → Fin 3 → R) (i j k : Fin 3) : R :=
  5 * H.det * T i j k -
    ((∑ a : Fin 3, ∑ b : Fin 3, H.adjugate a b * T i a b) * H j k +
      (∑ a : Fin 3, ∑ b : Fin 3, H.adjugate a b * T j a b) * H i k +
      (∑ a : Fin 3, ∑ b : Fin 3, H.adjugate a b * T k a b) * H i j)

theorem cleared_eq_clearedFormula (H : Matrix (Fin 3) (Fin 3) ℝ) (T : ConicTensor.Tensor)
    (i j k : Fin 3) : ConicTensor.cleared H T i j k = clearedFormula H T i j k := rfl

theorem map_clearedFormula {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (H : Matrix (Fin 3) (Fin 3) R) (T : Fin 3 → Fin 3 → Fin 3 → R) (i j k : Fin 3) :
    f (clearedFormula H T i j k) =
      clearedFormula (f.mapMatrix H) (fun a b c => f (T a b c)) i j k := by
  have hadj : ∀ a b, (H.map f).adjugate a b = f (H.adjugate a b) := by
    intro a b
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_adjugate, RingHom.mapMatrix_apply,
      Matrix.map_apply]
  simp only [clearedFormula, map_sub, map_add, map_mul, map_sum, RingHom.map_det, map_ofNat,
    RingHom.mapMatrix_apply, Matrix.map_apply, hadj]

namespace SqrtRep

/-- Every entry of the cleared cubic defect of presented functions is presented. -/
theorem clearedFormula3 {Δ : MvPolynomial (Fin n) ℂ} {D : ℕ} (hΔ : Δ.totalDegree ≤ D)
    (hroot : ∀ z ∈ Ω, (s z) ^ 2 = eval (fun i => z i) Δ)
    {d e : ℕ} {M : EuclideanSpace ℂ (Fin n) → Matrix (Fin 3) (Fin 3) ℂ}
    {T : EuclideanSpace ℂ (Fin n) → Fin 3 → Fin 3 → Fin 3 → ℂ}
    (hM : ∀ a b, SqrtRep Ω s d (fun z => M z a b))
    (hT : ∀ a b c, SqrtRep Ω s e (fun z => T z a b c)) (i j k : Fin 3) :
    SqrtRep Ω s (200 * (d + e + D)) (fun z => clearedFormula (M z) (T z) i j k) := by
  have hdet := det3 hΔ hroot hM
  have hadj := adjugate3 hΔ hroot hM
  have hm : ∀ l, SqrtRep Ω s (3 * (3 * (2 * (2 * d + D) + e + D)))
      (fun z => ∑ a : Fin 3, ∑ b : Fin 3, (M z).adjugate a b * T z l a b) :=
    fun l => sum_fin3 (fun a => sum_fin3 (fun b => (hadj a b).mul hΔ hroot (hT l a b)))
  have h1 := (hdet.const_mul 5).mul hΔ hroot (hT i j k)
  have h2 := (((hm i).mul hΔ hroot (hM j k)).add ((hm j).mul hΔ hroot (hM i k))).add
    ((hm k).mul hΔ hroot (hM i j))
  exact ((h1.sub h2).mono (by omega)).congr (fun z _ => rfl)

/-- Mixed directional complex jets of a presented function are presented: each derivative
is the rational square-root update of `FrechetRational.lean`, in its own direction. The proof
is that of `exists_iterated_rational_presentation` (`Analytic/IteratedRational.lean`), with the
constant direction replaced by the first direction of the tuple. -/
theorem iteratedFDeriv_apply (hΩ : IsOpen Ω) (hs : DifferentiableOn ℂ s Ω)
    {Δ : MvPolynomial (Fin n) ℂ} {d : ℕ} (hΔ : Δ.totalDegree ≤ d) (hΔne : Δ ≠ 0)
    (hroot : ∀ z ∈ Ω, (s z) ^ 2 = eval (fun i => z i) Δ)
    {φ : EuclideanSpace ℂ (Fin n) → ℂ} (hφ : SqrtRep Ω s d φ)
    (k : ℕ) (m : Fin k → EuclideanSpace ℂ (Fin n)) :
    SqrtRep Ω s (3 ^ k * d) (fun z => iteratedFDeriv ℂ k φ z m) := by
  obtain ⟨hφc, U, V, W, hW, hU, hV, hWd, hrep⟩ := hφ
  refine ⟨contDiffOn_complex_jet_apply hΩ hφc k m, ?_⟩
  induction k with
  | zero =>
    refine ⟨U, V, W, hW, by simpa using hU, by simpa using hV, by simpa using hWd,
      fun z hz => ?_⟩
    simpa only [iteratedFDeriv_zero_apply] using hrep z hz
  | succ k ih =>
    obtain ⟨Uk, Vk, Wk, hWkne, hUk, hVk, hWk, hkrepr⟩ := ih (Fin.tail m)
    let δ := complexPolynomialDirectional (fun i => m 0 i)
    have hδ : ∀ P : MvPolynomial (Fin n) ℂ,
        P.totalDegree ≤ 3 ^ k * d → (δ P).totalDegree ≤ 3 ^ k * d :=
      fun P hP => (complexPolynomialDirectional_totalDegree (fun i => m 0 i) P).trans hP
    have hΔk : Δ.totalDegree ≤ 3 ^ k * d := hΔ.trans (by
      simpa using Nat.mul_le_mul_right d (one_le_pow₀ (by norm_num : 1 ≤ (3 : ℕ))))
    obtain ⟨hnextU, hnextV, hnextW⟩ :=
      sqrtRationalNext_degrees (3 ^ k * d) δ hδ Δ Uk Vk Wk hΔk hUk hVk hWk
    refine ⟨sqrtRationalNextU δ Δ Uk Wk, sqrtRationalNextV δ Δ Vk Wk,
      sqrtRationalNextW Δ Wk, sqrtRationalNextW_ne_zero Δ Wk hΔne hWkne,
      ?_, ?_, ?_, ?_⟩
    · simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnextU
    · simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnextV
    · simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnextW
    · intro z hz
      have hj := contDiffOn_complex_jet_apply hΩ hφc k (Fin.tail m)
      have heq := frechet_sqrtRationalNext Δ Uk Vk Wk (m 0) Ω hΩ s
        (fun y => iteratedFDeriv ℂ k φ y (Fin.tail m)) hs
        (hj.differentiableOn (by simp)) hroot hkrepr z hz
      have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k φ) z :=
        (hφc.contDiffAt (hΩ.mem_nhds hz)).differentiableAt_iteratedFDeriv (by simp)
      rw [fderiv_continuousMultilinear_apply_const_apply hd] at heq
      simp only [iteratedFDeriv_succ_apply_left]
      exact heq

end SqrtRep

end SqrtRepSection

/-- A presented function with a real slice gives an algebraic real extension of that slice. -/
theorem hasRealExtension_of_sqrtRep {Δ : MvPolynomial (Fin 3) ℂ}
    {s : EuclideanSpace ℂ (Fin 3) → ℂ} {d : ℕ} (hΔ : Δ.totalDegree ≤ d)
    (hroot : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = eval (fun i => z i) Δ)
    {φ : EuclideanSpace ℂ (Fin 3) → ℂ} (hφ : SqrtRep (ball 0 4) s d φ) {g : Base → ℝ}
    (hg : ∀ x ∈ ball (0 : Base) 4, φ (DenseJet.realSlice x) = (g x : ℂ)) :
    HasRealExtension (8 * d + 2) g := by
  obtain ⟨hφc, U, V, W, hW, hU, hV, hWd, hrep⟩ := hφ
  obtain ⟨P, hPne, hPdeg, hP⟩ := exists_sqrt_rational_relation (Y := EuclideanSpace ℂ (Fin 3))
    d Δ U V W hW hΔ hU hV hWd (ball 0 4) (fun z i => z i) s φ hroot hrep
  refine ⟨φ, P, hPne, hPdeg, hφc, hP, fun x hx => ?_⟩
  rw [← DenseJet.realSlice_apply]
  exact hg x hx

/-- **Algebraic extensions of the Hessian and cleared-cubic entries.** For a branch `F` with a
rational presentation in a square root, its real slice `f`, a real affine function `c + L`, a
scale `s0 ≠ 0` and a real potential `Pot` of degree at most `q`, every Hessian entry of
`(f - c - L) / s0` and every entry of its cleared cubic defect against the third derivatives of
`Pot`, divided by `s0`, has an algebraic real extension, of a degree depending only on `D`
and `q`. The extensions are the corresponding complex jets: the Hessian of
`(F - c - L) / s0` in the real coordinate directions, and the cleared formula over `ℂ`. -/
theorem hasRealExtension_hessian_cleared (D q : ℕ) : ∃ D' : ℕ,
  ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ D → U.totalDegree ≤ D →
    V.totalDegree ≤ D → W.totalDegree ≤ D → Δ ≠ 0 → W ≠ 0 →
  ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ), DifferentiableOn ℂ s (Metric.ball 0 4) →
    ContDiffOn ℂ ⊤ F (Metric.ball 0 4) →
    (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = MvPolynomial.eval (fun i => z i) Δ) →
    (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      MvPolynomial.eval (fun i => z i) W * F z =
        MvPolynomial.eval (fun i => z i) U + MvPolynomial.eval (fun i => z i) V * s z) →
  ∀ (f : Base → ℝ), (∀ x ∈ Metric.ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
  ∀ (c s0 : ℝ) (L : Base →L[ℝ] ℝ) (Pot : MvPolynomial (Fin 3) ℝ), s0 ≠ 0 → Pot.totalDegree ≤ q →
    (∀ i j : Fin 3, HasRealExtension D'
      (fun x => FubiniHessian.hessian (fun y => (f y - c - L y) / s0) x i j)) ∧
    (∀ i j k : Fin 3, HasRealExtension D'
      (fun x => ConicTensor.cleared (FubiniHessian.hessian (fun y => (f y - c - L y) / s0) x)
        (FubiniHessian.cubic (fun y => MvPolynomial.eval (fun i => y i) Pot) x) i j k / s0)) := by
  refine ⟨8 * (10000 * (D + q + 1)) + 2, ?_⟩
  intro Δ U V W hΔ hU hV hW hΔne hWne s F hs hF hroot hrep f hfF c s0 L Pot _ hPot
  -- the branch, as a presented function
  have hFrep : SqrtRep (ball 0 4) s D F := ⟨hF, U, V, W, hWne, hU, hV, hW, hrep⟩
  -- the complexified affine part
  let AffP : MvPolynomial (Fin 3) ℂ :=
    C (c : ℂ) + ∑ i : Fin 3, C (L (EuclideanSpace.single i 1) : ℂ) * X i
  have hAffdeg : AffP.totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le (by simp) ((totalDegree_finsetSum _ _).trans
      (Finset.sup_le fun i _ => (totalDegree_mul _ _).trans (by simp))))
  have hAffeval : ∀ z : EuclideanSpace ℂ (Fin 3),
      eval (fun i => z i) AffP = DenseJet.complexAffine c L z := by
    intro z
    simp [AffP, DenseJet.complexAffine]
  -- the complex extension of `(f - c - L) / s0`
  let G : EuclideanSpace ℂ (Fin 3) → ℂ := fun z => (F z - eval (fun i => z i) AffP) / (s0 : ℂ)
  have hGrep : SqrtRep (ball 0 4) s (D + 1) G :=
    (hFrep.sub ((SqrtRep.poly AffP).mono hAffdeg)).div_const _
  have hGreal : ∀ x : Base, ‖x‖ < 4 →
      G (DenseJet.realSlice x) = (((f x - c - L x) / s0 : ℝ) : ℂ) := by
    intro x hx
    have hfx := hfF x (mem_ball_zero_iff.mpr hx)
    have haff := DenseJet.complexAffine_real c L x
    rw [← DenseJet.realSlice_apply] at haff
    simp only [G]
    rw [hfx, hAffeval, haff]
    push_cast
    ring
  -- the Hessian entries
  let Hc : Fin 3 → Fin 3 → EuclideanSpace ℂ (Fin 3) → ℂ := fun a b z =>
    iteratedFDeriv ℂ 2 G z (fun l => DenseJet.realSlice (FubiniJets.basis (![a, b] l)))
  have hHrep : ∀ a b, SqrtRep (ball 0 4) s (9 * (D + 1)) (Hc a b) := fun a b =>
    ((hGrep.iteratedFDeriv_apply isOpen_ball hs (hΔ.trans (by omega)) hΔne hroot 2 _).mono
      (by norm_num))
  have hHreal : ∀ a b, ∀ x : Base, ‖x‖ < 4 → Hc a b (DenseJet.realSlice x) =
      (FubiniHessian.hessian (fun y => (f y - c - L y) / s0) x a b : ℂ) :=
    fun a b x hx => complex_jet_on_real_directions (hGrep.1.of_le le_top) hGreal 2 hx _
  -- the third derivatives of the potential
  let PC : EuclideanSpace ℂ (Fin 3) → ℂ :=
    fun z => eval (fun i => z i) (Pot.map (algebraMap ℝ ℂ))
  have hPCrep : SqrtRep (ball 0 4) s (q + D) PC :=
    (SqrtRep.poly _).mono ((Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ Pot).trans
      (hPot.trans (by omega)))
  have hPCreal : ∀ x : Base, ‖x‖ < 4 →
      PC (DenseJet.realSlice x) = ((eval (fun i => x i) Pot : ℝ) : ℂ) :=
    fun x _ => Submission.Lib.K4QuadraticSheetsReal.eval_map_real Pot (fun i => x i)
  let Tc : Fin 3 → Fin 3 → Fin 3 → EuclideanSpace ℂ (Fin 3) → ℂ := fun a b e z =>
    iteratedFDeriv ℂ 3 PC z (fun l => DenseJet.realSlice (FubiniJets.basis (![a, b, e] l)))
  have hTrep : ∀ a b e, SqrtRep (ball 0 4) s (27 * (q + D)) (Tc a b e) := fun a b e =>
    ((hPCrep.iteratedFDeriv_apply isOpen_ball hs (hΔ.trans (by omega)) hΔne hroot 3 _).mono
      (by norm_num))
  have hTreal : ∀ a b e, ∀ x : Base, ‖x‖ < 4 → Tc a b e (DenseJet.realSlice x) =
      (FubiniHessian.cubic (fun y => eval (fun i => y i) Pot) x a b e : ℂ) :=
    fun a b e x hx => complex_jet_on_real_directions (hPCrep.1.of_le le_top) hPCreal 3 hx _
  refine ⟨fun i j => ?_, fun i j k => ?_⟩
  · exact (hasRealExtension_of_sqrtRep (hΔ.trans (by omega)) hroot (hHrep i j)
      (fun x hx => hHreal i j x (mem_ball_zero_iff.mp hx))).mono_degree (by omega)
  · have hC := (SqrtRep.clearedFormula3 hΔ hroot
      (M := fun z => Matrix.of fun a b => Hc a b z) (T := fun z a b e => Tc a b e z)
      (fun a b => hHrep a b) (fun a b e => hTrep a b e) i j k).div_const (s0 : ℂ)
    refine (hasRealExtension_of_sqrtRep (hΔ.trans (by omega)) hroot hC ?_).mono_degree
      (by omega)
    intro x hx
    have hx' : ‖x‖ < 4 := mem_ball_zero_iff.mp hx
    have hM : (Matrix.of fun a b => Hc a b (DenseJet.realSlice x)) =
        Complex.ofRealHom.mapMatrix
          (FubiniHessian.hessian (fun y => (f y - c - L y) / s0) x) := by
      ext a b
      simp [hHreal a b x hx']
    have hT : (fun a b e => Tc a b e (DenseJet.realSlice x)) = fun a b e =>
        Complex.ofRealHom (FubiniHessian.cubic (fun y => eval (fun i => y i) Pot) x a b e) := by
      funext a b e
      simp [hTreal a b e x hx']
    show clearedFormula (Matrix.of fun a b => Hc a b (DenseJet.realSlice x))
      (fun a b e => Tc a b e (DenseJet.realSlice x)) i j k / (s0 : ℂ) = _
    rw [hM, hT, ← map_clearedFormula, ← cleared_eq_clearedFormula]
    simp [Complex.ofReal_div]

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
