/- From o050 session x0170, commit 56b4456 (branch tip e18e298).
   Integrated with the locally proved sampler and parametric Tarski queries. -/
import Submission.Obl.k4_sign_projection.ParametricQuery
import Submission.Obl.k4_sign_projection.SignMoments

noncomputable section

namespace Submission.Obl.k4_sign_projection

open scoped BigOperators Classical

/-- A signed query counts distinct roots, with weights in `{-1,0,1}`. -/
def rootQuery (f g : Polynomial ℝ) : ℚ :=
  ∑ r ∈ f.roots.toFinset, (SignType.sign (g.eval r) : ℚ)

/-- Polynomial specialization in the retained real coordinates. -/
def specializePoly {ι : Type} (x : ι → ℝ)
    (f : Polynomial (MvPolynomial ι ℝ)) : Polynomial ℝ :=
  f.map (MvPolynomial.eval x)

/-- Apply the single-query child to a chosen parameter-polynomial pair. -/
theorem exists_query_tests (ι : Type) [Fintype ι]
    (f g : Polynomial (MvPolynomial ι ℝ)) :
    ∃ (n : ℕ) (q : Fin n → MvPolynomial ι ℝ),
      ∀ x y : ι → ℝ,
        (∀ j, SignType.sign (MvPolynomial.eval x (q j)) =
          SignType.sign (MvPolynomial.eval y (q j))) →
        rootQuery (specializePoly x f) (specializePoly x g) =
          rootQuery (specializePoly y f) (specializePoly y g) :=
  by
    obtain ⟨n, q, hq⟩ := parametric_tarski_query f g
    exact ⟨n, q, fun x y hxy => hq x y (funext hxy)⟩

/-- Choose test lists simultaneously for a finite family of signed queries. -/
theorem exists_simultaneous_query_tests {ι J : Type} [Fintype ι] [Fintype J]
    (f g : J → Polynomial (MvPolynomial ι ℝ)) :
    ∃ (n : J → ℕ) (q : (j : J) → Fin (n j) → MvPolynomial ι ℝ),
      ∀ x y : ι → ℝ,
        (∀ j k, SignType.sign (MvPolynomial.eval x (q j k)) =
          SignType.sign (MvPolynomial.eval y (q j k))) →
        ∀ j, rootQuery (specializePoly x (f j)) (specializePoly x (g j)) =
          rootQuery (specializePoly y (f j)) (specializePoly y (g j)) := by
  classical
  choose n q hq using fun j => exists_query_tests ι (f j) (g j)
  exact ⟨n, q, fun x y h j => hq j x y (h j)⟩

/-- The sign vector at a real point for a univariate polynomial family. -/
def signsAt {η : Type} (p : η → Polynomial ℝ) (r : ℝ) : η → SignType :=
  fun i => SignType.sign ((p i).eval r)

/-- The rational number of distinct roots with a given sign vector. -/
def rootWeight {η : Type} (f : Polynomial ℝ) (p : η → Polynomial ℝ)
    (s : η → SignType) : ℚ :=
  ((f.roots.toFinset.filter (fun r => signsAt p r = s)).card : ℚ)

/-- Root weights are positive precisely for sign vectors occurring at roots. -/
theorem rootWeight_pos_iff {η : Type} (f : Polynomial ℝ) (p : η → Polynomial ℝ)
    (s : η → SignType) :
    0 < rootWeight f p s ↔ ∃ r ∈ f.roots.toFinset, signsAt p r = s := by
  classical
  have hc : 0 < (f.roots.toFinset.filter (fun r => signsAt p r = s)).card ↔
      ∃ r ∈ f.roots.toFinset, signsAt p r = s := by
    rw [Finset.card_pos]
    simp only [Finset.Nonempty, Finset.mem_filter]
  change (0 : ℚ) < ((f.roots.toFinset.filter (fun r => signsAt p r = s)).card : ℚ) ↔ _
  exact_mod_cast hc

/-- Casting the sign commutes with a finite real product. -/
lemma sign_cast_finset_prod {η : Type} (S : Finset η) (v : η → ℝ) :
    (SignType.sign (∏ i ∈ S, v i) : ℚ) = ∏ i ∈ S, (SignType.sign (v i) : ℚ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi, sign_mul, SignType.coe_mul, ih]

/-- A monomial moment of the root signs is a signed polynomial root query. -/
theorem rootQuery_monomial {η : Type} (f : Polynomial ℝ)
    (p : η → Polynomial ℝ) (e : η →₀ ℕ) :
    rootQuery f (e.prod (fun i n => p i ^ n)) =
      ∑ r ∈ f.roots.toFinset, e.prod (fun i n => (signsAt p r i : ℚ) ^ n) := by
  classical
  unfold rootQuery
  simp only [Finsupp.prod, Polynomial.eval_prod, Polynomial.eval_pow,
    sign_cast_finset_prod, sign_pow, SignType.coe_pow, signsAt]

/-- Interpolation on the finite sign cube recovers every root sign count
from its fixed finite collection of signed queries. -/
theorem rootWeights_eq_of_queries {η : Type} [Fintype η]
    (f₁ f₂ : Polynomial ℝ) (p₁ p₂ : η → Polynomial ℝ)
    (h : ∀ e ∈ Moments.signMomentExponents η,
      rootQuery f₁ (e.prod (fun i n => p₁ i ^ n)) =
        rootQuery f₂ (e.prod (fun i n => p₂ i ^ n))) :
    rootWeight f₁ p₁ = rootWeight f₂ p₂ := by
  funext s
  have hc := Moments.finite_sign_counts_of_fixed_moments f₁.roots.toFinset f₂.roots.toFinset
    (signsAt p₁) (signsAt p₂) (fun e he => by
      simpa only [rootQuery_monomial] using h e he) s
  convert congrArg (fun n : ℕ => (n : ℚ)) hc using 1 <;>
    unfold rootWeight <;> congr 2 <;> ext r <;> simp only [Finset.mem_filter]

/-- In particular accepted sign patterns occur at roots on both sides. -/
theorem exists_root_signs_iff_of_queries {η : Type} [Fintype η]
    (f₁ f₂ : Polynomial ℝ) (p₁ p₂ : η → Polynomial ℝ) (B : Set (η → SignType))
    (h : ∀ e ∈ Moments.signMomentExponents η,
      rootQuery f₁ (e.prod (fun i n => p₁ i ^ n)) =
        rootQuery f₂ (e.prod (fun i n => p₂ i ^ n))) :
    (∃ r ∈ f₁.roots.toFinset, signsAt p₁ r ∈ B) ↔
      ∃ r ∈ f₂.roots.toFinset, signsAt p₂ r ∈ B := by
  have hw := rootWeights_eq_of_queries f₁ f₂ p₁ p₂ h
  constructor
  · rintro ⟨r, hr, hB⟩
    have hpos := (rootWeight_pos_iff f₁ p₁ (signsAt p₁ r)).mpr ⟨r, hr, rfl⟩
    rw [congrFun hw (signsAt p₁ r)] at hpos
    obtain ⟨u, hu, hs⟩ := (rootWeight_pos_iff f₂ p₂ _).mp hpos
    exact ⟨u, hu, hs ▸ hB⟩
  · rintro ⟨r, hr, hB⟩
    have hpos := (rootWeight_pos_iff f₂ p₂ (signsAt p₂ r)).mpr ⟨r, hr, rfl⟩
    rw [← congrFun hw (signsAt p₂ r)] at hpos
    obtain ⟨u, hu, hs⟩ := (rootWeight_pos_iff f₁ p₁ _).mp hpos
    exact ⟨u, hu, hs ▸ hB⟩

end Submission.Obl.k4_sign_projection
