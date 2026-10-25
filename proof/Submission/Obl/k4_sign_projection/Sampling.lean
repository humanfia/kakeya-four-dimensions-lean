/- From o050 session x0170, commit 56b4456 (branch tip e18e298).
   Integrated with the locally proved sampler and parametric Tarski queries. -/
import Submission.Obl.k4_sign_projection.RootSampling
import Submission.Obl.k4_sign_projection.Queries

noncomputable section

namespace Submission.Obl.k4_sign_projection

open scoped BigOperators Classical

/-- The product has a distinguished real root even if the selected family is empty. -/
def coveringPolynomial {η R : Type} [CommRing R]
    (p : η → Polynomial R) (S : Finset η) : Polynomial R :=
  Polynomial.X * ∏ i ∈ S, p i

/-- Roots, critical points, and points beyond the two extreme roots. -/
def samplePolynomial {R : Type} [CommRing R] (q : Polynomial R) : Polynomial R :=
  q * q.derivative * q.comp (Polynomial.X - Polynomial.C 1) *
    q.comp (Polynomial.X + Polynomial.C 1)

/-- Trying all subsets includes the subset of the specialized nonzero polynomials. -/
def samples {η R : Type} [CommRing R] (p : η → Polynomial R)
    (S : Finset η) : Polynomial R :=
  samplePolynomial (coveringPolynomial p S)

/-- The sampling polynomials have coefficients polynomial in all parameters. -/
@[simp] theorem specialize_samples {ι η : Type} (x : ι → ℝ)
    (p : η → Polynomial (MvPolynomial ι ℝ)) (S : Finset η) :
    specializePoly x (samples p S) = samples (fun i => specializePoly x (p i)) S := by
  simp [specializePoly, samples, samplePolynomial, coveringPolynomial,
    Polynomial.map_comp, Polynomial.map_prod, ← Polynomial.derivative_map]

/-- Scalar feasibility is exactly feasibility at a root of one of the
finitely many sampling polynomials. -/
theorem feasible_iff_samples {η : Type} [Fintype η]
    (p : η → Polynomial ℝ) (B : Set (η → SignType)) :
    (∃ t, signsAt p t ∈ B) ↔
      ∃ S : Finset η, ∃ u ∈ (samples p S).roots.toFinset, signsAt p u ∈ B := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    let S : Finset η := Finset.univ.filter (fun i => p i ≠ 0)
    let q := coveringPolynomial p S
    have hq : q ≠ 0 := by
      apply mul_ne_zero Polynomial.X_ne_zero
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hq0 : q.eval 0 = 0 := by simp [q, coveringPolynomial]
    have hp (i : η) : p i = 0 ∨ p i ∣ q := by
      by_cases hi : p i = 0
      · exact Or.inl hi
      · refine Or.inr (dvd_mul_of_dvd_right ?_ _)
        exact Finset.dvd_prod_of_mem p (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    obtain ⟨u, hu, hs⟩ := root_sampling η p q hq hq0 hp t
    refine ⟨S, u, ?_, ?_⟩
    · exact Multiset.mem_toFinset.mpr hu
    · have he : signsAt p u = signsAt p t := funext hs
      exact he ▸ ht
  · rintro ⟨S, u, hu, hB⟩
    exact ⟨u, hB⟩

end Submission.Obl.k4_sign_projection
