/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.GeneralPolynomialNorming
import Submission.Lib.K4PolynomialNorming.UniformCellNorming
import Submission.Lib.K4PolynomialNorming.FieldCurlStart
import Submission.Lib.K4CubicTests.PolynomialPotential

open Set MeasureTheory ProbabilityTheory MvPolynomial
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

-- The finite-cell exponents here are uniform before choosing the source
-- and cell index types, strengthening the original Root mass draft.
/-- Polynomial norming controls small-value mass under the ORIGINAL base
ceiling; no law conditioned on future successful switches is substituted. -/
theorem original_polynomial_sublevel_mass_bound (D n : ℕ) : ∃ cNorm : ℕ,
    ∀ {X : Type*} [MeasurableSpace X]
      (P : Measure X) (base : X → Fin n → ℝ) (hbase : Measurable base)
      (K : ENNReal) (hcap : P.map base ≤ K • volume)
      (hbox : ∀ᵐ x ∂P, ∀ j, |base x j| ≤ 1)
      (F : MvPolynomial (Fin n) ℝ) (hdegree : F.totalDegree ≤ D)
      (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε)
      (hlarge : ∃ m, A^cNorm*ε < |F.coeff m|),
      P {x | |MvPolynomial.eval (base x) F| ≤ ε} ≤ K*ENNReal.ofReal A⁻¹ := by
  obtain ⟨cNorm,hNorm⟩ := finite_dimensional_real_polynomial_norming D n
  refine ⟨cNorm,?_⟩
  intro X _ P base hbase K hcap hbox F hdegree A ε hA hε hlarge
  let E := {u : Fin n → ℝ | (∀ j, |u j| ≤ 1) ∧ |MvPolynomial.eval u F| ≤ ε}
  have hE : MeasurableSet E := by
    have hb : MeasurableSet {u : Fin n → ℝ | ∀ j, |u j| ≤ 1} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun j => measurableSet_le
        (continuous_abs.measurable.comp (measurable_pi_apply j)) measurable_const)
    exact hb.inter (measurableSet_le
      (continuous_abs.measurable.comp (MvPolynomial.continuous_eval F).measurable) measurable_const)
  have hv : volume E < ENNReal.ofReal A⁻¹ := by
    by_contra hn
    obtain ⟨m,hm⟩ := hlarge
    have h := hNorm F hdegree E hE (fun u hu => hu.1) A ε hA hε (le_of_not_gt hn)
      (fun u hu => hu.2) m
    exact (not_le_of_gt hm) h
  have hm : P {x | |MvPolynomial.eval (base x) F| ≤ ε} = (P.map base) E := by
    rw [Measure.map_apply hbase hE]
    apply measure_congr
    filter_upwards [hbox] with x hx
    simp only [E,Set.mem_preimage,Set.mem_ofPred_eq]
    apply propext
    exact ⟨fun h => ⟨hx,h⟩,fun h => h.2⟩
  rw [hm]
  exact (hcap E).trans (mul_le_mul' le_rfl hv.le)

/-- A large curl coefficient forces a large set of original starting
incidences whenever the original base law has its prepared ceiling. -/
theorem original_large_curl_mass (D : ℕ) : ∃ cNorm : ℕ,
    ∀ {X : Type*} [MeasurableSpace X]
      (P : Measure X) [IsProbabilityMeasure P]
      (base : X → Fin 3 → ℝ) (hbase : Measurable base)
      (K : ENNReal) (hcap : P.map base ≤ K • volume)
      (hbox : ∀ᵐ x ∂P, ∀ j, |base x j| ≤ 1)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ)
      (hdegree : ∀ i j, (pderiv j (T i)-pderiv i (T j)).totalDegree ≤ D)
      (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε)
      (hlarge : ∃ i j m, A^cNorm*ε < |(pderiv j (T i)-pderiv i (T j)).coeff m|),
      1 ≤ P (largeFieldCurlStart T base ε)+K*ENNReal.ofReal A⁻¹ := by
  obtain ⟨cNorm,hNorm⟩ := original_polynomial_sublevel_mass_bound D 3
  refine ⟨cNorm,?_⟩
  intro X _ P _ base hbase K hcap hbox T hdegree A ε hA hε hlarge
  obtain ⟨i,j,m,hm⟩ := hlarge
  let F := pderiv j (T i)-pderiv i (T j)
  have hsmall := hNorm P base hbase K hcap hbox F (hdegree i j) A ε hA hε ⟨m,hm⟩
  have hcover : (Set.univ : Set X) ⊆ largeFieldCurlStart T base ε ∪
      {x | |MvPolynomial.eval (base x) F| ≤ ε} := by
    intro x _
    by_cases hx : x ∈ largeFieldCurlStart T base ε
    · exact Or.inl hx
    · apply Or.inr
      change |MvPolynomial.eval (base x) F| ≤ ε
      refine le_of_not_gt (fun h => hx ?_)
      exact ⟨i,j,by simpa only [F,map_sub] using h⟩
  calc
    _ = P univ := by simp
    _ ≤ P (largeFieldCurlStart T base ε ∪ {x | |MvPolynomial.eval (base x) F| ≤ ε}) :=
      measure_mono hcover
    _ ≤ P (largeFieldCurlStart T base ε)+P {x | |MvPolynomial.eval (base x) F| ≤ ε} :=
      measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hsmall

/-- Finite original cell ceilings give high-curl starting mass even for
singular base laws. The cell variation loss is retained explicitly. -/
theorem original_large_curl_mass_of_cells (D : ℕ) : ∃ cNorm : ℕ,
    ∀ {X ι : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
      (I : Finset ι) (events : ι → Set X) (cells : ι → Set (Fin 3 → ℝ))
      (base : X → Fin 3 → ℝ)
      (hmeas : ∀ i ∈ I, MeasurableSet (cells i))
      (hdisj : (I : Set ι).PairwiseDisjoint cells)
      (hbox : ∀ i ∈ I, ∀ u ∈ cells i, ∀ j, |u j| ≤ 1)
      (hcover : ∀ᵐ x ∂P, x ∈ ⋃ i ∈ I, events i)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ)
      (hdegree : ∀ i j, (pderiv j (T i)-pderiv i (T j)).totalDegree ≤ D)
      (A ε L Δ K : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε) (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (hK : 0 ≤ K)
      (hdiam : ∀ i ∈ I, ∀ x ∈ cells i, ∀ y ∈ cells i, ∀ j, |y j-x j| ≤ Δ)
      (hmap : ∀ i ∈ I, ∀ x ∈ events i, base x ∈ cells i)
      (hcap : ∀ i ∈ I, P (events i) ≤ ENNReal.ofReal K*volume (cells i))
      (hLip : ∀ i j : Fin 3, ∀ x y : Fin 3 → ℝ,
        (∀ k, |x k| ≤ 1) → (∀ k, |y k| ≤ 1) → (∀ k, |y k-x k| ≤ Δ) →
        |MvPolynomial.eval y (pderiv j (T i)-pderiv i (T j))-
          MvPolynomial.eval x (pderiv j (T i)-pderiv i (T j))| ≤ L*Δ)
      (hlarge : ∃ i j m, A^cNorm*(ε+L*Δ) < |(pderiv j (T i)-pderiv i (T j)).coeff m|),
      1 ≤ P (largeFieldCurlStart T base ε)+ENNReal.ofReal (K/A) := by
  obtain ⟨cNorm,hNorm⟩ := finite_cell_polynomial_sublevel_mass_uniform D 3
  refine ⟨cNorm,?_⟩
  intro X ι _ P _ I events cells base hmeas hdisj hbox hcover T hdegree A ε L Δ K hA hε hL hΔ hK
    hdiam hmap hcap hLip hlarge
  obtain ⟨i,j,m,hm⟩ := hlarge
  let F := pderiv j (T i)-pderiv i (T j)
  have hsmall : P {x | x ∈ ⋃ i ∈ I, events i ∧ |MvPolynomial.eval (base x) F| ≤ ε} ≤
      ENNReal.ofReal (K/A) := hNorm F (hdegree i j) P I events cells base hmeas hdisj hbox
      A ε L Δ K hA hε hL hΔ hK hdiam hmap hcap (hLip i j) ⟨m,hm⟩
  have hcover' : (⋃ i ∈ I, events i) ⊆ largeFieldCurlStart T base ε ∪
      {x | x ∈ ⋃ i ∈ I, events i ∧ |MvPolynomial.eval (base x) F| ≤ ε} := by
    intro x hx
    by_cases hg : x ∈ largeFieldCurlStart T base ε
    · exact Or.inl hg
    · refine Or.inr ⟨hx,le_of_not_gt (fun h => hg ?_)⟩
      exact ⟨i,j,by simpa only [F,map_sub] using h⟩
  calc
    _ = P univ := by simp
    _ = P (⋃ i ∈ I, events i) := by
      apply measure_congr
      filter_upwards [hcover] with x hx
      simp only [Set.mem_univ,hx]
    _ ≤ P (largeFieldCurlStart T base ε ∪
        {x | x ∈ ⋃ i ∈ I, events i ∧ |MvPolynomial.eval (base x) F| ≤ ε}) := measure_mono hcover'
    _ ≤ P (largeFieldCurlStart T base ε)+
        P {x | x ∈ ⋃ i ∈ I, events i ∧ |MvPolynomial.eval (base x) F| ≤ ε} := measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hsmall

/-- Coarse original base ceilings suffice for coefficient conservativity;
no density assumption is imposed on the original starting law. -/
theorem original_curl_coefficients_of_cell_mass_budget (D : ℕ) : ∃ cNorm : ℕ,
    ∀ {X ι : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
      (I : Finset ι) (events : ι → Set X) (cells : ι → Set (Fin 3 → ℝ))
      (base : X → Fin 3 → ℝ)
      (hmeas : ∀ i ∈ I, MeasurableSet (cells i))
      (hdisj : (I : Set ι).PairwiseDisjoint cells)
      (hbox : ∀ i ∈ I, ∀ u ∈ cells i, ∀ j, |u j| ≤ 1)
      (hcover : ∀ᵐ x ∂P, x ∈ ⋃ i ∈ I, events i)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ)
      (hdegree : ∀ i j, (pderiv j (T i)-pderiv i (T j)).totalDegree ≤ D)
      (A ε L Δ K : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε) (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (hK : 0 ≤ K)
      (hdiam : ∀ i ∈ I, ∀ x ∈ cells i, ∀ y ∈ cells i, ∀ j, |y j-x j| ≤ Δ)
      (hmap : ∀ i ∈ I, ∀ x ∈ events i, base x ∈ cells i)
      (hcap : ∀ i ∈ I, P (events i) ≤ ENNReal.ofReal K*volume (cells i))
      (hLip : ∀ i j : Fin 3, ∀ x y : Fin 3 → ℝ,
        (∀ k, |x k| ≤ 1) → (∀ k, |y k| ≤ 1) → (∀ k, |y k-x k| ≤ Δ) →
        |MvPolynomial.eval y (pderiv j (T i)-pderiv i (T j))-
          MvPolynomial.eval x (pderiv j (T i)-pderiv i (T j))| ≤ L*Δ)
      (J Bound : ENNReal)
      (hupper : J*P (largeFieldCurlStart T base ε) ≤ Bound)
      (hbudget : Bound+J*ENNReal.ofReal (K/A) < J),
      ∀ i j m, |(pderiv j (T i)-pderiv i (T j)).coeff m| ≤ A^cNorm*(ε+L*Δ) := by
  obtain ⟨cNorm,hNorm⟩ := original_large_curl_mass_of_cells D
  refine ⟨cNorm,?_⟩
  intro X ι _ P _ I events cells base hmeas hdisj hbox hcover T hdegree A ε L Δ K hA hε hL hΔ hK
    hdiam hmap hcap hLip J Bound hupper hbudget i j m
  by_contra hn
  have hlower := hNorm P I events cells base hmeas hdisj hbox hcover T hdegree
    A ε L Δ K hA hε hL hΔ hK hdiam hmap hcap hLip ⟨i,j,m,lt_of_not_ge hn⟩
  have hscaled : J ≤ J*P (largeFieldCurlStart T base ε)+J*ENNReal.ofReal (K/A) := by
    simpa only [mul_one,mul_add] using mul_le_mul' le_rfl hlower
  exact (not_le_of_gt hbudget) (hscaled.trans (add_le_add hupper le_rfl))

/-- A strict original-law mass budget rules out every large skew coefficient. -/
theorem original_curl_coefficients_of_mass_budget (D : ℕ) : ∃ cNorm : ℕ,
    ∀ {X : Type*} [MeasurableSpace X]
      (P : Measure X) [IsProbabilityMeasure P]
      (base : X → Fin 3 → ℝ) (hbase : Measurable base)
      (K : ENNReal) (hcap : P.map base ≤ K • volume)
      (hbox : ∀ᵐ x ∂P, ∀ j, |base x j| ≤ 1)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ)
      (hdegree : ∀ i j, (pderiv j (T i)-pderiv i (T j)).totalDegree ≤ D)
      (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε)
      (J Bound : ENNReal)
      (hupper : J*P (largeFieldCurlStart T base ε) ≤ Bound)
      (hbudget : Bound+J*(K*ENNReal.ofReal A⁻¹) < J),
      ∀ i j m, |(pderiv j (T i)-pderiv i (T j)).coeff m| ≤ A^cNorm*ε := by
  obtain ⟨cNorm,hNorm⟩ := original_large_curl_mass D
  refine ⟨cNorm,?_⟩
  intro X _ P _ base hbase K hcap hbox T hdegree A ε hA hε J Bound hupper hbudget i j m
  by_contra hn
  have hlower := hNorm P base hbase K hcap hbox T hdegree A ε hA hε
    ⟨i,j,m,lt_of_not_ge hn⟩
  have hscaled : J ≤ J*P (largeFieldCurlStart T base ε)+J*(K*ENNReal.ofReal A⁻¹) := by
    simpa only [mul_one,mul_add] using mul_le_mul' le_rfl hlower
  exact (not_le_of_gt hbudget) (hscaled.trans (add_le_add hupper le_rfl))

/-- The potential is constructed from the original field once the original
mass contradiction has bounded its curl coefficients. -/
theorem original_polynomial_potential_of_mass_budget (D : ℕ) : ∃ cNorm : ℕ,
    ∀ {X : Type*} [MeasurableSpace X]
      (P : Measure X) [IsProbabilityMeasure P]
      (base : X → Fin 3 → ℝ) (hbase : Measurable base)
      (K : ENNReal) (hcap : P.map base ≤ K • volume)
      (hbox : ∀ᵐ x ∂P, ∀ j, |base x j| ≤ 1)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (hdegree : ∀ i, (T i).totalDegree ≤ D)
      (hdegreeCurl : ∀ i j, (pderiv j (T i)-pderiv i (T j)).totalDegree ≤ D)
      (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε)
      (J Bound : ENNReal)
      (hupper : J*P (largeFieldCurlStart T base ε) ≤ Bound)
      (hbudget : Bound+J*(K*ENNReal.ofReal A⁻¹) < J),
      ∃ Q : MvPolynomial (Fin 3) ℝ, Q.totalDegree ≤ D+1 ∧
        ∀ (B : ℝ), 0 ≤ B → ∀ x : Fin 3 → ℝ, (∀ i, |x i| ≤ B) → ∀ j,
          |MvPolynomial.eval x (pderiv j Q)-MvPolynomial.eval x (T j)| ≤
            ((D+1:ℕ):ℝ)^2*3*(max 1 (3*B))^D*(A^cNorm*ε) := by
  obtain ⟨cNorm,hNorm⟩ := original_curl_coefficients_of_mass_budget D
  refine ⟨cNorm,?_⟩
  intro X _ P _ base hbase K hcap hbox T hdegree hdegreeCurl A ε hA hε J Bound hupper hbudget
  have hskew := hNorm P base hbase K hcap hbox T hdegreeCurl A ε hA hε J Bound hupper hbudget
  refine ⟨Submission.Lib.K4CubicTests.polynomialRadialPotential T D,
    Submission.Lib.K4CubicTests.polynomialRadialPotential_totalDegree_le T D,?_⟩
  intro B hB x hx j
  simpa only [Fintype.card_fin,Nat.cast_ofNat,Nat.cast_pow] using
    Submission.Lib.K4CubicTests.polynomialRadialPotential_eval_error_le T D hdegree
      (A^cNorm*ε) B (mul_nonneg (pow_nonneg (by linarith) _) hε) hB hskew x hx j

/-- An original finite-cell mass budget produces the polynomial potential,
with the mesh variation loss retained in the gradient approximation. -/
theorem original_polynomial_potential_of_cell_mass_budget (D : ℕ) : ∃ cNorm : ℕ,
    ∀ {X ι : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
      (I : Finset ι) (events : ι → Set X) (cells : ι → Set (Fin 3 → ℝ))
      (base : X → Fin 3 → ℝ)
      (hmeas : ∀ i ∈ I, MeasurableSet (cells i))
      (hdisj : (I : Set ι).PairwiseDisjoint cells)
      (hbox : ∀ i ∈ I, ∀ u ∈ cells i, ∀ j, |u j| ≤ 1)
      (hcover : ∀ᵐ x ∂P, x ∈ ⋃ i ∈ I, events i)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (hdegree : ∀ i, (T i).totalDegree ≤ D)
      (hdegreeCurl : ∀ i j, (pderiv j (T i)-pderiv i (T j)).totalDegree ≤ D)
      (A ε L Δ K : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε) (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (hK : 0 ≤ K)
      (hdiam : ∀ i ∈ I, ∀ x ∈ cells i, ∀ y ∈ cells i, ∀ j, |y j-x j| ≤ Δ)
      (hmap : ∀ i ∈ I, ∀ x ∈ events i, base x ∈ cells i)
      (hcap : ∀ i ∈ I, P (events i) ≤ ENNReal.ofReal K*volume (cells i))
      (hLip : ∀ i j : Fin 3, ∀ x y : Fin 3 → ℝ,
        (∀ k, |x k| ≤ 1) → (∀ k, |y k| ≤ 1) → (∀ k, |y k-x k| ≤ Δ) →
        |MvPolynomial.eval y (pderiv j (T i)-pderiv i (T j))-
          MvPolynomial.eval x (pderiv j (T i)-pderiv i (T j))| ≤ L*Δ)
      (J Bound : ENNReal)
      (hupper : J*P (largeFieldCurlStart T base ε) ≤ Bound)
      (hbudget : Bound+J*ENNReal.ofReal (K/A) < J),
      ∃ Q : MvPolynomial (Fin 3) ℝ, Q.totalDegree ≤ D+1 ∧
        ∀ (B : ℝ), 0 ≤ B → ∀ x : Fin 3 → ℝ, (∀ i, |x i| ≤ B) → ∀ j,
          |MvPolynomial.eval x (pderiv j Q)-MvPolynomial.eval x (T j)| ≤
            ((D+1:ℕ):ℝ)^2*3*(max 1 (3*B))^D*(A^cNorm*(ε+L*Δ)) := by
  obtain ⟨cNorm,hNorm⟩ := original_curl_coefficients_of_cell_mass_budget D
  refine ⟨cNorm,?_⟩
  intro X ι _ P _ I events cells base hmeas hdisj hbox hcover T hdegree hdegreeCurl A ε L Δ K
    hA hε hL hΔ hK hdiam hmap hcap hLip J Bound hupper hbudget
  have hskew := hNorm P I events cells base hmeas hdisj hbox hcover T hdegreeCurl
    A ε L Δ K hA hε hL hΔ hK hdiam hmap hcap hLip J Bound hupper hbudget
  refine ⟨Submission.Lib.K4CubicTests.polynomialRadialPotential T D,
    Submission.Lib.K4CubicTests.polynomialRadialPotential_totalDegree_le T D,?_⟩
  intro B hB x hx j
  simpa only [Fintype.card_fin,Nat.cast_ofNat,Nat.cast_pow] using
    Submission.Lib.K4CubicTests.polynomialRadialPotential_eval_error_le T D hdegree
      (A^cNorm*(ε+L*Δ)) B
      (mul_nonneg (pow_nonneg (by linarith) _) (add_nonneg hε (mul_nonneg hL hΔ))) hB hskew x hx j


end Submission.Lib.K4PolynomialNorming
