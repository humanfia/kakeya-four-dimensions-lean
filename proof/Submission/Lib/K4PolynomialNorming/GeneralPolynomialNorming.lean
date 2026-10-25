/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.RemezPowers
import Submission.Lib.K4PolynomialNorming.NormingCoordinates

open Set MeasureTheory MvPolynomial

namespace Submission.Lib.K4PolynomialNorming

/-- In every fixed finite dimension and degree, observation mass at least
A^-1 gives coefficient norming with a fixed power of A. -/
theorem finite_dimensional_complex_polynomial_norming (D : ℕ) : ∀ n : ℕ, ∃ C : ℕ,
    ∀ (F : MvPolynomial (Fin n) ℂ), F.totalDegree ≤ D →
      ∀ E : Set (Fin n → ℝ), MeasurableSet E → (∀ u ∈ E, ∀ i, |u i| ≤ 1) →
        ∀ A ε : ℝ, 2 ≤ A → 0 ≤ ε → ENNReal.ofReal A⁻¹ ≤ volume E →
          (∀ u ∈ E, ‖MvPolynomial.eval (fun i => (u i : ℂ)) F‖ ≤ ε) →
            ∀ m : Fin n →₀ ℕ, ‖F.coeff m‖ ≤ A ^ C * ε := by
  classical
  intro n
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      intro F hD E hE hbox A ε hA hε hmass hsmall m
      have hne : E.Nonempty := by
        by_contra hn
        have he : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
        have hz : ENNReal.ofReal A⁻¹ ≤ 0 := by simpa [he] using hmass
        have hpos : (0 : ENNReal) < ENNReal.ofReal A⁻¹ := ENNReal.ofReal_pos.mpr (inv_pos.mpr (by linarith : 0 < A))
        exact (not_le_of_gt hpos) hz
      obtain ⟨u, hu⟩ := hne
      have hF : F = C (F.coeff 0) := by
        ext v
        have hv : v = 0 := Subsingleton.elim _ _
        subst v
        simp
      have heval : MvPolynomial.eval (fun i => (u i : ℂ)) F = F.coeff 0 := by
        conv_lhs => rw [hF]
        rw [eval_C]
      have hm : m = 0 := Subsingleton.elim _ _
      simpa only [heval, hm, pow_zero, one_mul] using hsmall u hu
  | succ n ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨(n + 3) * (C + D * (D + 10)), ?_⟩
      intro F hD E hE hbox A ε hA hε hmass hsmall m
      let B : ℝ := A ^ (n + 3)
      obtain ⟨hB, hB4, hBn⟩ := norming_enlargement_bounds A hA n
      have hApos : 0 < A := by linarith
      have hBpos : 0 < B := by dsimp [B]; positivity
      have hmass4 : B⁻¹ ≤ A⁻¹ / 4 := by
        simpa only [one_div, mul_inv_rev, div_eq_mul_inv, one_mul, B] using
          one_div_le_one_div_of_le (by positivity : (0:ℝ) < 4 * A) hB4
      have hmassn : B⁻¹ ≤ A⁻¹ / (2 * (2:ℝ)^n) := by
        simpa only [one_div, mul_inv_rev, div_eq_mul_inv, one_mul, B] using
          one_div_le_one_div_of_le (by positivity : (0:ℝ) < (2 * (2:ℝ)^n) * A) hBn
      let e := splitHeadCoordinates n
      let E' : Set ((Fin n → ℝ) × ℝ) := e.symm ⁻¹' E
      have hE' : MeasurableSet E' := e.symm.measurable hE
      have hvol : (volume.prod volume) E' = volume E :=
        (splitHeadCoordinates_measurePreserving n).symm.measure_preimage hE.nullMeasurableSet
      have hrect : E' ⊆ Set.Icc (-1 : Fin n → ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
        rintro ⟨x,t⟩ hxt
        have hc := hbox (e.symm (x,t)) hxt
        have hx (j : Fin n) : |x j| ≤ 1 := by
          simpa only [e, splitHeadCoordinates_symm_apply, Fin.cons_succ] using hc j.succ
        have ht : |t| ≤ 1 := by
          simpa only [e, splitHeadCoordinates_symm_apply, Fin.cons_zero] using hc 0
        exact ⟨⟨fun j => (abs_le.mp (hx j)).1, fun j => (abs_le.mp (hx j)).2⟩, abs_le.mp ht⟩
      obtain ⟨G, hGm, hGS, hGmass, hfib⟩ := exists_many_large_fibers
        volume volume (Set.Icc (-1 : Fin n → ℝ) 1) (Set.Icc (-1 : ℝ) 1) E'
        measurableSet_Icc hE' hrect ((2:ℝ)^n) 2 A⁻¹ (by positivity) (by norm_num) (inv_pos.mpr hApos)
        (volume_unit_coordinate_box n).le (by norm_num) (by simpa only [hvol] using hmass)
      have hGmassB : ENNReal.ofReal B⁻¹ ≤ volume G :=
        (ENNReal.ofReal_le_ofReal hmass4).trans (by simpa only [show (2:ℝ) * 2 = 4 by norm_num] using hGmass)
      let P := finSuccEquiv ℂ n F
      have houter : P.natDegree ≤ D :=
        ((natDegree_finSuccEquiv F).trans_le (degreeOf_le_totalDegree F 0)).trans hD
      have hpoint (k : ℕ) (x : Fin n → ℝ) (hx : x ∈ G) :
          ‖MvPolynomial.eval (fun i => (x i : ℂ)) (P.coeff k)‖ ≤ B ^ (D * (D + 10)) * ε := by
        let q : Polynomial ℂ := P.map (MvPolynomial.eval (fun i => (x i : ℂ)))
        have hq : q.natDegree ≤ D := Polynomial.natDegree_map_le.trans houter
        have hfibB : ENNReal.ofReal B⁻¹ ≤ volume (Prod.mk x ⁻¹' E') :=
          (ENNReal.ofReal_le_ofReal hmassn).trans (hfib x hx)
        have h := complex_polynomial_coeff_le_of_small_values q D hq (Prod.mk x ⁻¹' E')
          B⁻¹ 1 ε (inv_pos.mpr hBpos) (by norm_num) hε hfibB
          (fun t ht => abs_le.mpr (hrect ht).2)
          (fun t ht => by
            have hs := hsmall (e.symm (x,t)) ht
            have hv : (fun i : Fin (n + 1) => ((Fin.cons t x : Fin (n + 1) → ℝ) i : ℂ)) =
                (Fin.cons (t:ℂ) (fun i : Fin n => (x i : ℂ)) : Fin (n + 1) → ℂ) := by
              funext i
              exact Fin.cases rfl (fun j => rfl) i
            rw [show q.eval (t:ℂ) = MvPolynomial.eval (Fin.cons (t:ℂ) (fun i => (x i : ℂ))) F from
              (eval_eq_eval_mv_eval' (fun i => (x i : ℂ)) (t:ℂ) F).symm]
            simpa only [e, splitHeadCoordinates_symm_apply, hv] using hs) k
        have hb : 1 + 4 * (D + 1 : ℕ) * (1 + (1:ℝ)) / B⁻¹ = 1 + 8 * (D + 1 : ℕ) / B⁻¹ := by ring
        rw [hb] at h
        have h' : ‖MvPolynomial.eval (fun i => (x i : ℂ)) (P.coeff k)‖ ≤
            (1 + 8 * (D + 1 : ℕ) / B⁻¹) ^ D * ε := by
          simpa only [q, Polynomial.coeff_map] using h
        exact h'.trans (by simpa only [one_mul] using
          remez_loss_le_power B hB D 1 8 ε (by norm_num) (by norm_num) hε)
      have hcoeff := hC (P.coeff (m 0))
        ((finSuccEquiv_coeff_totalDegree_le F (m 0)).trans hD) G hGm
        (fun x hx i => abs_le.mpr ⟨(hGS hx).1 i, (hGS hx).2 i⟩)
        B (B ^ (D * (D + 10)) * ε) hB (by positivity) hGmassB (hpoint (m 0)) m.tail
      have hcoeff' : ‖F.coeff m‖ ≤ B ^ C * (B ^ (D * (D + 10)) * ε) := by
        simpa only [P, finSuccEquiv_coeff_coeff, Finsupp.cons_tail] using hcoeff
      calc
        _ ≤ B ^ C * (B ^ (D * (D + 10)) * ε) := hcoeff'
        _ = _ := by
          rw [← mul_assoc, ← pow_add]
          dsimp [B]
          rw [← pow_mul]


/-- Real coefficient norming in every finite dimension, in ordinary coordinate
Lebesgue measure. -/
theorem finite_dimensional_real_polynomial_norming (D n : ℕ) : ∃ C : ℕ,
    ∀ (F : MvPolynomial (Fin n) ℝ), F.totalDegree ≤ D →
      ∀ E : Set (Fin n → ℝ), MeasurableSet E → (∀ u ∈ E, ∀ i, |u i| ≤ 1) →
        ∀ A ε : ℝ, 2 ≤ A → 0 ≤ ε → ENNReal.ofReal A⁻¹ ≤ volume E →
          (∀ u ∈ E, |MvPolynomial.eval u F| ≤ ε) →
            ∀ m : Fin n →₀ ℕ, |F.coeff m| ≤ A ^ C * ε := by
  obtain ⟨C, hC⟩ := finite_dimensional_complex_polynomial_norming D n
  refine ⟨C, ?_⟩
  intro F hD E hE hbox A ε hA hε hmass hsmall m
  have hd : (MvPolynomial.map (algebraMap ℝ ℂ) F).totalDegree ≤ D :=
    (show (MvPolynomial.map (algebraMap ℝ ℂ) F).totalDegree ≤ F.totalDegree from by
      unfold MvPolynomial.totalDegree
      exact Finset.sup_mono (support_map_subset (algebraMap ℝ ℂ) F)).trans hD
  have h := hC (MvPolynomial.map (algebraMap ℝ ℂ) F) hd E hE hbox A ε hA hε hmass
    (fun u hu => by rw [norm_eval_complexification]; exact hsmall u hu) m
  rw [coeff_map] at h
  change ‖(F.coeff m : ℂ)‖ ≤ _ at h
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

/-- A Mathlib-only Euclidean interface: the loss exponent depends only on
dimension and polynomial degree, including dimensions four and six. -/
theorem euclidean_polynomial_norming (D n : ℕ) : ∃ C : ℕ, 1 ≤ C ∧
    ∀ (F : MvPolynomial (Fin n) ℝ), F.totalDegree ≤ D →
      ∀ E : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet E → (∀ u ∈ E, ∀ i, |u i| ≤ 1) →
        ∀ A ε : ℝ, 2 ≤ A → 0 ≤ ε → ENNReal.ofReal A⁻¹ ≤ volume E →
          (∀ u ∈ E, |MvPolynomial.eval (fun i => u i) F| ≤ ε) →
            ∀ m : Fin n →₀ ℕ, |F.coeff m| ≤ A ^ C * ε := by
  obtain ⟨C, hC⟩ := finite_dimensional_real_polynomial_norming D n
  refine ⟨C + 1, by omega, ?_⟩
  intro F hD E hE hbox A ε hA hε hmass hsmall m
  have hp := PiLp.volume_preserving_toLp (Fin n)
  have h := hC F hD (WithLp.toLp 2 ⁻¹' E) (hp.measurable hE)
    (fun u hu i => hbox (WithLp.toLp 2 u) hu i) A ε hA hε
    (by simpa only [hp.measure_preimage hE.nullMeasurableSet] using hmass)
    (fun u hu => hsmall (WithLp.toLp 2 u) hu) m
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by linarith : 1 ≤ A) (Nat.le_succ C)) hε)

/-- A nontrivial coefficient forces the sufficiently small sublevel region
inside the unit coordinate box to have arbitrarily small reciprocal-power
volume. This is the regular-minor deletion form of polynomial norming. -/
theorem euclidean_polynomial_sublevel_volume (D n : ℕ) : ∃ C : ℕ, 1 ≤ C ∧
    ∀ (F : MvPolynomial (Fin n) ℝ), F.totalDegree ≤ D →
      ∀ E : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet E → (∀ u ∈ E, ∀ i, |u i| ≤ 1) →
        ∀ A ε M : ℝ, 2 ≤ A → 0 ≤ ε → A ^ C * ε < M →
          (∃ m, M ≤ |F.coeff m|) →
            (∀ u ∈ E, |MvPolynomial.eval (fun i => u i) F| ≤ ε) → volume E < ENNReal.ofReal A⁻¹ := by
  obtain ⟨C, hCpos, hC⟩ := euclidean_polynomial_norming D n
  refine ⟨C, hCpos, ?_⟩
  intro F hD E hE hbox A ε M hA hε hgap hlarge hsmall
  by_contra hnot
  have hmass : ENNReal.ofReal A⁻¹ ≤ volume E := le_of_not_gt hnot
  obtain ⟨m, hm⟩ := hlarge
  exact (not_le_of_gt hgap) (hm.trans (hC F hD E hE hbox A ε hA hε hmass hsmall m))

end Submission.Lib.K4PolynomialNorming
