import Submission.Obl.k4_scalar_conditional_crop_worlds.Formats
import Submission.Obl.k4_eligibility_sign_description.Signs
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat

open MvPolynomial Finset Set

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

/-- Positive scalar normalization bounds every polynomial coefficient and preserves all signs. -/
lemma bounded_sign_polynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    ∃ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ p.totalDegree ∧
      (∀ b, |q.coeff b| ≤ 1) ∧ ∀ x, SignType.sign (eval x q) = SignType.sign (eval x p) := by
  classical
  let c : ℝ := 1 + ∑ b ∈ p.support, |p.coeff b|
  have hc : 0 < c := by dsimp [c]; positivity
  have hb (b : Fin n →₀ ℕ) : |p.coeff b| ≤ c := by
    by_cases h : b ∈ p.support
    · have := Finset.single_le_sum (fun d (_ : d ∈ p.support) => abs_nonneg (p.coeff d)) h
      dsimp [c]
      linarith
    · have : p.coeff b = 0 := by simpa only [MvPolynomial.mem_support_iff, not_not] using h
      rw [this, abs_zero]
      exact hc.le
  refine ⟨C c⁻¹ * p, k4_eligibility_sign_description.degree_C_mul_le _ _, ?_, ?_⟩
  · intro b
    rw [coeff_C_mul, abs_mul, abs_inv, abs_of_pos hc, mul_comm, ← div_eq_mul_inv]
    exact (div_le_one hc).2 (hb b)
  · intro x
    rw [map_mul, eval_C, sign_mul, sign_pos (inv_pos.2 hc), one_mul]

/-- A finite sign description can be put in the bounded-coefficient frozen format. -/
lemma format_of_signRep {n k D : ℕ} {R : ℝ} {S : Set (Fin n → ℝ)}
    (hR : 1 ≤ R) (hk : (k : ℝ) ≤ R)
    (h : k4_eligibility_sign_description.SignRep id k D (fun x => x ∈ S)) : Format n R D S := by
  classical
  obtain ⟨p, T, hp, hT⟩ := h
  choose q hqdeg hqcoeff hqsign using fun j => bounded_sign_polynomial (p j)
  refine ⟨k, hk, q, fun j => ⟨(hqdeg j).trans (hp j), fun b => (hqcoeff j b).trans hR⟩, T, ?_⟩
  ext x
  simp only [mem_ofPred_eq]
  have hs : (fun j => SignType.sign (eval x (q j))) = (fun j => SignType.sign (eval x (p j))) :=
    funext (fun j => hqsign j x)
  rw [hs]
  exact (hT x).symm

/-- Boolean polynomial tests may also be normalized to the frozen sign format. -/
lemma format_of_boolFormat {n D : ℕ} {R : ℝ} {S : Set (Fin n → ℝ)}
    (hR : 1 ≤ R) (h : k4_dyadic_crop_worlds.BoolFormat R D S) : Format n R D S := by
  classical
  obtain ⟨k, hk, p, hp, b, hb⟩ := h
  apply format_of_signRep hR hk
  refine ⟨p, {s | b (fun j => decide (0 ≤ s j)) = true}, hp, fun x => ?_⟩
  simpa only [Set.mem_ofPred_eq, sign_nonneg_iff, id_eq] using (hb x).symm

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
