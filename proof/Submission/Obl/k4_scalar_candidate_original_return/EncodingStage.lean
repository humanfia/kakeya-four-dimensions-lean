import Submission.Obl.k4_scalar_candidate_original_return.MassRecovery
import Submission.Obl.k4_scalar_candidate_original_return.SelectedFormat

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set
open scoped ENNReal

/-- The complete finite original-law encoding step at one sample. Its output
complexity is linear in the input geometric budget; its slack pays only V. -/
theorem encode_selected_family {p : Code} (hp : Exact p)
    {k B₀ B m : ℕ} {r₀ r b h₀ h ε₀ ε : ℝ} {flag : Bool}
    (a : Layer (W p k))
    (ha : ChartData p B₀ r₀ b h₀ ε₀ flag k
      a.T a.n a.world a.time a.prior a.selected a.u a.v a.width a.poly a.lists)
    (hB : B₀ ≤ B) (hM : M p ≤ B) (hD : D p ≤ B) (hε : ε₀ ≤ ε)
    (idx : Fin m → Fin a.n) (A : Fin m → Set Line) (P : Fin m → Poly)
    (C : Fin m → Set Inc)
    (hA : ∀ i, A i ⊆ a.prior (idx i))
    (hdisj : ∀ i j, i ≠ j → idx i = idx j → Disjoint (A i) (A j))
    (hAm : ∀ i, MeasurableSet (A i)) (hCm : ∀ i, MeasurableSet (C i))
    (hCsub : ∀ i, C i ⊆ E p k (a.world (idx i)) ∩
      (A i ×ˢ I a.T (a.time (idx i))))
    (hT : (2 : ℝ) ^ a.T ≤ N p k ^ h) (hcount : (m : ℝ) ≤ N p k ^ B)
    (hP : ∀ i, (P i).totalDegree ≤ 2 ∧ ∀ d, |(P i).coeff d| ≤ N p k ^ B)
    (hAf : ∀ i z, Format 5 (N p k ^ B) B {v | (z, v) ∈ A i})
    (hCf : ∀ i z, Format 6 (N p k ^ B) B
      {v | ((z, fun e : Fin 5 => v e.castSucc), v 5) ∈ C i})
    (hfit : ∀ i l, l ∈ A i → ∀ t ∈ I a.T (a.time (idx i)),
      |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N p k ^ (-r))
    (hterminal : (N p k ^ (-b))⁻¹ ≤ N p k ^ B)
    (L : Fin (W p k) → (Base × ℤ) → Finset (Fin m))
    (hL : ∀ g i, MeasurableSet {z | i ∈ L g z})
    (V : ℝ) (hV : 1 ≤ V) (hLcard : ∀ g z, ((L g z).card : ℝ) ≤ V)
    (hlower : ENNReal.ofReal V⁻¹ ≤ ∑ i, ENNReal.ofReal (ω p k (a.world (idx i))) *
      mu p k (a.world (idx i)) {q | q ∈ C i ∧ i ∈ L (a.world (idx i))
        (originalObservation (N p k ^ (-b)) q)})
    (herror : (N p k)⁻¹ ≤ (2 * V)⁻¹)
    (hεlist : 2 * V ≤ N p k ^ ε) (hεmass : N p k ^ (-ε) ≤ (4 * V ^ 2)⁻¹) :
    Chart p (36 * B + 104) r b h ε false k := by
  have hN : 1 ≤ N p k := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1.1 k)
  obtain ⟨Λ, hΛcard, hΛmeas, hΛformat, hΛmass⟩ := recover_original_union_mass hp k B hM hD
    hcount (fun i => a.world (idx i)) C hCm (fun i q hq => (hCsub i hq).1)
    hCf (N p k ^ (-b)) (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _)
    hterminal L hL V hV hLcard hlower herror
  have hpow : N p k ^ B ≤ N p k ^ (36 * B + 104) :=
    pow_le_pow_right₀ hN (by omega)
  have hformatbudget : N p k ^ B + N p k ^ (36 * B + 102) ≤
      N p k ^ (36 * B + 104) := by
    have h₁ : N p k ^ B ≤ N p k ^ (36 * B + 102) := pow_le_pow_right₀ hN (by omega)
    calc
      _ ≤ 2 * N p k ^ (36 * B + 102) := by linarith
      _ ≤ N p k ^ 2 * N p k ^ (36 * B + 102) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [hp.1.1 k]
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hselected := selectedByLists_format (fun i => a.world (idx i)) C Λ (N p k ^ (-b))
    (one_le_pow₀ hN) (one_le_pow₀ hN) hCf hΛformat
  apply chart_of_selected_refinement hp a ha (by omega) hε idx A P C Λ
    hA hdisj hAm hCm hCsub hT
  · simpa only [Real.rpow_natCast] using hcount.trans hpow
  · intro i
    exact ⟨(hP i).1, fun d => by simpa only [Real.rpow_natCast] using ((hP i).2 d).trans hpow⟩
  · intro i z
    exact k4_scalar_true_atlas_terminal_lists.Format.mono (hAf i z)
      (by simpa only [Real.rpow_natCast] using hpow) (by omega)
  · intro i z
    exact k4_scalar_true_atlas_terminal_lists.Format.mono (hselected i z)
      (by simpa only [Real.rpow_natCast] using hformatbudget) (by omega)
  · intro i l hl t ht
    apply (hfit i l hl t ht).trans
    have hεone : 1 ≤ N p k ^ ε := (by linarith : (1 : ℝ) ≤ 2 * V).trans hεlist
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hεone
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) (-r)).le
  · exact fun g z => (hΛcard g z).trans hεlist
  · exact hΛmeas
  · exact (ENNReal.ofReal_le_ofReal hεmass).trans hΛmass

end Submission.Obl.k4_scalar_candidate_original_return
