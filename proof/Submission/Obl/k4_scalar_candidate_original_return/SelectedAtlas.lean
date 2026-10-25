import Submission.Obl.k4_scalar_candidate_original_return.Atlas
import Submission.Obl.k4_scalar_candidate_original_return.MeshPolicy

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set

noncomputable section

/-- Retain exactly those original geometric incidences named by the actual
terminal-observer rule. -/
def selectedByLists {p : Code} {k m : ℕ} (γ : Fin m → Fin (W p k))
    (C : Fin m → Set Inc) (L : Fin (W p k) → (Base × ℤ) → Finset (Fin m))
    (δ : ℝ) (i : Fin m) : Set Inc :=
  {q | q ∈ C i ∧ i ∈ L (γ i) (originalObservation δ q)}

/-- A geometric refinement may select fresh original incidences. It needs no
support assumption tying a dominated analytical law to the old selected sets. -/
theorem chart_of_selected_refinement {p : Code} (hp : Exact p)
    {k B₀ B m : ℕ} {r₀ r b h₀ h ε₀ ε : ℝ} {flag : Bool}
    (a : Layer (W p k))
    (ha : ChartData p B₀ r₀ b h₀ ε₀ flag k
      a.T a.n a.world a.time a.prior a.selected a.u a.v a.width a.poly a.lists)
    (hB : B₀ ≤ B) (hε : ε₀ ≤ ε)
    (idx : Fin m → Fin a.n) (A : Fin m → Set Line) (P : Fin m → Poly)
    (C : Fin m → Set Inc) (Λ : Fin (W p k) → (Base × ℤ) → Finset (Fin m))
    (hA : ∀ i, A i ⊆ a.prior (idx i))
    (hdisj : ∀ i j, i ≠ j → idx i = idx j → Disjoint (A i) (A j))
    (hAm : ∀ i, MeasurableSet (A i)) (hCm : ∀ i, MeasurableSet (C i))
    (hCsub : ∀ i, C i ⊆ E p k (a.world (idx i)) ∩
      (A i ×ˢ I a.T (a.time (idx i))))
    (hT : (2 : ℝ) ^ a.T ≤ N p k ^ h) (hcount : (m : ℝ) ≤ N p k ^ (B : ℝ))
    (hP : ∀ i, (P i).totalDegree ≤ 2 ∧ ∀ d, |(P i).coeff d| ≤ N p k ^ (B : ℝ))
    (hAf : ∀ i z, Format 5 (N p k ^ (B : ℝ)) B {v | (z, v) ∈ A i})
    (hCf : ∀ i z, Format 6 (N p k ^ (B : ℝ)) B
      {v | ((z, fun e : Fin 5 => v e.castSucc), v 5) ∈
        selectedByLists (fun i => a.world (idx i)) C Λ (N p k ^ (-b)) i})
    (hfit : ∀ i l, l ∈ A i → ∀ t ∈ I a.T (a.time (idx i)),
      |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N p k ^ ε * N p k ^ (-r))
    (hlist : ∀ g z, ((Λ g z).card : ℝ) ≤ N p k ^ ε)
    (hΛ : ∀ g i, MeasurableSet {z | i ∈ Λ g z})
    (hmass : ENNReal.ofReal (N p k ^ (-ε)) ≤
      ∑ g, ENNReal.ofReal (ω p k g) * mu p k g
        {q | ∃ i, a.world (idx i) = g ∧ q ∈
          selectedByLists (fun i => a.world (idx i)) C Λ (N p k ^ (-b)) i}) :
    Chart p B r b h ε false k := by
  have hN : 1 ≤ N p k := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1.1 k)
  have hεpow : N p k ^ ε₀ ≤ N p k ^ ε := Real.rpow_le_rpow_of_exponent_le hN hε
  have hBpow : N p k ^ (B₀ : ℝ) ≤ N p k ^ (B : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by exact_mod_cast hB)
  let out : Layer (W p k) := ⟨a.T, m, (fun i => a.world (idx i)),
    (fun i => a.time (idx i)), A,
    selectedByLists (fun i => a.world (idx i)) C Λ (N p k ^ (-b)),
    (fun i => a.u (idx i)), (fun i => a.v (idx i)), (fun i => a.width (idx i)), P, Λ⟩
  apply AtlasCertificate.chart (p := p) (k := k) (B := B) (r := r) (b := b) (h := h) (ε := ε)
  refine ⟨out, hT, hcount, ?_, ?_, ?_, ?_, hlist, hΛ, ?_, hmass⟩
  · intro i
    exact ⟨hAm i, (hCm i).inter ((hΛ _ i).preimage (measurable_originalObservation _))⟩
  · intro i j hij hγ hj
    by_cases heq : idx i = idx j
    · exact hdisj i j hij heq
    · exact (ha.2.2.2.1 (idx i) (idx j) heq hγ hj).mono (hA i) (hA j)
  · intro i q hq
    exact hCsub i hq.1
  · intro i
    rcases ha.2.2.2.2.2.1 (idx i) with
      ⟨hμ, hJ, hinv, hup, hctr, hdeg, hcoef, hbound, hpriorfmt, hselfmt, holdfit, hfloor⟩
    refine ⟨hJ, hinv.trans hBpow,
      hup.trans (div_le_div_of_nonneg_right hεpow (by positivity)),
      hctr.trans hεpow, (hP i).1, (hP i).2, ?_, hAf i, hCf i, ?_⟩
    · intro l hl
      exact ⟨(hbound l (hA i hl)).1.trans hBpow,
        fun e => ((hbound l (hA i hl)).2 e).trans hεpow⟩
    · intro l hl t ht
      exact ⟨(holdfit l (hA i hl) t ht).1.trans
        (mul_le_mul_of_nonneg_right hεpow hJ.le), hfit i l hl t ht⟩
  · intro i
    apply measure_mono_null (t := ∅)
    · rintro q ⟨hq, hbad⟩
      exact hbad hq.2
    · exact measure_empty

end

end Submission.Obl.k4_scalar_candidate_original_return
