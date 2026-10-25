import Submission.Obl.k4_dyadic_crop_worlds.NativeBounds
import Submission.Obl.k4_dyadic_crop_worlds.Partition
import Submission.Obl.k4_dyadic_crop_worlds.Selection

/-!
# Assembly helpers for `k4_dyadic_crop_worlds`

Monotonicity of the formats in their size bound, the polynomial budget of a crop, sums over an
enumeration of a finset, and the per-crop conjuncts of the frozen weighted-world format with the
native test `X 3` and `B = 1`.
-/

open MeasureTheory Set Filter

namespace Submission.Obl.k4_dyadic_crop_worlds

noncomputable section

lemma PriorFormat.mono {R R' : ℝ} {D : ℕ} {ν : Measure Line} (h : PriorFormat R D ν)
    (hR : R ≤ R') : PriorFormat R' D ν := by
  obtain ⟨m, hm, c, i, A, hA, hν⟩ := h
  refine ⟨m, hm.trans hR, c, i, A, fun j => ?_, hν⟩
  obtain ⟨h0, hc, hi, hB, hx⟩ := hA j
  exact ⟨h0, hc.trans hR, hi.trans hR, hB.mono hR le_rfl, fun x hxA b => (hx x hxA b).trans hR⟩

lemma EventFormat.mono {R R' : ℝ} {D : ℕ} {E : Set Incident} (h : EventFormat R D E)
    (hR : R ≤ R') : EventFormat R' D E := by
  obtain ⟨hm, hsub, hb, hs⟩ := h
  exact ⟨hm, hsub, fun p hp => ⟨(hb p hp).1.trans hR, fun e => ((hb p hp).2 e).trans hR⟩,
    fun i => (hs i).mono hR le_rfl⟩

/-- A sum over an enumeration of a finset. -/
lemma sum_equivFin {ι M : Type*} [AddCommMonoid M] (Q : Finset ι) (f : ι → M) :
    ∑ γ : Fin Q.card, f (Q.equivFin.symm γ).1 = ∑ q ∈ Q, f q := by
  rw [← Finset.sum_coe_sort Q f]
  exact Equiv.sum_comp Q.equivFin.symm (fun x => f x.1)

lemma injective_equivFin {ι : Type*} (Q : Finset ι) :
    Function.Injective (fun γ : Fin Q.card => (Q.equivFin.symm γ).1) :=
  Subtype.val_injective.comp Q.equivFin.symm.injective

lemma event_budget {N : ℝ} (hN : 2 ≤ N) (M A : ℕ) : N ^ M + 8 ≤ N ^ (M + A + 5) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hM : (1 : ℝ) ≤ N ^ M := one_le_pow₀ hN1
  have h4 : (16 : ℝ) ≤ N ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ N ^ 4 := pow_le_pow_left₀ (by norm_num) hN 4
  have hA : (1 : ℝ) ≤ N ^ (A + 1) := one_le_pow₀ hN1
  calc N ^ M + 8 ≤ N ^ M * N ^ 4 := by nlinarith
    _ ≤ N ^ M * N ^ 4 * N ^ (A + 1) := le_mul_of_one_le_right (by positivity) hA
    _ = N ^ (M + A + 5) := by rw [← pow_add, ← pow_add]; ring_nf

lemma prior_budget {N : ℝ} (hN : 2 ≤ N) (M A : ℕ) :
    (N ^ M + 8) / N ^ (-((A : ℝ) + 1)) ≤ N ^ (M + A + 5) := by
  have hN0 : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hM : (1 : ℝ) ≤ N ^ M := one_le_pow₀ hN1
  have h4 : (16 : ℝ) ≤ N ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ N ^ 4 := pow_le_pow_left₀ (by norm_num) hN 4
  have hpow : N ^ (-((A : ℝ) + 1)) = (N ^ (A + 1))⁻¹ := by
    rw [Real.rpow_neg hN0.le]
    congr 1
    rw [← Real.rpow_natCast]
    push_cast
    ring_nf
  rw [hpow, div_inv_eq_mul]
  calc (N ^ M + 8) * N ^ (A + 1) ≤ (N ^ M * N ^ 4) * N ^ (A + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
    _ = N ^ (M + A + 5) := by rw [← pow_add, ← pow_add]; ring_nf

/-- The per-crop conjuncts of the frozen weighted-world format, for the native test `X 3`
and `B = 1`. -/
lemma crop_gamma_facts {R K : ℝ} {D : ℕ} (ν : Measure Line) (E : Set Incident)
    (hprob : IsProbabilityMeasure ν) (hR : 1 ≤ R) (hν : PriorFormat R D ν)
    (hE : EventFormat R D E) (hK : ∀ᵐ l ∂ν, NativeBound K l) (hK1 : 1 ≤ K) :
    MeasureTheory.IsProbabilityMeasure ν ∧ 0 < (1 : ℝ) ∧ (1 : ℝ) ≤ R ∧ (1 : ℝ)⁻¹ ≤ R ∧ (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 2 ∧ (∀ b, |(MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ).coeff b| ≤ R) ∧ (∃ m : ℕ, (m : ℝ) ≤ R ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ R ∧ (i j : ℝ) ≤ R ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ R ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ R)) ∧ ν = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet E ∧ E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E, (p.1.1 : ℝ) ≤ R ∧ ∀ e, |p.1.2 e| ≤ R) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ R ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ E}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂ν, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ)| ≤ K ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ))| ≤ K * (1 : ℝ) ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ)))| ≤ K * (1 : ℝ) ^ 2) ∧ (∀ᵐ p ∂((ν.prod MeasureTheory.volume).restrict E), (1 : ℝ) / K ≤ |MvPolynomial.eval (![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ))|)
  := by
  obtain ⟨hEm, hEsub, hEb, hEs⟩ := hE
  have hX : ∀ x : Fin 4 → ℝ,
      MvPolynomial.eval x (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ) = x 3 :=
    fun x => MvPolynomial.eval_X (f := x) 3
  have hd1 : MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.X (3 : Fin 4) :
      MvPolynomial (Fin 4) ℝ) = 1 := MvPolynomial.pderiv_X_self 3
  refine ⟨hprob, one_pos, hR, by simpa using hR, ?_, ?_, hν, hEm, hEsub, hEb, hEs, ?_, ?_⟩
  · rw [MvPolynomial.totalDegree_X]; norm_num
  · intro b
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp <;> linarith
  · filter_upwards [hK] with l hl t ht
    obtain ⟨h1, h2⟩ := hl t ht
    refine ⟨h1, ?_, ?_, ?_⟩
    · rw [hX]; exact h2
    · rw [hd1, map_one]; simpa using hK1
    · rw [hd1, Derivation.map_one_eq_zero, map_zero]; simp; linarith
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [hd1, map_one, abs_one]
    exact div_le_one_of_le₀ hK1 (by linarith)

end

end Submission.Obl.k4_dyadic_crop_worlds
