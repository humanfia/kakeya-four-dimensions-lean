import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.ScalarAt
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Rescale

/-!
# Scalar mesh projection on one block

The frozen Scalar hypothesis applied to an incidence law carried by one block
`A × [t₀, t₀ + q]`, after rescaling time to `[0, 1]` and normalizing by `q ν(A)`. All
hypotheses and conclusions are stated in the original time variable.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Rescaled time of a point. -/
def tau (t₀ q : ℝ) (p : ℝ) : ℝ := (p - t₀) / q

/-- Mesh cell of a point on the block, in rescaled time and scalar coordinate. -/
def blockCell {α : Type*} (t₀ q σ : ℝ) (y0 y1 : α → ℝ) (p : α × ℝ) : Fin 2 → ℤ :=
  ![⌊tau t₀ q p.2 / σ⌋, ⌊(y0 p.1 + tau t₀ q p.2 * y1 p.1) / σ⌋]

/-- Scalar value of a point on the block. -/
def blockVal {α : Type*} (t₀ q : ℝ) (x0 x1 : α → ℝ) (p : α × ℝ) : ℝ :=
  x0 p.1 + tau t₀ q p.2 * x1 p.1

/-- Piecewise normalized coefficients. -/
def blockCoeff {α : Type*} (Good : Set α) (y0 y1 x0 x1 : α → ℝ) (l : α) : Fin 5 → ℝ :=
  by classical exact if l ∈ Good then ![y0 l, y1 l, x0 l, x1 l, 0] else 0

theorem measurable_blockCoeff {α : Type*} [MeasurableSpace α] {Good : Set α}
    (hG : MeasurableSet Good) {y0 y1 x0 x1 : α → ℝ} (hy0 : Measurable y0) (hy1 : Measurable y1)
    (hx0 : Measurable x0) (hx1 : Measurable x1) :
    Measurable (blockCoeff Good y0 y1 x0 x1) := by
  classical
  unfold blockCoeff
  refine Measurable.ite hG ?_ measurable_const
  refine measurable_pi_iff.mpr (fun i => ?_)
  fin_cases i <;> simp <;> assumption

theorem blockCoeff_of_mem {α : Type*} {Good : Set α} {y0 y1 x0 x1 : α → ℝ} {l : α}
    (hl : l ∈ Good) : blockCoeff Good y0 y1 x0 x1 l = ![y0 l, y1 l, x0 l, x1 l, 0] := by
  classical
  unfold blockCoeff; rw [ite_eq_left_iff.mpr (fun h => absurd hl h)]

theorem blockCoeff_of_not_mem {α : Type*} {Good : Set α} {y0 y1 x0 x1 : α → ℝ} {l : α}
    (hl : l ∉ Good) : blockCoeff Good y0 y1 x0 x1 l = 0 := by
  classical
  unfold blockCoeff; exact if_neg hl

/-- Scalar on one block, in the original time variable. -/
theorem scalar_on_block {d s m C S U ε η N₀ : ℝ} (hSA : ScalarAt d s m C S U ε η N₀)
    {N : ℝ} (hN : N₀ ≤ N) (hN1 : 1 ≤ N)
    {α : Type} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (mm : Measure (α × ℝ)) (A Good : Set α) (hA : MeasurableSet A) (hG : MeasurableSet Good)
    (t₀ q K c : ℝ) (hq : 0 < q) (hK0 : 0 ≤ K) (hKη : K ≤ N ^ η)
    (y0 y1 x0 x1 : α → ℝ) (hy0 : Measurable y0) (hy1 : Measurable y1) (hx0 : Measurable x0)
    (hx1 : Measurable x1) (hνA : ν A ≠ 0)
    (hm : mm ≤ ENNReal.ofReal K • ν.prod volume)
    (hsupp : mm (A ×ˢ Icc t₀ (t₀ + q))ᶜ = 0)
    (hgood : ∀ᵐ p ∂mm, p.1 ∈ Good)
    (hbd : ∀ l ∈ Good, |y0 l| ≤ N ^ η ∧ |y1 l| ≤ N ^ η ∧ |x0 l| ≤ N ^ η ∧ |x1 l| ≤ N ^ η)
    (hc1 : N ^ (-C) ≤ c) (hc2 : c ≤ N ^ C)
    (hmass : ENNReal.ofReal (N ^ (-η)) * (ENNReal.ofReal q * ν A) ≤ mm univ)
    (hcaps : ∀ (r : ℝ) (cell : Fin 2 → ℤ) (jj : ℤ), 0 ≤ r → r ≤ s →
      mm {p | blockCell t₀ q (N ^ (-m)) y0 y1 p = cell ∧
          ⌊blockVal t₀ q x0 x1 p / N ^ (-r)⌋ = jj} ≤
        ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * c * (N ^ (-r)) ^ d) * (ENNReal.ofReal q * ν A))
    (hsupport : ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      (F.card : ℝ) * (N ^ (-m)) ^ 2 ≤ N ^ η * c⁻¹ * (N ^ (-s)) ^ (-d) ∧
      ∀ᵐ p ∂mm, (blockCell t₀ q (N ^ (-m)) y0 y1 p, ⌊blockVal t₀ q x0 x1 p / N ^ (-s)⌋) ∈ F)
    (hang : ∀ (r : ℝ) (cell : Fin 2 → ℤ) (jj kk : ℤ), 0 < r → r ≤ U →
      mm {p | blockCell t₀ q (N ^ (-m)) y0 y1 p = cell ∧
          ⌊blockVal t₀ q x0 x1 p / N ^ (-s)⌋ = jj ∧ ⌊y1 p.1 / N ^ (-r)⌋ = kk} ≤
        ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * c * (N ^ (-s)) ^ d * N ^ (-S * r)) *
          (ENNReal.ofReal q * ν A)) :
    ∃ (n : ℕ) (β : ℝ) (A' : Fin n → Set α) (u v : Fin n → ℝ)
      (P : Fin n → MvPolynomial (Fin 2) ℝ),
      N ^ (-ε) ≤ β ∧ β ≤ N ^ ε ∧ (∀ i, MeasurableSet (A' i)) ∧
      (∀ i j, i ≠ j → Disjoint (A' i) (A' j)) ∧
      (∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧
        (∀ τ ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
          |MvPolynomial.eval ![τ, u i + τ * v i + β * w] (P i)| ≤ N ^ ε) ∧
        (∀ l ∈ A' i, l ∈ Good → ∀ τ ∈ Icc (0 : ℝ) 1,
          |y0 l + τ * y1 l - u i - τ * v i| ≤ N ^ ε * β ∧
          |x0 l + τ * x1 l - MvPolynomial.eval ![τ, y0 l + τ * y1 l] (P i)| ≤
            N ^ ε * N ^ (-s)) ∧
        ENNReal.ofReal (c * (N ^ (-s)) ^ d * β / N ^ ε) * (ENNReal.ofReal q * ν A) ≤
          mm (A' i ×ˢ univ)) ∧
      ENNReal.ofReal (N ^ (-ε)) * (ENNReal.ofReal q * ν A) ≤ mm {p | ∃ i, p.1 ∈ A' i} := by
  classical
  set b' := blockCoeff Good y0 y1 x0 x1 with hb'
  set Z : ℝ≥0∞ := ENNReal.ofReal q * ν A with hZ
  have hZ0 : Z ≠ 0 := mul_ne_zero (by simpa using hq) hνA
  have hZtop : Z ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν A)
  set μ'' : Measure (α × ℝ) := Z⁻¹ • mm.map (rescale t₀ q) with hμ''
  set ν' : Measure α := ProbabilityTheory.cond ν A with hν'
  have hν'p : IsProbabilityMeasure ν' := ProbabilityTheory.cond_isProbabilityMeasure hνA
  -- transfer of upper bounds through the rescaling
  have hnull : mm {p | p.1 ∉ Good} = 0 := by
    rw [ae_iff] at hgood; simpa using hgood
  have hrel : ∀ (E E' : Set (α × ℝ)), (∀ p, p.1 ∈ Good → rescale t₀ q p ∈ E → p ∈ E') →
      μ'' E ≤ Z⁻¹ * mm E' := by
    intro E E' hEE'
    rw [hμ'', Measure.smul_apply, smul_eq_mul, map_rescale_apply mm t₀ q hq.ne']
    refine mul_le_mul_right ?_ _
    calc mm (rescale t₀ q ⁻¹' E) ≤ mm (E' ∪ {p | p.1 ∉ Good}) := by
          apply measure_mono
          intro p hp
          by_cases hpg : p.1 ∈ Good
          · exact Or.inl (hEE' p hpg hp)
          · exact Or.inr hpg
      _ ≤ mm E' + mm {p | p.1 ∉ Good} := measure_union_le _ _
      _ = mm E' := by rw [hnull, add_zero]
  have hcell : ∀ p : α × ℝ, p.1 ∈ Good →
      (![⌊(rescale t₀ q p).2 / N ^ (-m)⌋,
        ⌊(b' (rescale t₀ q p).1 0 + (rescale t₀ q p).2 * b' (rescale t₀ q p).1 1) /
          N ^ (-m)⌋] : Fin 2 → ℤ) = blockCell t₀ q (N ^ (-m)) y0 y1 p := by
    intro p hp
    simp only [rescale, hb', blockCoeff_of_mem hp, blockCell, tau]
    rfl
  have hval : ∀ p : α × ℝ, p.1 ∈ Good →
      b' (rescale t₀ q p).1 2 + (rescale t₀ q p).2 * b' (rescale t₀ q p).1 3 +
        (rescale t₀ q p).2 ^ 2 * b' (rescale t₀ q p).1 4 = blockVal t₀ q x0 x1 p := by
    intro p hp
    simp only [rescale, hb', blockCoeff_of_mem hp, blockVal, tau]
    simp
  have hslope : ∀ p : α × ℝ, p.1 ∈ Good → b' (rescale t₀ q p).1 1 = y1 p.1 := by
    intro p hp
    simp only [rescale, hb', blockCoeff_of_mem hp]
    rfl
  have hS := hSA N hN α ν' μ'' b' c true
  beta_reduce at hS
  have hNη : 0 < N ^ η := Real.rpow_pos_of_pos (by linarith) η
  -- (μ'' E) * Z = mm (rescale⁻¹ E)
  have hμZ : ∀ E : Set (α × ℝ), μ'' E * Z = mm (rescale t₀ q ⁻¹' E) := by
    intro E
    rw [hμ'', Measure.smul_apply, smul_eq_mul, map_rescale_apply mm t₀ q hq.ne', mul_comm,
      ← mul_assoc, ENNReal.mul_inv_cancel hZ0 hZtop, one_mul]
  have hup : ∀ (E E' : Set (α × ℝ)) (B : ℝ≥0∞),
      (∀ p, p.1 ∈ Good → rescale t₀ q p ∈ E → p ∈ E') → mm E' ≤ B * Z → μ'' E ≤ B := by
    intro E E' B hEE' hB
    calc μ'' E ≤ Z⁻¹ * mm E' := hrel E E' hEE'
      _ ≤ Z⁻¹ * (B * Z) := mul_le_mul_right hB _
      _ = B := by rw [mul_comm B Z, ← mul_assoc, ENNReal.inv_mul_cancel hZ0 hZtop, one_mul]
  -- domination
  have hdom : μ'' ≤ ENNReal.ofReal (N ^ η) • ν'.prod volume := by
    have hmap := map_rescale_le ν mm A hA t₀ q K hq hK0 hm hsupp
    have hrestr : ν.restrict A = ν A • ν' := by
      rw [hν', ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel hνA (measure_ne_top ν A),
        one_smul]
    rw [Measure.le_iff]
    intro E hE
    rw [hμ'', Measure.smul_apply, smul_eq_mul]
    calc Z⁻¹ * (mm.map (rescale t₀ q)) E
        ≤ Z⁻¹ * ((ENNReal.ofReal (K * q) • (ν.restrict A).prod volume) E) :=
          mul_le_mul_right (hmap E) _
      _ = Z⁻¹ * (ENNReal.ofReal (K * q) * (ν A * (ν'.prod volume) E)) := by
          rw [Measure.smul_apply, smul_eq_mul, hrestr, Measure.prod_smul_left, Measure.smul_apply,
            smul_eq_mul]
      _ = ENNReal.ofReal K * (ν'.prod volume) E := by
          rw [ENNReal.ofReal_mul hK0, hZ]
          have hq0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
          rw [ENNReal.mul_inv (Or.inl hq0) (Or.inl ENNReal.ofReal_ne_top)]
          calc (ENNReal.ofReal q)⁻¹ * (ν A)⁻¹ *
                (ENNReal.ofReal K * ENNReal.ofReal q * (ν A * (ν'.prod volume) E))
              = ENNReal.ofReal K * ((ENNReal.ofReal q)⁻¹ * ENNReal.ofReal q) *
                  ((ν A)⁻¹ * ν A) * (ν'.prod volume) E := by ring
            _ = _ := by
                rw [ENNReal.inv_mul_cancel hq0 ENNReal.ofReal_ne_top,
                  ENNReal.inv_mul_cancel hνA (measure_ne_top ν A), mul_one, mul_one]
      _ ≤ ENNReal.ofReal (N ^ η) * (ν'.prod volume) E :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hKη) _
      _ = (ENNReal.ofReal (N ^ η) • ν'.prod volume) E := by rw [Measure.smul_apply, smul_eq_mul]
  -- support
  have hsupp'' : μ'' (univ ×ˢ Icc 0 1)ᶜ = 0 := by
    have h0 : mm (rescale t₀ q ⁻¹' (univ ×ˢ Icc (0 : ℝ) 1)ᶜ) = 0 := by
      refine measure_mono_null ?_ hsupp
      intro p hp hpA
      apply hp
      simp only [rescale, mem_prod, mem_univ, true_and, mem_Icc]
      obtain ⟨_, h1, h2⟩ := hpA
      constructor
      · exact div_nonneg (by linarith) hq.le
      · rw [div_le_one hq]; linarith
    have := hμZ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ
    rw [h0] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hZ0
  -- mass
  have hmass'' : ENNReal.ofReal (N ^ (-η)) ≤ μ'' univ := by
    have h1 := hμZ univ
    rw [preimage_univ] at h1
    have h2 : ENNReal.ofReal (N ^ (-η)) * Z ≤ μ'' univ * Z := by rw [h1]; exact hmass
    exact (ENNReal.mul_le_mul_iff_left hZ0 hZtop).mp h2
  -- coefficient bounds
  have hbd'' : ∀ (l : α) (i : Fin 5), |b' l i| ≤ N ^ η := by
    intro l i
    by_cases hl : l ∈ Good
    · rw [hb', blockCoeff_of_mem hl]
      obtain ⟨h0, h1, h2, h3⟩ := hbd l hl
      fin_cases i <;> simp [h0, h1, h2, h3, hNη.le]
    · rw [hb', blockCoeff_of_not_mem hl]; simp [hNη.le]
  -- caps
  have hcaps'' : ∀ (r : ℝ) (q' : Fin 2 → ℤ) (jj : ℤ), 0 ≤ r → r ≤ s →
      μ'' {p | ![⌊p.2 / N ^ (-m)⌋, ⌊(b' p.1 0 + p.2 * b' p.1 1) / N ^ (-m)⌋] = q' ∧
          ⌊(b' p.1 2 + p.2 * b' p.1 3 + p.2 ^ 2 * b' p.1 4) / N ^ (-r)⌋ = jj} ≤
        ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * c * (N ^ (-r)) ^ d) := by
    intro r q' jj hr0 hrs
    refine hup _ _ _ ?_ (hcaps r q' jj hr0 hrs)
    intro p hp hE
    obtain ⟨h1, h2⟩ := hE
    exact ⟨(hcell p hp).symm.trans h1, by rw [← hval p hp]; exact h2⟩
  -- support count
  have hsupport'' : ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      (F.card : ℝ) * (N ^ (-m)) ^ 2 ≤ N ^ η * c⁻¹ * (N ^ (-s)) ^ (-d) ∧
      ∀ᵐ p ∂μ'', (![⌊p.2 / N ^ (-m)⌋, ⌊(b' p.1 0 + p.2 * b' p.1 1) / N ^ (-m)⌋],
        ⌊(b' p.1 2 + p.2 * b' p.1 3 + p.2 ^ 2 * b' p.1 4) / N ^ (-s)⌋) ∈ F := by
    obtain ⟨F, hFc, hFae⟩ := hsupport
    refine ⟨F, hFc, ?_⟩
    rw [ae_iff]
    apply le_antisymm _ zero_le
    refine hup {p | ¬ ((![⌊p.2 / N ^ (-m)⌋, ⌊(b' p.1 0 + p.2 * b' p.1 1) / N ^ (-m)⌋],
        ⌊(b' p.1 2 + p.2 * b' p.1 3 + p.2 ^ 2 * b' p.1 4) / N ^ (-s)⌋) ∈ F)}
      {p | ¬ ((blockCell t₀ q (N ^ (-m)) y0 y1 p, ⌊blockVal t₀ q x0 x1 p / N ^ (-s)⌋) ∈ F)}
      0 ?_ ?_
    · intro p hp hE
      have h1 := hcell p hp
      have h2 := hval p hp
      simp only [mem_ofPred_eq, mem_preimage] at hE ⊢
      rw [h1, h2] at hE
      exact hE
    · rw [zero_mul]; rw [ae_iff] at hFae; exact hFae.le
  -- angular caps
  have hang'' : true = true → ∀ (r : ℝ) (q' : Fin 2 → ℤ) (jj kk : ℤ), 0 < r → r ≤ U →
      μ'' {p | ![⌊p.2 / N ^ (-m)⌋, ⌊(b' p.1 0 + p.2 * b' p.1 1) / N ^ (-m)⌋] = q' ∧
          ⌊(b' p.1 2 + p.2 * b' p.1 3 + p.2 ^ 2 * b' p.1 4) / N ^ (-s)⌋ = jj ∧
          ⌊b' p.1 1 / N ^ (-r)⌋ = kk} ≤
        ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * c * (N ^ (-s)) ^ d * N ^ (-S * r)) := by
    intro _ r q' jj kk hr hrU
    refine hup _ _ _ ?_ (hang r q' jj kk hr hrU)
    intro p hp hE
    obtain ⟨h1, h2, h3⟩ := hE
    exact ⟨(hcell p hp).symm.trans h1, by rw [← hval p hp]; exact h2,
      by rw [← hslope p hp]; exact h3⟩
  obtain ⟨n, β, A', u, v, P, _, hβ2, hβ3, hA'm, hA'd, hA'p, htot⟩ :=
    hS (measurable_blockCoeff hG hy0 hy1 hx0 hx1) hν'p hdom hsupp'' hmass'' hbd'' hc1 hc2
      hcaps'' hsupport'' hang''
  refine ⟨n, β, A', u, v, P, hβ3 rfl, hβ2, hA'm, hA'd, fun i => ?_, ?_⟩
  · obtain ⟨huv, hdeg, hmov, hfit, hmi⟩ := hA'p i
    refine ⟨huv, hdeg, hmov, ?_, ?_⟩
    · intro l hl hlG τ hτ
      have := hfit l hl τ hτ
      rw [hb', blockCoeff_of_mem hlG] at this
      simpa using this
    · have h1 := hμZ (A' i ×ˢ Icc (0 : ℝ) 1)
      calc ENNReal.ofReal (c * (N ^ (-s)) ^ d * β / N ^ ε) * Z
          ≤ μ'' (A' i ×ˢ Icc (0 : ℝ) 1) * Z := mul_le_mul_left hmi _
        _ = mm (rescale t₀ q ⁻¹' (A' i ×ˢ Icc (0 : ℝ) 1)) := h1
        _ ≤ mm (A' i ×ˢ univ) := by
            apply measure_mono
            intro p hp
            exact ⟨hp.1, mem_univ _⟩
  · have h1 := hμZ {p | ∃ i, p.1 ∈ A' i}
    calc ENNReal.ofReal (N ^ (-ε)) * Z ≤ μ'' {p | ∃ i, p.1 ∈ A' i} * Z := mul_le_mul_left htot _
      _ = mm (rescale t₀ q ⁻¹' {p | ∃ i, p.1 ∈ A' i}) := h1
      _ = mm {p | ∃ i, p.1 ∈ A' i} := rfl

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
