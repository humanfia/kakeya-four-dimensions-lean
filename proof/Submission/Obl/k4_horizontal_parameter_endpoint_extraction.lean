import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.k4_horizontal_parameter_endpoint_extraction`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_horizontal_parameter_endpoint_extraction`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_horizontal_parameter_endpoint_extraction/`
belong to this obligation.
-/

theorem Submission.k4_horizontal_parameter_endpoint_extraction : (fun Engine : Bool → (ℝ → ℝ → Prop) → Prop => Engine false (fun (κ u : ℝ) => 2 * κ < u ∧ u ≤ 1) → Engine false (fun (κ u : ℝ) => u = 2 * κ)) (fun (fixedBuffer : Bool) (rates : ℝ → ℝ → Prop) => ((fun (horizontal : Bool) (regime : ℝ → Prop) => ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ d κ ℓ S U e₀ : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < ℓ → 0 < S → S ≤ 1 → 0 < U → 0 < e₀ → regime κ → (horizontal = true → ℓ = κ) → ∀ (α : Type) [MeasurableSpace α] (ν : ℕ → MeasureTheory.Measure α) (μ ρ : ℕ → MeasureTheory.Measure (α × ℝ)) (π : ℕ → MeasureTheory.Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) (P : ℕ → MvPolynomial (Fin 4) ℝ) (T n : ℕ → ℝ → ℕ) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α) (c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ) (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ), (fun (x : ℕ → α → ℝ → Fin 4 → ℝ) (I : (T : ℕ) → Fin (2 ^ T) → Set ℝ) => (fun z : ℕ → ℝ → ℝ → (α × ℝ) → Fin 3 → ℤ => (fun fit : ℕ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → α → Set ℝ → Prop => (∀ k, Measurable (b k) ∧ MeasureTheory.IsProbabilityMeasure (ν k) ∧ MeasureTheory.IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod MeasureTheory.volume) ∧ ρ k ≤ μ k ∧ μ k (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ρ k Set.univ ∧ (P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂ν k, |b k l 0| + |b k l 1| + |b k l 3| + |b k l 4| ≤ K k) ∧ (∀ᵐ p ∂μ k, (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (x k p.1 t) (P k)| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (P k))| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k)))| ≤ K k) ∧ (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k))|)) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a : ℤ, π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-S * v))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s)) * π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ U → (fun (q : ℝ) (a g : ℝ → ℝ) => N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧ (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i, MeasurableSet (A k s i) ∧ MeasurableSet (B k s i) ∧ B k s i ⊆ A k s i) ∧ (∀ i i', i ≠ i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i, ENNReal.ofReal (a s ^ d * q ^ 2 * g s / K k) ≤ ν k (A k s i) ∧ ν k (A k s i) ≤ ENNReal.ofReal (K k * a s ^ d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / K k) * ν k (A k s i) ≤ μ k (B k s i ×ˢ I (T k s) (j k s i)) ∧ (∀ e, |c k s i e| ≤ K k) ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i), |(x k l t) 1 - c k s i 0 - t * c k s i 1| ≤ K k * q ∧ |(x k l t) 2 - c k s i 2 - t * c k s i 3 - c k s i 4 * (x k l t) 1| ≤ K k * q * g s ∧ |b k l 4 - c k s i 3 - c k s i 4 * b k l 3| ≤ K k * g s) ∧ (∀ l ∈ B k s i, fit k (K k) (a s) (F k s i) l (I (T k s) (j k s i))) ∧ (∀ᵐ p ∂μ k, p.1 ∈ B k s i → p.2 ∈ I (T k s) (j k s i) → (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (F k s i))|) ∧ (horizontal = true → P k = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂μ k, |b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀)) ∧ |c k s i 3 + c k s i 0 + ((j k s i : ℕ) + (1 : ℝ) / 2) * q * c k s i 1| + |c k s i 4 - ((j k s i : ℕ) + (1 : ℝ) / 2) * q| ≤ K k * q ∧ (∃ L : Fin 4 → ℝ, F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ B k s i, ∀ t ∈ I (T k s) (j k s i), |L 1 - (x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂μ k, ∃ i, p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i)) ∧ (∀ (i : Fin (n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → μ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * q) * ν k (A k s i) * π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(T k s : ℤ))) (fun s => N k ^ (-s)) (fun s => N k ^ (-ℓ * s))) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ U → ∀ i : Fin (n k t), ∃ h : Fin (n k s), A k t i ⊆ A k s h ∧ I (T k t) (j k t i) ⊆ I (T k s) (j k s h)) → (∃ sMax R : ℝ, 0 < sMax ∧ 2 * sMax < U ∧ 100 * sMax < e₀ ∧ 1 < R ∧ (fixedBuffer = true → sMax = min (U / 4) (e₀ / 200)) ∧ ∀ u : ℝ, rates κ u → ∀ (m : ℕ) (sH : Fin m → ℝ), (∀ r, 0 < sH r ∧ sH r < sMax) → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, ∃ ρH : MeasureTheory.Measure (α × ℝ), ρH ≤ ρ k ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ ρH Set.univ ∧ ∃ (nH : Fin m → ℕ) (AH : (r : Fin m) → Fin (nH r) → Set α) (qH : (r : Fin m) → Fin (nH r) → Fin 3 → ℤ) (hH : (r : Fin m) → Fin (nH r) → Fin 6 → ℝ), ∀ r, (fun (χ D a : ℝ) (H : (Fin 6 → ℝ) → ℝ → ℝ → ℝ → ℝ) => (∀ i, MeasurableSet (AH r i)) ∧ (∀ i i', i ≠ i' → Disjoint (AH r i) (AH r i')) ∧ (∀ i, (∀ l ∈ AH r i, ⌊b k l 3 / χ⌋ = qH r i 0 ∧ ⌊b k l 0 / D⌋ = qH r i 1 ∧ ⌊b k l 1 / D⌋ = qH r i 2) ∧ (∀ e, |hH r i e| ≤ N k ^ R) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ Set.Icc ((qH r i 1 : ℝ) * D) (((qH r i 1 : ℝ) + 1) * D), ∀ q ∈ Set.Icc ((qH r i 2 : ℝ) * D) (((qH r i 2 : ℝ) + 1) * D), |H (hH r i) t p q| ≤ N k ^ ε) ∧ (∀ l ∈ AH r i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |(x k l t) 3 - H (hH r i) t (b k l 0) (b k l 1)| ≤ N k ^ ε * a) ∧ ENNReal.ofReal (D ^ 2 * a ^ d / N k ^ ε) * π k (Set.Ico ((qH r i 0 : ℝ) * χ) (((qH r i 0 : ℝ) + 1) * χ)) ≤ ρH (AH r i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ ρH {p | ∃ i, p.1 ∈ AH r i}ᶜ = 0) (N k ^ (-e₀)) (N k ^ (-u * sH r)) (N k ^ (-sH r)) (fun h t p q => h 0 + h 1 * t + (h 2 + h 3 * t) * p + (h 4 + h 5 * t) * q))) (fun k H a Q l I => ∀ t ∈ I, |MvPolynomial.eval (x k l t) Q| ≤ H * a ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ H ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤ H / a)) (fun k Nk r p e => ⌊(![p.2, (x k p.1 p.2) 1, (x k p.1 p.2) 2] : Fin 3 → ℝ) e / (Nk ^ (-r))⌋)) (fun k l t => ![t, b k l 0 + t * b k l 3, b k l 1 + t * b k l 4, b k l 2 + t * b k l 5]) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)))) true (fun κ => 2 * κ < 1)) := by
  intro hInterior N K hN hNt hK d κ ℓ S U e₀ hd0 hd1 hκ0 hκ1 hℓ hS0 hS1
    hU he₀ hreg hℓκ α _ ν μ ρ π b P T n j A B c F hbasic hcaps hlayers hnested
  obtain ⟨sMax, R, hs0, hsU, hse, hR, hfixed, hfamily⟩ :=
    hInterior N K hN hNt hK d κ ℓ S U e₀ hd0 hd1 hκ0 hκ1 hℓ hS0 hS1
      hU he₀ hreg hℓκ α ν μ ρ π b P T n j A B c F hbasic hcaps hlayers hnested
  refine ⟨sMax, R, hs0, hsU, hse, hR, hfixed, ?_⟩
  intro u hu m sH hsH ε hε
  subst u
  -- Rescale the depths by f < 1 and use the interior rate 2 * κ / f.
  -- Their product stays 2 * κ * s, so every parameter square is unchanged.
  -- Choosing f close enough to 1 absorbs the loss in fitting accuracy.
  have hw0 : 0 < 2 * κ := by positivity
  have hδ : 0 < ε / (2 * sMax) := div_pos hε (by positivity)
  obtain ⟨f, hf, hf1⟩ := exists_between
    (max_lt hreg (show 1 - ε / (2 * sMax) < 1 by linarith))
  have hwf : 2 * κ < f := lt_of_le_of_lt (le_max_left _ _) hf
  have hclose : 1 - ε / (2 * sMax) < f := lt_of_le_of_lt (le_max_right _ _) hf
  have hf0 : 0 < f := hw0.trans hwf
  have hu0 : 2 * κ < 2 * κ / f := (lt_div_iff₀ hf0).2 (by nlinarith)
  have hu1 : 2 * κ / f ≤ 1 := (div_le_one hf0).2 hwf.le
  have hnear : (1 - f) * sMax ≤ ε / 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * sMax by positivity)).mp
      (show 1 - f ≤ ε / (2 * sMax) by linarith)
    nlinarith
  have hdepth : ∀ r, 0 < f * sH r ∧ f * sH r < sMax := by
    intro r
    have hs := hsH r
    constructor
    · exact mul_pos hf0 hs.1
    · exact (mul_le_of_le_one_left hs.1.le hf1.le).trans_lt hs.2
  filter_upwards [hfamily (2 * κ / f) ⟨hu0, hu1⟩ m (fun r => f * sH r)
    hdepth (ε / 2) (half_pos hε)] with k hk
  rcases hk with ⟨ρH, hρH, hmass, nH, AH, qH, hH, hAH⟩
  have hN1 : 1 ≤ N k := le_trans (by norm_num) (hN k)
  have hN0 : 0 < N k := lt_of_lt_of_le zero_lt_one hN1
  have hεle : N k ^ (ε / 2) ≤ N k ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  refine ⟨ρH, hρH, le_trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))) hmass,
    nH, AH, qH, hH, ?_⟩
  intro r
  have hr := hAH r
  have hwidth : -(2 * κ / f) * (f * sH r) = -(2 * κ) * sH r := by
    field_simp [ne_of_gt hf0]
  rw [hwidth] at hr
  rcases hr with ⟨hA, hdisj, hrow, hsupport⟩
  refine ⟨hA, hdisj, ?_, hsupport⟩
  intro i
  rcases hrow i with ⟨hbin, hcoeff, hnorm, hfit, hfloor⟩
  refine ⟨hbin, hcoeff, ?_, ?_, ?_⟩
  · intro t ht p hp q hq
    exact (hnorm t ht p hp q hq).trans hεle
  · intro l hl t ht
    have hgap : sH r - f * sH r ≤ ε / 2 := by
      have h := mul_le_mul_of_nonneg_left (hsH r).2.le (sub_nonneg.mpr hf1.le)
      nlinarith
    have hbudget : N k ^ (ε / 2) * N k ^ (-(f * sH r)) ≤
        N k ^ ε * N k ^ (-sH r) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    exact (hfit l hl t ht).trans hbudget
  -- Since d ≥ 0, the shallower interior depth gives a stronger mass floor.
  · have ha : N k ^ (-sH r) ≤ N k ^ (-(f * sH r)) :=
      Real.rpow_le_rpow_of_exponent_le hN1
        (neg_le_neg (mul_le_of_le_one_left (hsH r).1.le hf1.le))
    apply le_trans _ hfloor
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) ha hd0) (sq_nonneg _))
      (Real.rpow_pos_of_pos hN0 _) hεle
