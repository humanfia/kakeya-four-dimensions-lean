import Mathlib
import ChallengeDeps
import Submission.Obl.k4_finite_narrowness_path_improvement.LevelMass
import Submission.Obl.k4_finite_narrowness_path_improvement.ChartCells

/-!
# The interface X is vacuous for `l > 0` and `S > 1`

`x_steep_vacuous` is the frozen interface X of o107 (its fourth part, verbatim) with the extra
hypothesis `1 < S`. With the one-level grid `m = 1`, `s = 1`, `δ₀ = l/8`, no critical path
exists at late samples: every chart of the path is narrow (`|det Q| 4^T ≤ N^(-(nw - δ₀ L))`,
`nw ≥ (l - δ₀) L`), so its velocities meet at most `48 κ³ N^u` cells of width `δ(N, u)`
(`gchart_cells`); the charts are known by the terminal observation through lists of size `κ`;
the angular cap (`S > 1`) with the pure density lower bound then charges the level mass by
`κ⁴ N^((1-S) u / 2)` plus typicality exceptions (`level_mass_le`), against the level floor
`1/κ ≥ N^(-σ)` (`steep_numeric`). This is the mechanism of paper Lemma a01:largest-axis;
in the paper the finite-narrowness palette is one-dimensional, so the engine lives in `S ≤ 1`.

`rpow_neg_le_gδ`, `cells_le_of_widths`, `steep_numeric` are the numeric steps.
-/

namespace Submission.Obl.k4_finite_narrowness_path_improvement

/-- The frozen thickness is at least `N^(-u)`. -/
theorem rpow_neg_le_gδ {N : ℝ} (u : ℝ) (hN : 1 ≤ N) : N ^ (-u) ≤ gδ N u := by
  unfold gδ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  rw [← Real.rpow_intCast, Int.cast_neg]
  have hfl : (⌊u * Real.log N / Real.log 2⌋ : ℝ) ≤ u * Real.log N / Real.log 2 := Int.floor_le _
  calc N ^ (-u) = (2 : ℝ) ^ (-(u * Real.log N / Real.log 2)) := by
        rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
        congr 1
        field_simp
    _ ≤ (2 : ℝ) ^ (-(⌊u * Real.log N / Real.log 2⌋ : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hfl)

/-- The cell count of a narrow chart at width `ε ≥ N^(-u)` when `√θ ≤ N^(-u)`. -/
theorem cells_le_of_widths {κ ε θ N u : ℝ} (hκ : 1 ≤ κ) (hN : 1 ≤ N) (hu : 0 ≤ u)
    (hε : N ^ (-u) ≤ ε) (hθ : Real.sqrt θ ≤ N ^ (-u)) :
    (4 * κ ^ 2 / ε + 2) * (4 * κ * Real.sqrt θ / ε + 4) ≤ 48 * κ ^ 3 * N ^ u := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have hNu : 0 < N ^ (-u) := Real.rpow_pos_of_pos hN0 _
  have hε0 : 0 < ε := lt_of_lt_of_le hNu hε
  have hinv : 1 / ε ≤ N ^ u := by
    rw [div_le_iff₀ hε0]
    calc (1 : ℝ) = N ^ u * N ^ (-u) := by rw [← Real.rpow_add hN0]; simp
      _ ≤ N ^ u * ε := mul_le_mul_of_nonneg_left hε (Real.rpow_nonneg hN0.le _)
  have hNu1 : 1 ≤ N ^ u := Real.one_le_rpow hN hu
  have hsq : Real.sqrt θ / ε ≤ 1 := by
    rw [div_le_one hε0]; exact hθ.trans hε
  have h1 : 4 * κ ^ 2 / ε + 2 ≤ 6 * κ ^ 2 * N ^ u := by
    have : 4 * κ ^ 2 / ε = 4 * κ ^ 2 * (1 / ε) := by ring
    rw [this]
    have hk2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
    nlinarith [mul_le_mul_of_nonneg_left hinv (by positivity : (0:ℝ) ≤ 4 * κ ^ 2)]
  have h2 : 4 * κ * Real.sqrt θ / ε + 4 ≤ 8 * κ := by
    have : 4 * κ * Real.sqrt θ / ε = 4 * κ * (Real.sqrt θ / ε) := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ 4 * κ)]
  have hpos2 : 0 ≤ 4 * κ * Real.sqrt θ / ε + 4 := by positivity
  calc (4 * κ ^ 2 / ε + 2) * (4 * κ * Real.sqrt θ / ε + 4)
      ≤ (6 * κ ^ 2 * N ^ u) * (8 * κ) := mul_le_mul h1 h2 hpos2 (by positivity)
    _ = 48 * κ ^ 3 * N ^ u := by ring

end Submission.Obl.k4_finite_narrowness_path_improvement

namespace Submission.Obl.k4_finite_narrowness_path_improvement

/-- The exponent count of the steep case: with `κ ≤ N^σ` and `σ` small, the level mass bound
`κ⁻¹ ≤ κ (48 κ³ N^u) N^(-S u + (S-1) u / 2) + 2 κ N^(-c)` fails for large `N`. -/
theorem steep_numeric {N κ u S c σ : ℝ} (hN : 1 < N) (hκ1 : 1 ≤ κ) (hκ : κ ≤ N ^ σ)
    (hσu : σ ≤ (S - 1) * u / 20) (hσc : σ ≤ c / 4)
    (hbig1 : 48 * N ^ (-((S - 1) * u / 4)) < 1 / 2) (hbig2 : 2 * N ^ (-(c / 2)) < 1 / 2) :
    ¬ (κ⁻¹ ≤ κ * (48 * κ ^ 3 * N ^ u) * N ^ (-S * u + 2 * ((S - 1) * u / 4)) +
        κ * (2 * N ^ (-c))) := by
  intro h
  have hN0 : 0 < N := lt_trans one_pos hN
  have hκ0 : 0 < κ := lt_of_lt_of_le one_pos hκ1
  have hpow : ∀ x : ℝ, 0 < N ^ x := fun x => Real.rpow_pos_of_pos hN0 x
  -- κ^4 ≤ N^(4σ)
  have hκ4 : κ ^ 4 ≤ N ^ (4 * σ) := by
    calc κ ^ 4 ≤ (N ^ σ) ^ 4 := pow_le_pow_left₀ hκ0.le hκ 4
      _ = N ^ (4 * σ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have hkinv : N ^ (-σ) ≤ κ⁻¹ := by
    rw [Real.rpow_neg hN0.le]
    exact inv_anti₀ hκ0 hκ
  -- rewrite the right side
  have hr1 : κ * (48 * κ ^ 3 * N ^ u) * N ^ (-S * u + 2 * ((S - 1) * u / 4)) =
      48 * κ ^ 4 * N ^ (-((S - 1) * u / 2)) := by
    have : N ^ u * N ^ (-S * u + 2 * ((S - 1) * u / 4)) = N ^ (-((S - 1) * u / 2)) := by
      rw [← Real.rpow_add hN0]; ring_nf
    calc κ * (48 * κ ^ 3 * N ^ u) * N ^ (-S * u + 2 * ((S - 1) * u / 4))
        = 48 * κ ^ 4 * (N ^ u * N ^ (-S * u + 2 * ((S - 1) * u / 4))) := by ring
      _ = _ := by rw [this]
  rw [hr1] at h
  -- multiply by N^σ
  have hmono : ∀ x y : ℝ, x ≤ y → N ^ x ≤ N ^ y := fun x y hxy =>
    Real.rpow_le_rpow_of_exponent_le hN.le hxy
  have key : 1 ≤ 48 * N ^ (-((S - 1) * u / 4)) + 2 * N ^ (-(c / 2)) := by
    have h' := mul_le_mul_of_nonneg_left (hkinv.trans h) (hpow σ).le
    have hl : N ^ σ * N ^ (-σ) = 1 := by rw [← Real.rpow_add hN0]; simp
    rw [hl] at h'
    refine h'.trans ?_
    have e1 : N ^ σ * (48 * κ ^ 4 * N ^ (-((S - 1) * u / 2))) ≤
        48 * N ^ (-((S - 1) * u / 4)) := by
      calc N ^ σ * (48 * κ ^ 4 * N ^ (-((S - 1) * u / 2)))
          ≤ N ^ σ * (48 * N ^ (4 * σ) * N ^ (-((S - 1) * u / 2))) := by gcongr
        _ = 48 * (N ^ σ * N ^ (4 * σ) * N ^ (-((S - 1) * u / 2))) := by ring
        _ = 48 * N ^ (σ + 4 * σ + -((S - 1) * u / 2)) := by
            rw [Real.rpow_add hN0, Real.rpow_add hN0]
        _ ≤ 48 * N ^ (-((S - 1) * u / 4)) :=
            mul_le_mul_of_nonneg_left (hmono _ _ (by linarith)) (by norm_num)
    have e2 : N ^ σ * (κ * (2 * N ^ (-c))) ≤ 2 * N ^ (-(c / 2)) := by
      calc N ^ σ * (κ * (2 * N ^ (-c))) ≤ N ^ σ * (N ^ σ * (2 * N ^ (-c))) := by gcongr
        _ = 2 * (N ^ σ * N ^ σ * N ^ (-c)) := by ring
        _ = 2 * N ^ (σ + σ + -c) := by rw [Real.rpow_add hN0, Real.rpow_add hN0]
        _ ≤ 2 * N ^ (-(c / 2)) :=
            mul_le_mul_of_nonneg_left (hmono _ _ (by linarith)) (by norm_num)
    calc N ^ σ * (48 * κ ^ 4 * N ^ (-((S - 1) * u / 2)) + κ * (2 * N ^ (-c)))
        = N ^ σ * (48 * κ ^ 4 * N ^ (-((S - 1) * u / 2))) +
            N ^ σ * (κ * (2 * N ^ (-c))) := by ring
      _ ≤ _ := add_le_add e1 e2
  linarith

end Submission.Obl.k4_finite_narrowness_path_improvement

namespace Submission.Obl.k4_finite_narrowness_path_improvement

open MeasureTheory

open scoped ENNReal

set_option maxHeartbeats 4000000 in
theorem x_steep_vacuous : ((fun x : (ℕ × (Fin 6 → ℝ)) → ℝ → Fin 4 → ℝ => (fun y : (ℕ × (Fin 6 → ℝ)) → ℝ → EuclideanSpace ℝ (Fin 2) => (fun v : (ℕ × (Fin 6 → ℝ)) → EuclideanSpace ℝ (Fin 2) => (fun δ : ℝ → ℝ → ℝ => (fun obs : ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ => (fun fmt : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop => (fun chart : ℝ → ℕ → ℕ → ℝ → ℕ → ℝ → ℝ → ℝ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ → MvPolynomial (Fin 4) ℝ → Set (ℕ × (Fin 6 → ℝ)) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → Prop → Prop => (∀ (d₁ κ₁ ℓ S η : ℝ), 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 ≤ ℓ → 0 < S → 0 < η → 0 < ℓ → 1 < S → ∃ (m : ℕ) (s : ℕ → ℝ), 0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1 ∧ ∃ Δ δ₀ : ℝ, 0 < Δ ∧ 0 < δ₀ ∧ ∀ N K : ℕ → ℝ, ∀ L d : ℝ, ∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ), ∀ (g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧ 0 < L ∧ 0 < d ∧ d < 1 ∧ 0 < S ∧ 0 < η ∧ (fun μ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) => (∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (fmt 6 (N k ^ M) D (A j)) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (fmt 7 (N k ^ M) D ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}))) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(y l t)‖ + ‖(v l)‖ ≤ K k ∧ |MvPolynomial.eval (x l t) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(μ k γ), B k γ / K k ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) Set.univ) ∧ (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧ MeasureTheory.Measure.map (obs (B k γ) (δ (N k) r)) (μ k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) ∧ (∀ k γ u, 0 < u → u ≤ η * L → Measurable (G k γ u) ∧ MeasureTheory.Measure.map (fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) (μ k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)) ∧ (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r) ∧ (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | g k γ r ((obs (B k γ) (δ (N k) r)) p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r ((obs (B k γ) (δ (N k) r)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))) ∧ (∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) ∧ (∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u ((fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c)))) (fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) → (∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - d₁ * r| ≤ δ₀ * L) → ∀ Mp Dp : ℕ, ∃ Mi Di : ℕ, ∀ τ : ℝ, 0 < τ → ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (κ : ℝ) (C : ℕ) (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin (W k)) (j : Fin C → ℕ) (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (lst : ℕ → Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)), 1 ≤ κ → κ ≤ N k ^ σ → (C : ℝ) ≤ N k ^ Mp → r (m - 1) = L → (∀ i, i < m → |r i - s i * L| ≤ δ₀ * L ∧ 0 < r i ∧ N k ^ ((κ₁ * s i - δ₀) * L) ≤ (2 : ℝ) ^ T i ∧ (2 : ℝ) ^ T i ≤ N k ^ ((κ₁ * s i + δ₀) * L) ∧ |nw i - ℓ * s i * L| ≤ δ₀ * L ∧ ENNReal.ofReal κ⁻¹ ≤ ∑ b, if lev b = i then ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod MeasureTheory.volume) (F b) else 0) → (∀ i γ₁ o, ((lst i γ₁ o).card : ℝ) ≤ κ) → (∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) → (∀ b, lev b < m ∧ j b < 2 ^ T (lev b) ∧ chart (N k) Mp Dp κ (T (lev b)) (j b : ℝ) (r (lev b)) (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f (r (lev b))) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T (lev b) * κ)) ≤ ((ν k (γ b)).prod MeasureTheory.volume) (F b) ∧ ν k (γ b) (A b) ≤ ENNReal.ofReal (κ * N k ^ (-f (r (lev b))) * |Matrix.det (Q b)|) ∧ N k ^ (-(nw (lev b) + δ₀ * L)) ≤ |Matrix.det (Q b)| * (4 : ℝ) ^ T (lev b) ∧ |Matrix.det (Q b)| * (4 : ℝ) ^ T (lev b) ≤ N k ^ (-(nw (lev b) - δ₀ * L)) ∧ (∀ p ∈ F b, b ∈ lst (lev b) (γ b) (obs (B k (γ b)) (δ (N k) (r (lev b))) p)) ∧ (0 < lev b → lev (par b) + 1 = lev b ∧ γ (par b) = γ b ∧ A b ⊆ A (par b) ∧ F b ⊆ F (par b) ∧ (j (par b) : ℝ) / (2 : ℝ) ^ T (lev (par b)) ≤ (j b : ℝ) / (2 : ℝ) ^ T (lev b) ∧ ((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b) ≤ ((j (par b) : ℝ) + 1) / (2 : ℝ) ^ T (lev (par b))))) → ∃ (r₂ : ℝ) (T₂ C₂ : ℕ) (γ₂ : Fin C₂ → Fin (W k)) (j₂ : Fin C₂ → Fin (2 ^ T₂)) (c₂ u₂ : Fin C₂ → EuclideanSpace ℝ (Fin 2)) (Q₂ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ) (R₂ : Fin C₂ → MvPolynomial (Fin 4) ℝ) (A₂ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ))) (F₂ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (lst₂ : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)), r₂ + Δ * L ≤ L ∧ ((Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ N k ^ (κ₁ * Δ * L / 2)) ∨ ∃ i, i < m ∧ ((r i + Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i * N k ^ (κ₁ * Δ * L / 2)) ∨ (r₂ = r i ∧ T₂ = T i ∧ ∀ b, |Matrix.det (Q₂ b)| * (4 : ℝ) ^ T₂ ≤ N k ^ (-(nw i + Δ * L))))) ∧ (C₂ : ℝ) ≤ N k ^ Mi ∧ (∀ b b', b ≠ b' → γ₂ b = γ₂ b' → j₂ b = j₂ b' → Disjoint (A₂ b) (A₂ b')) ∧ (∀ γ₁ o, ((lst₂ γ₁ o).card : ℝ) ≤ N k ^ τ) ∧ (∀ b, chart (N k) Mi Di (N k ^ τ) T₂ ((j₂ b : ℕ) : ℝ) r₂ (B k (γ₂ b)) (E k (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b) (∀ p ∈ F₂ b, b ∈ lst₂ (γ₂ b) (obs (B k (γ₂ b)) (δ (N k) L) p))) ∧ ENNReal.ofReal (N k ^ (-τ)) ≤ ∑ b, ENNReal.ofReal (ω k (γ₂ b)) * ((ν k (γ₂ b)).prod MeasureTheory.volume) (F₂ b))) (fun Nk M D κ T j r Bv Ev c u Q R A F ex => Matrix.det Q ≠ 0 ∧ ‖c‖ + ‖u‖ ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧ R.totalDegree ≤ 2 ∧ (∀ e, |R.coeff e| ≤ Nk ^ M) ∧ MeasurableSet A ∧ MeasurableSet F ∧ (∀ i, fmt 6 (Nk ^ M) D {x | (i, x) ∈ A} ∧ fmt 7 (Nk ^ M) D {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F}) ∧ (∀ l ∈ A, (l.1 : ℝ) ≤ Nk ^ M ∧ (∀ e, |l.2 e| ≤ Nk ^ M) ∧ ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ ∧ |MvPolynomial.eval (x l t) R| ≤ κ * δ Nk r ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ κ * Bv ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤ κ * Bv ^ 2 / δ Nk r) ∧ (∀ p ∈ F, p ∈ Ev ∧ p.1 ∈ A ∧ p.2 ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧ Bv / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) ∧ ex)) (fun n H D A => ∃ m₀ : ℕ, (m₀ : ℝ) ≤ H ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin n) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ A ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) (fun B a p => (WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2], ⌊B * (x p.1 p.2) 3 / a⌋))) (fun N r => (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ)))) (fun l => WithLp.toLp 2 ![l.2 3, l.2 4])) (fun l t => WithLp.toLp 2 ![(x l t) 1, (x l t) 2])) (fun l t => ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5])) := by
  intro d₁ κ₁ ℓ S η hd₁ hd₁' hκ₁ hκ₁' hℓ0 hS hη hℓ hS1
  refine ⟨1, fun _ => 1, Nat.one_pos, one_pos, fun i hi => absurd hi (by omega), rfl,
    1 / 4, ℓ / 8, by norm_num, by positivity, ?_⟩
  intro N K L d W ω ν E P B f g G hprob hlin Mp Dp
  refine ⟨0, 0, ?_⟩
  intro τ hτ
  obtain ⟨hN2, hNt, hK, hL, hd0, hd1, hS0, hη0, hrest⟩ := hprob
  obtain ⟨htemp, hgmap, hGmap, hfmono, hpure, hcap, hang⟩ := hrest
  set u : ℝ := min η (ℓ / 4) * L / 2 with hu_def
  have hmin : 0 < min η (ℓ / 4) := lt_min hη (by positivity)
  have hu : 0 < u := by positivity
  have huη : u ≤ η * L := by
    have := min_le_left η (ℓ / 4)
    rw [hu_def]; nlinarith
  have huℓ : u ≤ ℓ * L / 8 := by
    have := min_le_right η (ℓ / 4)
    rw [hu_def]; nlinarith
  set τ' : ℝ := (S - 1) * u / 4 with hτ'_def
  have hS1' : 0 < S - 1 := by linarith
  have hτ' : 0 < τ' := by positivity
  obtain ⟨c₁, hc₁, hev₁⟩ := hang u τ' hu huη hτ'
  obtain ⟨c₂, hc₂, hev₂⟩ := hpure L τ' hL.le le_rfl hτ'
  set c := min c₁ c₂ with hc_def
  have hc : 0 < c := lt_min hc₁ hc₂
  set σ := min (c / 4) ((S - 1) * u / 20) with hσ_def
  have hσ : 0 < σ := lt_min (by positivity) (by positivity)
  have hlim : ∀ a : ℝ, 0 < a → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, N k ^ (-a) < ε :=
    fun a ha ε hε => ((tendsto_rpow_neg_atTop ha).comp hNt).eventually (gt_mem_nhds hε)
  have hlim1 := hlim ((S - 1) * u / 4) (by positivity) (1 / 96) (by norm_num)
  have hlim2 := hlim (c / 2) (by positivity) (1 / 4) (by norm_num)
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp (hev₁.and (hev₂.and (hlim1.and hlim2)))
  refine ⟨σ, hσ, k₀, ?_⟩
  intro k hk r T nw κ C lev par γ j c' u' Q R A F lst hκ1 hκN hC hrm hlev hlst hdisj hcharts
  exfalso
  obtain ⟨hev1k, hev2k, hb1, hb2⟩ := hk₀ k hk
  have hN2k : 2 ≤ N k := hN2 k
  have hN1 : 1 ≤ N k := by linarith
  have hN1' : 1 < N k := by linarith
  have hN0 : 0 < N k := by linarith
  obtain ⟨hr0, hr0pos, hT0lo, hT0hi, hnw0, hmass0⟩ := hlev 0 Nat.one_pos
  have hrL : r 0 = L := hrm
  have hlev0 : ∀ b, lev b = 0 := fun b => by have := (hcharts b).1; omega
  have hchart : ∀ b, gchart (N k) Mp Dp κ (T 0) ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b))
      (c' b) (u' b) (Q b) (R b) (A b) (F b) True ∧
      |Matrix.det (Q b)| * (4 : ℝ) ^ T 0 ≤ N k ^ (-(nw 0 - ℓ / 8 * L)) ∧
      (∀ p ∈ F b, b ∈ lst 0 (γ b) (gobs (B k (γ b)) (gδ (N k) L) p)) := by
    intro b
    obtain ⟨-, -, hcb⟩ := hcharts b
    rw [hlev0 b, hrL] at hcb
    obtain ⟨hQ, hcu, hQQ, hQs, hdeg, hcoef, hAm, hFm, hfmt, hAl, hFp, hfloor, hsat, hnlo, hnhi,
      hlb, hpar⟩ := hcb
    exact ⟨⟨hQ, hcu, hQQ, hQs, hdeg, hcoef, hAm, hFm, hfmt, hAl, hFp, trivial⟩, hnhi, hlb⟩
  have hκ0 : 0 ≤ κ := by linarith
  have hnw0' : ℓ * L - ℓ / 8 * L ≤ nw 0 := by
    have := (abs_le.mp hnw0).1
    simp only [mul_one] at this
    linarith
  have hθ : Real.sqrt (N k ^ (-(nw 0 - ℓ / 8 * L))) ≤ N k ^ (-u) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    nlinarith
  have hcells : ∀ b, ∃ V : Finset (Fin 2 → ℤ), (V.card : ℝ) ≤ 48 * κ ^ 3 * N k ^ u ∧
      ∀ l ∈ A b, (fun j => ⌊(gv l) j / gδ (N k) u⌋) ∈ V := by
    intro b
    obtain ⟨V, hV, hmem⟩ := gchart_cells (hchart b).1 (hchart b).2.1 (gδ_pos (N k) u) hκ0
    exact ⟨V, hV.trans (cells_le_of_widths hκ1 hN1 hu.le (rpow_neg_le_gδ u hN1) hθ), hmem⟩
  choose V hVcard hVmem using hcells
  set Mc : ℕ := ⌊48 * κ ^ 3 * N k ^ u⌋₊ with hMc
  have hM : ∀ b, (V b).card ≤ Mc := fun b => Nat.le_floor (hVcard b)
  obtain ⟨M₀, D₀, htk⟩ := htemp
  obtain ⟨-, hω0, hω1, hγw, -⟩ := htk k
  have hprobm : ∀ γ₀, MeasureTheory.IsProbabilityMeasure (ν k γ₀) := fun γ₀ => (hγw γ₀).1
  have hEsub : ∀ γ₀, E k γ₀ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := fun γ₀ =>
    (hγw γ₀).2.2.2.2.2.2.2.2.1
  have hFm : ∀ b, MeasurableSet (F b) := fun b => (hchart b).1.2.2.2.2.2.2.2.1
  have hFp : ∀ b, ∀ p ∈ F b, p ∈ E k (γ b) ∧ p.1 ∈ A b := fun b p hp =>
    ⟨((hchart b).1.2.2.2.2.2.2.2.2.2.2.1 p hp).1, ((hchart b).1.2.2.2.2.2.2.2.2.2.2.1 p hp).2.1⟩
  set α := ENNReal.ofReal (N k ^ (-f L - S * u + τ')) with hα
  set β := ENNReal.ofReal (N k ^ (-f L - τ')) with hβdef
  have hβ : β ≠ 0 := by
    rw [hβdef]
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hN0 _)).ne'
  have hLM := level_mass_le (ω k) (ν k) (E k) hEsub (B k) (gδ (N k) L) (gδ (N k) u)
    (fun γ₀ => g k γ₀ L) (fun γ₀ => (hgmap k γ₀ L hL.le le_rfl).1)
    (fun γ₀ => (hgmap k γ₀ L hL.le le_rfl).2)
    (fun γ₀ => G k γ₀ u) (fun γ₀ => (hGmap k γ₀ u hu huη).1)
    (fun γ₀ => (hGmap k γ₀ u hu huη).2)
    γ F hFm (fun b p hp => (hFp b p hp).1) (lst 0) (fun b p hp => (hchart b).2.2 p hp) ⌊κ⌋₊
    (fun γ₀ o => Nat.le_floor (hlst 0 γ₀ o)) V (fun b p hp => hVmem b p.1 (hFp b p hp).2)
    Mc hM α β hβ
  -- the level mass
  have hlevel : ENNReal.ofReal κ⁻¹ ≤
      ∑ b, ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod volume) (F b) := by
    refine hmass0.trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
    simp only [hlev0 b, ite_true]
  -- total incidence mass at most one
  have hsum1 : ∑ γ₀, ENNReal.ofReal (ω k γ₀) *
      (((ν k γ₀).prod volume).restrict (E k γ₀)) Set.univ ≤ 1 := by
    calc ∑ γ₀, ENNReal.ofReal (ω k γ₀) * (((ν k γ₀).prod volume).restrict (E k γ₀)) Set.univ
        ≤ ∑ γ₀, ENNReal.ofReal (ω k γ₀) * 1 := by
          refine Finset.sum_le_sum fun γ₀ _ => ?_
          gcongr
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          calc ((ν k γ₀).prod volume) (E k γ₀)
              ≤ ((ν k γ₀).prod volume) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := measure_mono (hEsub γ₀)
            _ = 1 := by rw [Measure.prod_prod]; simp
      _ = ENNReal.ofReal (∑ γ₀, ω k γ₀) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun γ₀ _ => hω0 γ₀)]; simp
      _ = 1 := by rw [hω1, ENNReal.ofReal_one]
  -- the bad mass, from the typicality hypotheses
  have hbad : ∑ γ₀, ENNReal.ofReal (ω k γ₀) * (((ν k γ₀).prod volume).restrict (E k γ₀))
      {p | α < G k γ₀ u (gobs (B k γ₀) (gδ (N k) L) p, fun j : Fin 2 =>
        ⌊(gv p.1) j / gδ (N k) u⌋) ∨ g k γ₀ L (gobs (B k γ₀) (gδ (N k) L) p) < β} ≤
      ENNReal.ofReal (N k ^ (-c₁)) + ENNReal.ofReal (N k ^ (-c₂)) := by
    calc _ ≤ ∑ γ₀, ENNReal.ofReal (ω k γ₀) *
          ((((ν k γ₀).prod volume).restrict (E k γ₀))
            {p | α < G k γ₀ u (gobs (B k γ₀) (gδ (N k) L) p, fun j : Fin 2 =>
              ⌊(gv p.1) j / gδ (N k) u⌋)} +
          (((ν k γ₀).prod volume).restrict (E k γ₀))
            {p | g k γ₀ L (gobs (B k γ₀) (gδ (N k) L) p) < β ∨
              ENNReal.ofReal (N k ^ (-f L + τ')) < g k γ₀ L (gobs (B k γ₀) (gδ (N k) L) p)}) := by
          refine Finset.sum_le_sum fun γ₀ _ => ?_
          gcongr
          refine (measure_mono ?_).trans (measure_union_le _ _)
          intro p hp
          rcases hp with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
      _ = (∑ γ₀, ENNReal.ofReal (ω k γ₀) * (((ν k γ₀).prod volume).restrict (E k γ₀))
            {p | α < G k γ₀ u (gobs (B k γ₀) (gδ (N k) L) p, fun j : Fin 2 =>
              ⌊(gv p.1) j / gδ (N k) u⌋)}) +
          (∑ γ₀, ENNReal.ofReal (ω k γ₀) * (((ν k γ₀).prod volume).restrict (E k γ₀))
            {p | g k γ₀ L (gobs (B k γ₀) (gδ (N k) L) p) < β ∨
              ENNReal.ofReal (N k ^ (-f L + τ')) < g k γ₀ L (gobs (B k γ₀) (gδ (N k) L) p)}) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun γ₀ _ => ?_
          rw [mul_add]
      _ ≤ _ := add_le_add hev1k hev2k
  have hαβ : α / β = ENNReal.ofReal (N k ^ (-S * u + 2 * ((S - 1) * u / 4))) := by
    rw [hα, hβdef, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hN0 _),
      ← Real.rpow_sub hN0]
    congr 2
    rw [hτ'_def]
    ring
  set e := N k ^ (-S * u + 2 * ((S - 1) * u / 4)) with he
  have he0 : 0 ≤ e := (Real.rpow_pos_of_pos hN0 _).le
  have hc10 : 0 ≤ N k ^ (-c₁) := (Real.rpow_pos_of_pos hN0 _).le
  have hc20 : 0 ≤ N k ^ (-c₂) := (Real.rpow_pos_of_pos hN0 _).le
  have hfin : ENNReal.ofReal κ⁻¹ ≤ ENNReal.ofReal ((⌊κ⌋₊ : ℝ) * (Mc : ℝ) * e +
      (⌊κ⌋₊ : ℝ) * (N k ^ (-c₁) + N k ^ (-c₂))) := by
    calc ENNReal.ofReal κ⁻¹ ≤ _ := hlevel
      _ ≤ _ := hLM
      _ ≤ ((⌊κ⌋₊ : ℝ≥0∞) * Mc * (α / β)) * 1 +
          ⌊κ⌋₊ * (ENNReal.ofReal (N k ^ (-c₁)) + ENNReal.ofReal (N k ^ (-c₂))) := by
          gcongr
      _ = _ := by
          rw [hαβ, mul_one, ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hc10 hc20,
            ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfin
  have hfl : (⌊κ⌋₊ : ℝ) ≤ κ := Nat.floor_le hκ0
  have hMc : (Mc : ℝ) ≤ 48 * κ ^ 3 * N k ^ u := Nat.floor_le (by positivity)
  have hcc1 : N k ^ (-c₁) ≤ N k ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (min_le_left _ _))
  have hcc2 : N k ^ (-c₂) ≤ N k ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (min_le_right _ _))
  apply steep_numeric hN1' hκ1 hκN (min_le_right _ _) (min_le_left _ _)
    (by linarith) (by linarith)
  calc κ⁻¹ ≤ _ := hfin
    _ ≤ κ * (48 * κ ^ 3 * N k ^ u) * e + κ * (2 * N k ^ (-c)) := by
        gcongr
        linarith

end Submission.Obl.k4_finite_narrowness_path_improvement
