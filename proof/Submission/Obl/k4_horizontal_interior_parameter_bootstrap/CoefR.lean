import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.Interface

/-!
# Recovering the coefficient budget

The frozen conclusion of o245 asks for a coefficient budget `|h_e| ≤ N k ^ R` with one `R`
for every rate. It need not be carried through the bootstrap: an affine predictor bounded by
`M` on a whole parameter square `[p₀, p₀ + D] × [q₀, q₀ + D]` over unit time has every
coefficient at most `2 M + (4 M / D) (|p₀| + |q₀| + 1)` (`coef_of_square`). Active squares
contain a trajectory with `|b₀| + |b₁| ≤ K`, so for depths below `1/100` and losses below
`1/100` this is at most `N ^ 2` eventually (`coef_numeric`).

`budget_of_layers` turns `LayersAt` (no budget) into `BudgetLayersAt` with `R = 2`, for every
rate `u ≤ 1` and every `sMax ≤ 1/100`. Labels are first restricted to the full-measure set
`{|b₀| + |b₁| + |b₃| + |b₄| ≤ K}`; a label left empty carries no palette mass by its floor and
gets the zero predictor.
-/

open MeasureTheory Filter Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap

/-- The affine predictor shape of the frozen layers. -/
def predH (h : Fin 6 → ℝ) (t p q : ℝ) : ℝ :=
  h 0 + h 1 * t + (h 2 + h 3 * t) * p + (h 4 + h 5 * t) * q

/-- Coefficients of an affine predictor from its bound on a whole parameter square. -/
theorem coef_of_square {h : Fin 6 → ℝ} {M D p0 q0 : ℝ} (hD : 0 < D)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc p0 (p0 + D), ∀ q ∈ Icc q0 (q0 + D),
      |predH h t p q| ≤ M) :
    ∀ e, |h e| ≤ 2 * M + 4 * M / D * (|p0| + |q0| + 1) := by
  have ht0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have ht1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have hp0 : p0 ∈ Icc p0 (p0 + D) := ⟨le_refl _, by linarith⟩
  have hp1 : p0 + D ∈ Icc p0 (p0 + D) := ⟨by linarith, le_refl _⟩
  have hq0 : q0 ∈ Icc q0 (q0 + D) := ⟨le_refl _, by linarith⟩
  have hq1 : q0 + D ∈ Icc q0 (q0 + D) := ⟨by linarith, le_refl _⟩
  have a00 := hb 0 ht0 p0 hp0 q0 hq0
  have a0p := hb 0 ht0 (p0 + D) hp1 q0 hq0
  have a0q := hb 0 ht0 p0 hp0 (q0 + D) hq1
  have a10 := hb 1 ht1 p0 hp0 q0 hq0
  have a1p := hb 1 ht1 (p0 + D) hp1 q0 hq0
  have a1q := hb 1 ht1 p0 hp0 (q0 + D) hq1
  simp only [predH] at a00 a0p a0q a10 a1p a1q
  have hM : 0 ≤ M := le_trans (abs_nonneg _) a00
  set c : ℝ := M / D with hc
  have hc0 : 0 ≤ c := div_nonneg hM hD.le
  have hcD : c * D = M := by rw [hc]; field_simp
  -- slopes in `p` and `q` at times `0` and `1`
  have slope : ∀ {x y z : ℝ}, |x| ≤ M → |y| ≤ M → y - x = z * D → |z| ≤ 2 * c := by
    intro x y z hx hy hxy
    have h1 : |z * D| ≤ 2 * M := by
      rw [← hxy]; exact (abs_sub _ _).trans (by linarith)
    rw [abs_mul, abs_of_pos hD] at h1
    have : |z| * D ≤ 2 * c * D := by rw [mul_assoc, hcD]; exact h1
    exact le_of_mul_le_mul_right this hD
  have b2 : |h 2| ≤ 2 * c := slope a00 a0p (by ring)
  have b4 : |h 4| ≤ 2 * c := slope a00 a0q (by ring)
  have b23 : |h 2 + h 3| ≤ 2 * c := slope a10 a1p (by ring)
  have b45 : |h 4 + h 5| ≤ 2 * c := slope a10 a1q (by ring)
  have hP : 0 ≤ |p0| := abs_nonneg _
  have hQ : 0 ≤ |q0| := abs_nonneg _
  have prod_le : ∀ {x y : ℝ}, |x| ≤ 2 * c → |x * y| ≤ 2 * c * |y| := by
    intro x y hx
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  -- intercepts at times `0` and `1`
  have b0 : |h 0| ≤ M + 2 * c * (|p0| + |q0|) := by
    have e : h 0 = (h 0 + (h 2 + h 3 * 0) * p0 + (h 4 + h 5 * 0) * q0) - h 2 * p0 - h 4 * q0 := by
      ring
    have e2 : h 0 + h 1 * 0 + (h 2 + h 3 * 0) * p0 + (h 4 + h 5 * 0) * q0 =
        h 0 + (h 2 + h 3 * 0) * p0 + (h 4 + h 5 * 0) * q0 := by ring
    rw [e2] at a00
    rw [e]
    calc |(h 0 + (h 2 + h 3 * 0) * p0 + (h 4 + h 5 * 0) * q0) - h 2 * p0 - h 4 * q0|
        ≤ |h 0 + (h 2 + h 3 * 0) * p0 + (h 4 + h 5 * 0) * q0| + |h 2 * p0| + |h 4 * q0| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ M + 2 * c * |p0| + 2 * c * |q0| := by
          gcongr
          · exact prod_le b2
          · exact prod_le b4
      _ = M + 2 * c * (|p0| + |q0|) := by ring
  have b01 : |h 0 + h 1| ≤ M + 2 * c * (|p0| + |q0|) := by
    have e : h 0 + h 1 = (h 0 + h 1 * 1 + (h 2 + h 3 * 1) * p0 + (h 4 + h 5 * 1) * q0)
        - (h 2 + h 3) * p0 - (h 4 + h 5) * q0 := by ring
    rw [e]
    calc |(h 0 + h 1 * 1 + (h 2 + h 3 * 1) * p0 + (h 4 + h 5 * 1) * q0)
          - (h 2 + h 3) * p0 - (h 4 + h 5) * q0|
        ≤ |h 0 + h 1 * 1 + (h 2 + h 3 * 1) * p0 + (h 4 + h 5 * 1) * q0|
            + |(h 2 + h 3) * p0| + |(h 4 + h 5) * q0| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ M + 2 * c * |p0| + 2 * c * |q0| := by
          gcongr
          · exact prod_le b23
          · exact prod_le b45
      _ = M + 2 * c * (|p0| + |q0|) := by ring
  have key : 4 * M / D * (|p0| + |q0| + 1) = 4 * c * (|p0| + |q0| + 1) := by
    rw [hc]; ring
  rw [key]
  have hcP : 0 ≤ c * (|p0| + |q0|) := by positivity
  have h1' : |h 1| ≤ |h 0 + h 1| + |h 0| := by
    have := abs_sub (h 0 + h 1) (h 0)
    simp only [add_sub_cancel_left] at this
    exact this
  have h3' : |h 3| ≤ |h 2 + h 3| + |h 2| := by
    have := abs_sub (h 2 + h 3) (h 2)
    simp only [add_sub_cancel_left] at this
    exact this
  have h5' : |h 5| ≤ |h 4 + h 5| + |h 4| := by
    have := abs_sub (h 4 + h 5) (h 4)
    simp only [add_sub_cancel_left] at this
    exact this
  have B0 : |h 0| ≤ 2 * M + 4 * c * (|p0| + |q0| + 1) := by nlinarith
  have B1 : |h 1| ≤ 2 * M + 4 * c * (|p0| + |q0| + 1) := by nlinarith
  have B2 : |h 2| ≤ 2 * M + 4 * c * (|p0| + |q0| + 1) := by nlinarith
  have B3 : |h 3| ≤ 2 * M + 4 * c * (|p0| + |q0| + 1) := by nlinarith
  have B4 : |h 4| ≤ 2 * M + 4 * c * (|p0| + |q0| + 1) := by nlinarith
  have B5 : |h 5| ≤ 2 * M + 4 * c * (|p0| + |q0| + 1) := by nlinarith
  intro e
  fin_cases e
  exacts [B0, B1, B2, B3, B4, B5]

/-- The numerical budget: with `K, M, 1/D ≤ N^(1/100)` and `N ≥ 22`, the square bound of
`coef_of_square` is at most `N ^ 2`. -/
theorem coef_numeric {N K M D p0 q0 : ℝ} (hN : 22 ≤ N) (hK0 : 0 ≤ K)
    (hK : K ≤ N ^ (1 / 100 : ℝ)) (hM0 : 0 ≤ M) (hM : M ≤ N ^ (1 / 100 : ℝ)) (hD0 : 0 < D)
    (hD : N ^ (-(1 / 100 : ℝ)) ≤ D) (hp : |p0| ≤ K + D) (hq : |q0| ≤ K + D) :
    2 * M + 4 * M / D * (|p0| + |q0| + 1) ≤ N ^ (2 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  set n : ℝ := N ^ (1 / 100 : ℝ) with hn
  have hn1 : 1 ≤ n := Real.one_le_rpow hN1 (by norm_num)
  have hinv : 1 / D ≤ n := by
    rw [div_le_iff₀ hD0]
    have : N ^ (-(1 / 100 : ℝ)) * n = 1 := by
      rw [hn, ← Real.rpow_add hN0]; norm_num
    nlinarith
  have hsum : (|p0| + |q0| + 1) / D ≤ (2 * K + 1) * n + 2 := by
    have h1 : (|p0| + |q0| + 1) / D ≤ (2 * K + 2 * D + 1) / D :=
      div_le_div_of_nonneg_right (by linarith) hD0.le
    have h2 : (2 * K + 2 * D + 1) / D = (2 * K + 1) * (1 / D) + 2 := by
      field_simp
      ring
    rw [h2] at h1
    have h3 : (2 * K + 1) * (1 / D) ≤ (2 * K + 1) * n :=
      mul_le_mul_of_nonneg_left hinv (by linarith)
    linarith
  have hmain : 2 * M + 4 * M / D * (|p0| + |q0| + 1) ≤ 22 * n ^ 3 := by
    have e : 4 * M / D * (|p0| + |q0| + 1) = 4 * M * ((|p0| + |q0| + 1) / D) := by ring
    rw [e]
    have hpos : 0 ≤ (|p0| + |q0| + 1) / D := div_nonneg (by positivity) hD0.le
    have hK' : (2 * K + 1) * n + 2 ≤ (2 * n + 1) * n + 2 := by nlinarith
    have h4 : 4 * M * ((|p0| + |q0| + 1) / D) ≤ 4 * n * ((2 * n + 1) * n + 2) := by
      calc 4 * M * ((|p0| + |q0| + 1) / D) ≤ 4 * n * ((|p0| + |q0| + 1) / D) := by
            gcongr
        _ ≤ 4 * n * ((2 * n + 1) * n + 2) := by
            gcongr
            exact hsum.trans hK'
    have h5 : 4 * n * ((2 * n + 1) * n + 2) = 8 * n ^ 3 + 4 * n ^ 2 + 8 * n := by ring
    have hn2 : n ≤ n ^ 3 := by nlinarith
    have hn3 : n ^ 2 ≤ n ^ 3 := by nlinarith
    linarith

  have hcube : n ^ 3 = N ^ (3 / 100 : ℝ) := by
    rw [hn, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hsplit : N ^ (2 : ℝ) = N ^ (3 / 100 : ℝ) * N ^ (197 / 100 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hbig : 22 ≤ N ^ (197 / 100 : ℝ) := by
    have : N ^ (1 : ℝ) ≤ N ^ (197 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    rw [Real.rpow_one] at this; linarith
  have hpos : 0 ≤ N ^ (3 / 100 : ℝ) := Real.rpow_nonneg hN0.le _
  calc 2 * M + 4 * M / D * (|p0| + |q0| + 1) ≤ 22 * n ^ 3 := hmain
    _ = 22 * N ^ (3 / 100 : ℝ) := by rw [hcube]
    _ ≤ N ^ (197 / 100 : ℝ) * N ^ (3 / 100 : ℝ) := by gcongr
    _ = N ^ (2 : ℝ) := by rw [hsplit]; ring

/-- A floor cell contains its point: `|n D| ≤ |x| + D` when `⌊x / D⌋ = n`. -/
theorem abs_floor_mul_le {x D : ℝ} {n : ℤ} (hD : 0 < D) (h : ⌊x / D⌋ = n) :
    |(n : ℝ) * D| ≤ |x| + D := by
  have h1 : (n : ℝ) ≤ x / D := by rw [← h]; exact Int.floor_le _
  have h2 : x / D < (n : ℝ) + 1 := by rw [← h]; exact Int.lt_floor_add_one _
  have h1' : (n : ℝ) * D ≤ x := by rwa [le_div_iff₀ hD] at h1
  have h2' : x < ((n : ℝ) + 1) * D := by rwa [div_lt_iff₀ hD] at h2
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg x, le_abs_self x, neg_abs_le x]

/-- `ρH` gives no mass to trajectories outside the a.e. parameter bound. -/
theorem null_of_ae_bound {α : Type} [MeasurableSpace α] {ν : Measure α}
    {μ ρH : Measure (α × ℝ)} {K : ℝ} (hμ : μ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hρ : ρH ≤ μ) {G : Set α} (hG : ν Gᶜ = 0) : ρH (Gᶜ ×ˢ univ) = 0 := by
  refine le_antisymm ?_ bot_le
  calc ρH (Gᶜ ×ˢ univ) ≤ μ (Gᶜ ×ˢ univ) := hρ _
    _ ≤ (ENNReal.ofReal K • (ν.prod volume)) (Gᶜ ×ˢ univ) := hμ _
    _ = 0 := by
        rw [Measure.smul_apply, Measure.prod_prod, hG, zero_mul, smul_zero]

/-- The coefficient budget `R = 2` from `LayersAt`, for every rate `u ≤ 1` and every
`sMax ≤ 1/100`. -/
theorem budget_of_layers {N K : ℕ → ℝ} (hN2 : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {d e₀ u sMax : ℝ} (hu : u ≤ 1) (hsMax : sMax ≤ 1 / 100)
    {α : Type} [MeasurableSpace α] {ν : ℕ → Measure α} {μ ρ : ℕ → Measure (α × ℝ)}
    {π : ℕ → Measure ℝ} {b : ℕ → α → Fin 6 → ℝ} {P : ℕ → MvPolynomial (Fin 4) ℝ}
    (h1 : Hyp1 K ν μ ρ π b P) (hL : LayersAt N d e₀ u sMax ρ π b) :
    BudgetLayersAt N d e₀ 2 u sMax ρ π b := by
  classical
  intro m sH hsH ε hε
  set ε' : ℝ := min ε (1 / 100) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'1 : ε' ≤ 1 / 100 := min_le_right _ _
  filter_upwards [hL m sH hsH ε' hε'0, hK.2 (1 / 100) (by norm_num),
    hNt.eventually_ge_atTop 22] with k hk hKk hNk
  obtain ⟨ρH, hρH, hmass, nH, AH, qH, hH, hlay⟩ := hk
  obtain ⟨hbm, -, -, hμle, hρle, -, -, -, hbae, -⟩ := h1 k
  have hN0 : 0 < N k := by linarith [hN2 k]
  have hN1 : 1 ≤ N k := by linarith [hN2 k]
  have hK1 : 1 ≤ K k := hK.1 k
  have hpow : N k ^ ε' ≤ N k ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 hε'ε
  set G : Set α := {l | |b k l 0| + |b k l 1| + |b k l 3| + |b k l 4| ≤ K k} with hGdef
  have hGm : MeasurableSet G := by
    have hc : ∀ i : Fin 6, Measurable fun l => b k l i := fun i => (measurable_pi_apply i).comp hbm
    exact measurableSet_le (by fun_prop) measurable_const
  have hGc : ν k Gᶜ = 0 := by
    rw [ae_iff] at hbae
    simpa [hGdef, Set.compl_ofPred] using hbae
  have hGnull : ρH (Gᶜ ×ˢ univ) = 0 := null_of_ae_bound hμle (hρH.trans hρle) hGc
  -- restrict every label to `G`
  have hsplit : ∀ S : Set α, ρH (S ×ˢ Icc (0 : ℝ) 1) = ρH ((S ∩ G) ×ˢ Icc (0 : ℝ) 1) := by
    intro S
    apply le_antisymm
    · calc ρH (S ×ˢ Icc (0 : ℝ) 1) ≤ ρH ((S ∩ G) ×ˢ Icc (0 : ℝ) 1 ∪ Gᶜ ×ˢ univ) := by
            apply measure_mono
            rintro ⟨l, t⟩ ⟨hl, ht⟩
            by_cases hlG : l ∈ G
            · exact Or.inl ⟨⟨hl, hlG⟩, ht⟩
            · exact Or.inr ⟨hlG, trivial⟩
        _ ≤ ρH ((S ∩ G) ×ˢ Icc (0 : ℝ) 1) + ρH (Gᶜ ×ˢ univ) := measure_union_le _ _
        _ = ρH ((S ∩ G) ×ˢ Icc (0 : ℝ) 1) := by rw [hGnull, add_zero]
    · exact measure_mono (prod_mono inter_subset_left le_rfl)
  refine ⟨ρH, hρH, le_trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))) hmass, nH,
    fun r i => AH r i ∩ G, qH,
    fun r i => if (AH r i ∩ G).Nonempty then hH r i else 0, fun r => ?_⟩
  have hl := hlay r
  dsimp only [LayerAt] at hl
  obtain ⟨hmeas, hdisj, hrow, hcov⟩ := hl
  set D : ℝ := N k ^ (-u * sH r) with hD
  set a : ℝ := N k ^ (-sH r) with ha
  have hD0 : 0 < D := Real.rpow_pos_of_pos hN0 _
  have ha0 : 0 < a := Real.rpow_pos_of_pos hN0 _
  have hDlow : N k ^ (-(1 / 100 : ℝ)) ≤ D := by
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have hs := hsH r
    nlinarith
  dsimp only [BudgetLayerAt]
  refine ⟨fun i => (hmeas i).inter hGm, ?_, fun i => ?_, ?_⟩
  · intro i i' hii'
    exact (hdisj i i' hii').mono inter_subset_left inter_subset_left
  · obtain ⟨hfl, hsq, hfit, hfloor⟩ := hrow i
    by_cases hne : (AH r i ∩ G).Nonempty
    · simp only [hne, ↓reduceIte]
      refine ⟨fun l hl => hfl l hl.1, ?_, ?_, ?_, ?_⟩
      · obtain ⟨l0, hl0A, hl0G⟩ := hne
        obtain ⟨-, hf0, hf1⟩ := hfl l0 hl0A
        have hb0 : |b k l0 0| ≤ K k := by
          have := hl0G; simp only [hGdef, mem_ofPred_eq] at this
          linarith [abs_nonneg (b k l0 1), abs_nonneg (b k l0 3), abs_nonneg (b k l0 4)]
        have hb1 : |b k l0 1| ≤ K k := by
          have := hl0G; simp only [hGdef, mem_ofPred_eq] at this
          linarith [abs_nonneg (b k l0 0), abs_nonneg (b k l0 3), abs_nonneg (b k l0 4)]
        have hp : |(qH r i 1 : ℝ) * D| ≤ K k + D :=
          (abs_floor_mul_le hD0 hf0).trans (by linarith)
        have hq : |(qH r i 2 : ℝ) * D| ≤ K k + D :=
          (abs_floor_mul_le hD0 hf1).trans (by linarith)
        have hcoef := coef_of_square (h := hH r i) (M := N k ^ ε')
          (p0 := (qH r i 1 : ℝ) * D) (q0 := (qH r i 2 : ℝ) * D) hD0 (by
            intro t ht p hp q hq
            have hp' : p ∈ Icc ((qH r i 1 : ℝ) * D) (((qH r i 1 : ℝ) + 1) * D) := by
              constructor <;> [exact hp.1; linarith [hp.2]]
            have hq' : q ∈ Icc ((qH r i 2 : ℝ) * D) (((qH r i 2 : ℝ) + 1) * D) := by
              constructor <;> [exact hq.1; linarith [hq.2]]
            exact hsq t ht p hp' q hq')
        intro e
        refine (hcoef e).trans ?_
        exact coef_numeric hNk (by linarith) hKk (Real.rpow_nonneg hN0.le _)
          (Real.rpow_le_rpow_of_exponent_le hN1 hε'1) hD0 hDlow hp hq
      · intro t ht p hp q hq
        exact (hsq t ht p hp q hq).trans hpow
      · intro l hl t ht
        exact (hfit l hl.1 t ht).trans (mul_le_mul_of_nonneg_right hpow ha0.le)
      · rw [← hsplit]
        refine le_trans ?_ hfloor
        gcongr
    · simp only [hne, ↓reduceIte]
      have hempty : AH r i ∩ G = ∅ := not_nonempty_iff_eq_empty.mp hne
      refine ⟨fun l hl => absurd ⟨l, hl⟩ hne, fun e => ?_, ?_, fun l hl => absurd ⟨l, hl⟩ hne, ?_⟩
      · simp only [Pi.zero_apply, abs_zero]; exact Real.rpow_nonneg hN0.le _
      · intro t ht p hp q hq
        simp only [Pi.zero_apply, zero_mul, add_zero, abs_zero]
        exact Real.rpow_nonneg hN0.le _
      · have h0 : ρH (AH r i ×ˢ Icc (0 : ℝ) 1) = 0 := by rw [hsplit, hempty]; simp
        rw [h0] at hfloor
        have hpi : π k (Ico ((qH r i 0 : ℝ) * N k ^ (-e₀)) (((qH r i 0 : ℝ) + 1) * N k ^ (-e₀)))
            = 0 := by
          have hpos : ENNReal.ofReal (D ^ 2 * a ^ d / N k ^ ε') ≠ 0 := by
            rw [ENNReal.ofReal_ne_zero_iff]  -- placeholder name
            positivity
          exact (mul_eq_zero.mp (le_antisymm hfloor bot_le)).resolve_left hpos
        rw [hpi, mul_zero]
        exact bot_le
  · refine le_antisymm ?_ bot_le
    calc ρH {p | ∃ i, p.1 ∈ AH r i ∩ G}ᶜ
        ≤ ρH ({p | ∃ i, p.1 ∈ AH r i}ᶜ ∪ Gᶜ ×ˢ univ) := by
          apply measure_mono
          intro p hp
          by_cases hpG : p.1 ∈ G
          · left
            intro ⟨i, hi⟩
            exact hp ⟨i, hi, hpG⟩
          · right; exact ⟨hpG, trivial⟩
      _ ≤ ρH {p | ∃ i, p.1 ∈ AH r i}ᶜ + ρH (Gᶜ ×ˢ univ) := measure_union_le _ _
      _ = 0 := by rw [hcov, hGnull, add_zero]

/-- The frozen per-input conclusion of `Interior` from `LayersAt` at every strict interior rate
on one small buffer `sMax`, with the coefficient exponent `R = 2`. -/
theorem interior_conclusion_of_layers {N K : ℕ → ℝ} (hN2 : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {d κ U e₀ sMax : ℝ} (hs0 : 0 < sMax) (hsU : 2 * sMax < U) (hse : 100 * sMax < e₀)
    (hs1 : sMax ≤ 1 / 100)
    {α : Type} [MeasurableSpace α] {ν : ℕ → Measure α} {μ ρ : ℕ → Measure (α × ℝ)}
    {π : ℕ → Measure ℝ} {b : ℕ → α → Fin 6 → ℝ} {P : ℕ → MvPolynomial (Fin 4) ℝ}
    (h1 : Hyp1 K ν μ ρ π b P)
    (hL : ∀ u : ℝ, 2 * κ < u → u ≤ 1 → LayersAt N d e₀ u sMax ρ π b) :
    ∃ sMax R : ℝ, 0 < sMax ∧ 2 * sMax < U ∧ 100 * sMax < e₀ ∧ 1 < R ∧
      (false = true → sMax = min (U / 4) (e₀ / 200)) ∧
      ∀ u : ℝ, (2 * κ < u ∧ u ≤ 1) → BudgetLayersAt N d e₀ R u sMax ρ π b :=
  ⟨sMax, 2, hs0, hsU, hse, by norm_num, fun h => absurd h (by decide), fun u hu =>
    budget_of_layers hN2 hNt hK hu.2 hs1 h1 (hL u hu.1 hu.2)⟩

/-- `Interior` (the frozen conclusion of o245) from layers at every strict interior rate, on one
buffer `sMax ≤ 1/100` per prepared input; the coefficient budget is recovered with `R = 2`. -/
theorem interior_of_all_layers (H : ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Tendsto N atTop atTop →
    ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε) →
    ∀ d κ ℓ S U e₀ : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < ℓ → 0 < S → S ≤ 1 → 0 < U →
    0 < e₀ → 2 * κ < 1 → ℓ = κ →
    ∀ (α : Type) [MeasurableSpace α] (ν : ℕ → Measure α) (μ ρ : ℕ → Measure (α × ℝ))
      (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) (P : ℕ → MvPolynomial (Fin 4) ℝ)
      (T n : ℕ → ℝ → ℕ) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
      (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α)
      (c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ)
      (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ),
      Hyp1 K ν μ ρ π b P → Hyp2 N K d S μ π b P → Hyp3 N K d κ ℓ U e₀ ν μ π b P T n j A B c F →
      Hyp4 U T n j A → ∃ sMax : ℝ, 0 < sMax ∧ 2 * sMax < U ∧ 100 * sMax < e₀ ∧
        sMax ≤ 1 / 100 ∧ ∀ u : ℝ, 2 * κ < u → u ≤ 1 → LayersAt N d e₀ u sMax ρ π b) :
    Interior := by
  intro N K hN hNt hK d κ ℓ S U e₀ hd0 hd1 hκ0 hκ1 hℓ0 hS0 hS1 hU he₀ hreg hhor α _ ν μ ρ π b P
    T n j A B c F h1 h2 h3 h4
  obtain ⟨sMax, hs0, hsU, hse, hs1, hL⟩ := H N K hN hNt hK d κ ℓ S U e₀ hd0 hd1 hκ0 hκ1 hℓ0 hS0
    hS1 hU he₀ hreg (hhor rfl) α ν μ ρ π b P T n j A B c F h1 h2 h3 h4
  exact interior_conclusion_of_layers hN hNt hK hs0 hsU hse hs1 h1 hL

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap

end
