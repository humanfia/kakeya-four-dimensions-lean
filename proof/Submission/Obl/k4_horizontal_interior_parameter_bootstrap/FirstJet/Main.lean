import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.Asymptotics

/-!
# The first-jet cover from the row fit

`firstJetCover_of_rowFit : RowFitComponent → FirstJetCover`.

At a fixed large `N` (`cover_at_N`): prepare the labels at density `δ = N^(-η)`, take a heavy
block of length `H = 1/⌈N^a⌉`, `a = 64 c/(1 - d)`, fit the first row component on it, restrict
the block's labels to the first fitting set, fit the second component there, and apply
`explicit_cover` with `p₀ = H^(1/8)`, `w' = H^((1-d)/32) ≤ w²`, cell floor
`f = N^(-ε/8) p₀² H^d` and group threshold `μ₀ = N^(-ε/8) H^d`.
-/

open MeasureTheory Set Filter

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

/-- `RowFitComponent` at one `N`. -/
def RowFitAt (d c' c'' η' ε' N : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω), IsProbabilityMeasure ν →
    ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ) (ζ : ℝ),
      0 < ζ → Data ν y β γ E F d (N ^ η') ζ →
    ∀ (H t₀ : ℝ), N ^ (-c'') ≤ H → H ≤ N ^ (-c') → ζ ≤ H ^ 8 → 0 ≤ t₀ → t₀ + H ≤ 1 →
      ENNReal.ofReal (N ^ (-η') * H) ≤ (ν.prod volume) (E ∩ Set.univ ×ˢ Set.Icc t₀ (t₀ + H)) →
      (∀ t ∈ Set.Icc t₀ (t₀ + H), (∃ l, (l, t) ∈ E) →
        ENNReal.ofReal (N ^ (-η')) ≤ timeMass ν E t) →
    ∀ i : Fin 2, ∃ T : Set ℝ, MeasurableSet T ∧ T ⊆ Set.Icc t₀ (t₀ + H) ∧
      (∀ t ∈ T, ∃ l, (l, t) ∈ E) ∧
      ENNReal.ofReal (N ^ (-ε') * H) ≤ volume T ∧
      ∃ a A : ℝ, |A| ≤ N ^ ε' ∧ ∀ t ∈ T, |F t i - (a + (t - t₀) * A)| ≤
        N ^ ε' * H ^ (5 / 4 : ℝ)

/-- Facts about the block length `H = 1/⌈N^a⌉`. -/
theorem blockLen_bounds {N a : ℝ} (hN0 : 0 < N) (hN : 1 ≤ N ^ a) :
    0 < (1 / (⌈N ^ a⌉₊ : ℝ)) ∧ N ^ (-a) / 2 ≤ 1 / (⌈N ^ a⌉₊ : ℝ) ∧
      1 / (⌈N ^ a⌉₊ : ℝ) ≤ N ^ (-a) ∧ 0 < ⌈N ^ a⌉₊ := by
  have h1 : (N ^ a) ≤ (⌈N ^ a⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈N ^ a⌉₊ : ℝ) < N ^ a + 1 := Nat.ceil_lt_add_one (by linarith)
  have hpos : 0 < (⌈N ^ a⌉₊ : ℝ) := by linarith
  have hNa : 0 < N ^ a := by linarith
  rw [Real.rpow_neg hN0.le]
  refine ⟨by positivity, ?_, ?_, by exact_mod_cast hpos⟩
  · rw [div_le_div_iff₀ (by positivity) hpos]
    have : (N ^ a)⁻¹ * (⌈N ^ a⌉₊ : ℝ) ≤ (N ^ a)⁻¹ * (2 * N ^ a) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [show (N ^ a)⁻¹ * (2 * N ^ a) = 2 by field_simp] at this
    linarith
  · rw [one_div]
    exact inv_anti₀ hNa h1

/-- Labels at times of `T`, each time carrying mass `≥ m`, have mass `≥ m |T|`. -/
theorem prod_inter_time_ge {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [SFinite ν]
    {E : Set (Ω × ℝ)} (hE : MeasurableSet E) {T : Set ℝ} (hT : MeasurableSet T) {m : ENNReal}
    (hm : ∀ t ∈ T, m ≤ timeMass ν E t) :
    m * volume T ≤ (ν.prod volume) (E ∩ Set.univ ×ˢ T) := by
  rw [Measure.prod_apply_symm (hE.inter (MeasurableSet.univ.prod hT))]
  calc m * volume T = ∫⁻ t in T, m := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ t in T, timeMass ν E t := setLIntegral_mono (measurable_timeMass hE) hm
    _ = ∫⁻ t, T.indicator (timeMass ν E) t := (lintegral_indicator hT _).symm
    _ ≤ ∫⁻ t, ν ((fun l => (l, t)) ⁻¹' (E ∩ Set.univ ×ˢ T)) := by
        apply lintegral_mono
        intro t
        by_cases ht : t ∈ T
        · rw [Set.indicator_of_mem ht]
          unfold timeMass
          exact measure_mono (fun l hl => ⟨hl, trivial, ht⟩)
        · rw [Set.indicator_of_notMem ht]; exact bot_le

/-- The far-slope numerics of the cover. -/
theorem num_farN {N η ε c d a H : ℝ} (hN0 : 0 < N) (hN1 : 1 ≤ N) (hη : 0 < η) (hd0 : 0 ≤ d)
    (hd1 : d < 1) (ha : a = c * (64 / (1 - d))) (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hHhi : H ≤ N ^ (-a))
    (n9 : 16 * N ^ η * N ^ (ε / 16) * N ^ (-a / 8) ≤ 1)
    (n10 : 5971968 * N ^ (11 * η) * N ^ (-6 * c) ≤ N ^ (-ε / 4)) :
    cnt1 (N ^ η) d (H ^ (1 / 8 : ℝ)) * (2 * (H ^ (1 / 8 : ℝ) +
        2 * (4 * N ^ η * (N ^ (ε / 16) * H ^ (5 / 4 : ℝ)) / H)) / H ^ ((1 - d) / 32)) *
      groupMass (N ^ η) d H ^ 2 < (N ^ (-ε / 8) * H ^ d) ^ 2 / 2 := by
  set K := N ^ η with hKdef
  set p₀ := H ^ (1 / 8 : ℝ) with hp₀def
  set w' := H ^ ((1 - d) / 32) with hw'def
  have hK1 : 1 ≤ K := Real.one_le_rpow hN1 hη.le
  have hp₀0 : 0 < p₀ := Real.rpow_pos_of_pos hH0 _
  have hw'0 : 0 < w' := Real.rpow_pos_of_pos hH0 _
  have hHle : ∀ q : ℝ, 0 ≤ q → H ^ q ≤ N ^ (-a * q) := by
    intro q hq
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow hH0.le hHhi hq
  have hp₀sq : p₀ ^ 2 = H ^ (1 / 4 : ℝ) := by
    rw [hp₀def, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]; congr 1; norm_num
  have hp₀N : p₀ ≤ N ^ (-a / 8) := by
    rw [show -a / 8 = -a * (1 / 8) by ring]; exact hHle _ (by norm_num)
  have he : 4 * K * (N ^ (ε / 16) * H ^ (5 / 4 : ℝ)) / H = 4 * K * N ^ (ε / 16) * p₀ ^ 2 := by
    rw [hp₀sq, show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hH0, Real.rpow_one]
    field_simp
  have hKp₀ : 16 * K * N ^ (ε / 16) * p₀ ≤ 1 := by
    calc 16 * K * N ^ (ε / 16) * p₀ ≤ 16 * N ^ η * N ^ (ε / 16) * N ^ (-a / 8) := by gcongr
      _ ≤ 1 := n9
  have h3p : 2 * (p₀ + 2 * (4 * K * (N ^ (ε / 16) * H ^ (5 / 4 : ℝ)) / H)) ≤ 3 * p₀ := by
    rw [he]
    have hN16 : 0 < N ^ (ε / 16) := Real.rpow_pos_of_pos hN0 _
    have : 4 * K * N ^ (ε / 16) * p₀ ^ 2 ≤ p₀ / 4 := by
      have := mul_le_mul_of_nonneg_right hKp₀ hp₀0.le
      nlinarith
    linarith
  have hcnt := cnt1_le hK1 hd0 hd1 hp₀0
  have hgm := groupMass_le hK1 hd0 hH0 hH1
  have hgm0 : 0 ≤ groupMass K d H := by unfold groupMass; positivity
  have hcnt0 : 0 ≤ cnt1 K d p₀ := by unfold cnt1; positivity
  have hpd : p₀ ^ (-d) * p₀ / w' = H ^ (3 * (1 - d) / 32) := by
    rw [hp₀def, hw'def, ← Real.rpow_mul hH0.le]
    rw [div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hH0 _))]
    conv_lhs => rw [← Real.rpow_one (H ^ (1 / 8 : ℝ))]
    rw [← Real.rpow_mul hH0.le, ← Real.rpow_add hH0, ← Real.rpow_add hH0]
    congr 1; ring
  have hH6c : H ^ (3 * (1 - d) / 32) ≤ N ^ (-6 * c) := by
    refine (hHle _ (by
      have : 0 < 1 - d := by linarith
      positivity)).trans (le_of_eq ?_)
    congr 1; rw [ha]
    have : 1 - d ≠ 0 := by linarith
    field_simp; ring
  have hK11 : K ^ 11 = N ^ (11 * η) := by
    rw [hKdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hHd : 0 < H ^ d := Real.rpow_pos_of_pos hH0 _
  have hμ₀sq : (N ^ (-ε / 8) * H ^ d) ^ 2 = N ^ (-ε / 4) * (H ^ d) ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast (N ^ (-ε / 8)), ← Real.rpow_mul hN0.le]
    congr 2; push_cast; ring
  have step1 : cnt1 K d p₀ * (2 * (p₀ + 2 * (4 * K * (N ^ (ε / 16) * H ^ (5 / 4 : ℝ)) / H)) / w') *
      groupMass K d H ^ 2 ≤ (24 * K ^ 3 * p₀ ^ (-d)) * (3 * p₀ / w') * (144 * K ^ 4 * H ^ d) ^ 2 := by
    gcongr
  have step2 : (24 * K ^ 3 * p₀ ^ (-d)) * (3 * p₀ / w') * (144 * K ^ 4 * H ^ d) ^ 2 =
      1492992 * K ^ 11 * (p₀ ^ (-d) * p₀ / w') * (H ^ d) ^ 2 := by ring
  rw [hK11, hpd] at step2
  have step3 : 1492992 * N ^ (11 * η) * H ^ (3 * (1 - d) / 32) * (H ^ d) ^ 2 ≤
      N ^ (-ε / 4) / 4 * (H ^ d) ^ 2 := by
    have hH2 : 0 ≤ (H ^ d) ^ 2 := by positivity
    have h11 : 0 ≤ N ^ (11 * η) := Real.rpow_nonneg hN0.le _
    calc 1492992 * N ^ (11 * η) * H ^ (3 * (1 - d) / 32) * (H ^ d) ^ 2
        ≤ 1492992 * N ^ (11 * η) * N ^ (-6 * c) * (H ^ d) ^ 2 := by gcongr
      _ ≤ N ^ (-ε / 4) / 4 * (H ^ d) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hH2; linarith
  have hpos : 0 < N ^ (-ε / 4) * (H ^ d) ^ 2 := by positivity
  rw [hμ₀sq]
  linarith [step1, step2, step3]

/-- The slope windows fit in two reading bins. -/
theorem num_rho {N η ε c d a H ζ : ℝ} (hN0 : 0 < N) (hN1 : 1 ≤ N) (hη : 0 < η) (hd1 : d < 1)
    (ha : a = c * (64 / (1 - d))) (hH0 : 0 < H) (hH1 : H ≤ 1) (hHhi : H ≤ N ^ (-a))
    (hζ0 : 0 ≤ ζ) (hζH : ζ ≤ H)
    (n11 : 4 * N ^ (-2 * c) ≤ N ^ (-c))
    (n12a : 128 * N ^ (2 * η) * N ^ (-a / 8) ≤ N ^ (-c))
    (n12b : 32 * N ^ (ε / 16) * N ^ (-a / 8) ≤ N ^ (-c)) :
    2 * (H ^ ((1 - d) / 32) + slopeVar (N ^ η) (N ^ (ε / 16)) H (H ^ (1 / 8 : ℝ)) ζ) ≤
      N ^ (-c) := by
  have hK1 : 1 ≤ N ^ η := Real.one_le_rpow hN1 hη.le
  have hHle : ∀ q : ℝ, 0 ≤ q → H ^ q ≤ N ^ (-a * q) := by
    intro q hq
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow hH0.le hHhi hq
  have hHp₀ : H ≤ H ^ (1 / 8 : ℝ) := by
    calc H = H ^ (1 : ℝ) := (Real.rpow_one H).symm
      _ ≤ H ^ (1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hH0 hH1 (by norm_num)
  have hsv := slopeVar_le hK1 (Real.rpow_nonneg hN0.le (ε / 16)) hζ0 hζH hHp₀
  have hp₀N : H ^ (1 / 8 : ℝ) ≤ N ^ (-a / 8) := by
    rw [show -a / 8 = -a * (1 / 8) by ring]; exact hHle _ (by norm_num)
  have hw' : H ^ ((1 - d) / 32) ≤ N ^ (-2 * c) := by
    refine (hHle _ (by
      have : 0 < 1 - d := by linarith
      positivity)).trans (le_of_eq ?_)
    congr 1; rw [ha]
    have : 1 - d ≠ 0 := by linarith
    field_simp; ring
  have hK2 : (N ^ η) ^ 2 = N ^ (2 * η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hp0 : 0 ≤ H ^ (1 / 8 : ℝ) := Real.rpow_nonneg hH0.le _
  calc 2 * (H ^ ((1 - d) / 32) + slopeVar (N ^ η) (N ^ (ε / 16)) H (H ^ (1 / 8 : ℝ)) ζ)
      ≤ 2 * (N ^ (-2 * c) + (8 * (N ^ η) ^ 2 + 2 * N ^ (ε / 16)) * H ^ (1 / 8 : ℝ)) := by
        gcongr
    _ ≤ 2 * (N ^ (-2 * c) + (8 * N ^ (2 * η) + 2 * N ^ (ε / 16)) * N ^ (-a / 8)) := by
        rw [hK2]; gcongr
    _ ≤ N ^ (-c) := by nlinarith

/-- The dyadic reading width. -/
theorem num_dyadic {N c : ℝ} (hN1 : 1 ≤ N) (hc : 0 < c) :
    (2 : ℝ) ^ (-((⌈Real.logb 2 (N ^ c)⌉₊ : ℕ) : ℤ)) ≤ N ^ (-c) ∧
      N ^ (-c) ≤ 2 * (2 : ℝ) ^ (-((⌈Real.logb 2 (N ^ c)⌉₊ : ℕ) : ℤ)) := by
  have hN0 : 0 < N := by linarith
  set x := N ^ c with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
  have hx1 : 1 ≤ x := Real.one_le_rpow hN1 hc.le
  set n := ⌈Real.logb 2 x⌉₊ with hn
  have hlog0 : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
  have h2n : (2 : ℝ) ^ (-((n : ℕ) : ℤ)) = ((2 : ℝ) ^ (n : ℝ))⁻¹ := by
    rw [zpow_neg, zpow_natCast, Real.rpow_natCast]
  have hxlog : (2 : ℝ) ^ (Real.logb 2 x) = x := Real.rpow_logb (by norm_num) (by norm_num) hx0
  have hNc : N ^ (-c) = x⁻¹ := by rw [hx, Real.rpow_neg hN0.le]
  rw [h2n, hNc]
  constructor
  · apply inv_anti₀ hx0
    rw [← hxlog]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  · have h1 : (n : ℝ) < Real.logb 2 x + 1 := Nat.ceil_lt_add_one hlog0
    have h2 : (2 : ℝ) ^ (n : ℝ) ≤ 2 * x := by
      calc (2 : ℝ) ^ (n : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 x + 1) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
        _ = 2 * x := by rw [Real.rpow_add (by norm_num), hxlog, Real.rpow_one]; ring
    have h3 : 0 < (2 : ℝ) ^ (n : ℝ) := by positivity
    rw [inv_le_comm₀ hx0 (by positivity), mul_inv, inv_inv]
    calc x ≥ (2 : ℝ) ^ (n : ℝ) / 2 := by linarith
      _ = 2⁻¹ * 2 ^ (n : ℝ) := by ring

/-- The mass of the window lines. -/
theorem num_massL {N η ε d H : ℝ} (hN0 : 0 < N) (hN1 : 1 ≤ N) (hη : 0 < η) (hd0 : 0 ≤ d)
    (hd1 : d < 1) (hH0 : 0 < H) (hH1 : H ≤ 1)
    (n14 : 38080 * N ^ (6 * η) * N ^ (-ε / 8) ≤ N ^ (-2 * η) * N ^ (-ε / 16))
    (n15 : 193536 * N ^ (-ε / 4) ≤ N ^ (-3 * ε / 16) * N ^ (-7 * η)) :
    N ^ (-ε / 4) ≤ massL (N ^ η) d H (H ^ (1 / 8 : ℝ))
      (N ^ (-ε / 8) * (H ^ (1 / 8 : ℝ)) ^ 2 * H ^ d) (N ^ (-ε / 8) * H ^ d) (N ^ (-η))
      (N ^ (-(ε / 16)) * H) := by
  set K := N ^ η with hKdef
  set p₀ := H ^ (1 / 8 : ℝ) with hp₀def
  have hK1 : 1 ≤ K := Real.one_le_rpow hN1 hη.le
  have hK0 : 0 < K := by linarith
  have hp₀0 : 0 < p₀ := Real.rpow_pos_of_pos hH0 _
  have hp₀1 : p₀ ≤ 1 := Real.rpow_le_one hH0.le hH1 (by norm_num)
  have hHd : 0 < H ^ d := Real.rpow_pos_of_pos hH0 _
  have hHdi : (1 / H) ^ d * H ^ d = 1 := by
    rw [← Real.mul_rpow (by positivity) hH0.le, one_div, inv_mul_cancel₀ hH0.ne',
      Real.one_rpow]
  set C := cnt1 K d p₀ * cap2 K d H p₀ with hCdef
  have hC : C ≤ 1512 * K ^ 5 * H ^ d * p₀ ^ 2 := cnt1_cap2_le hK1 hd0 hd1 hH0 hH1 hp₀0
  have hC0 : 0 < C := by
    rw [hCdef]; unfold cnt1 cap2
    have : 0 < 4 * K ^ 2 + K + 1 := by positivity
    positivity
  have hN8 : 0 < N ^ (-ε / 8) := Real.rpow_pos_of_pos hN0 _
  have hK5 : K ^ 5 = N ^ (5 * η) := by
    rw [hKdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hK6 : K ^ 6 = N ^ (6 * η) := by
    rw [hKdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  -- the prefactor
  have hpre : N ^ (-ε / 8) / (6048 * N ^ (5 * η)) ≤
      N ^ (-ε / 8) * p₀ ^ 2 * H ^ d / (4 * C) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [← hK5]
    have : 4 * C ≤ 6048 * K ^ 5 * H ^ d * p₀ ^ 2 := by linarith
    calc N ^ (-ε / 8) * (4 * C) ≤ N ^ (-ε / 8) * (6048 * K ^ 5 * H ^ d * p₀ ^ 2) := by gcongr
      _ = N ^ (-ε / 8) * p₀ ^ 2 * H ^ d * (6048 * K ^ 5) := by ring
  -- the bracket
  have hgc := groupCount_le hK1 hd0 hH0 (K := K) (d := d)
  have hsq : (2 * K / p₀ + 2) ^ 2 ≤ 16 * K ^ 2 / p₀ ^ 2 := by
    have : 2 * K / p₀ + 2 ≤ 4 * K / p₀ := by
      rw [div_add' _ _ _ hp₀0.ne', div_le_div_iff_of_pos_right hp₀0]; nlinarith
    calc (2 * K / p₀ + 2) ^ 2 ≤ (4 * K / p₀) ^ 2 := by gcongr
      _ = 16 * K ^ 2 / p₀ ^ 2 := by ring
  have hinner : (2 * K / p₀ + 2) ^ 2 * (N ^ (-ε / 8) * p₀ ^ 2 * H ^ d) + N ^ (-ε / 8) * H ^ d ≤
      17 * K ^ 2 * N ^ (-ε / 8) * H ^ d := by
    have h1 : (2 * K / p₀ + 2) ^ 2 * (N ^ (-ε / 8) * p₀ ^ 2 * H ^ d) ≤
        16 * K ^ 2 / p₀ ^ 2 * (N ^ (-ε / 8) * p₀ ^ 2 * H ^ d) := by gcongr
    have h2 : 16 * K ^ 2 / p₀ ^ 2 * (N ^ (-ε / 8) * p₀ ^ 2 * H ^ d) =
        16 * K ^ 2 * N ^ (-ε / 8) * H ^ d := by field_simp
    have h3 : N ^ (-ε / 8) * H ^ d ≤ K ^ 2 * N ^ (-ε / 8) * H ^ d := by
      have : 1 ≤ K ^ 2 := one_le_pow₀ hK1
      nlinarith [mul_pos hN8 hHd]
    linarith
  have hGC : groupCount K d H * ((2 * K / p₀ + 2) ^ 2 * (N ^ (-ε / 8) * p₀ ^ 2 * H ^ d) +
      N ^ (-ε / 8) * H ^ d) ≤ 1190 * N ^ (6 * η) * N ^ (-ε / 8) := by
    have hgc0 : 0 ≤ groupCount K d H := by
      unfold groupCount
      have : (0 : ℝ) ≤ (1 / H) ^ d := Real.rpow_nonneg (by positivity) _
      positivity
    calc groupCount K d H * ((2 * K / p₀ + 2) ^ 2 * (N ^ (-ε / 8) * p₀ ^ 2 * H ^ d) +
          N ^ (-ε / 8) * H ^ d)
        ≤ 70 * K ^ 4 * (1 / H) ^ d * (17 * K ^ 2 * N ^ (-ε / 8) * H ^ d) := by
          apply mul_le_mul hgc hinner (by positivity) (by positivity)
      _ = 1190 * K ^ 6 * N ^ (-ε / 8) * ((1 / H) ^ d * H ^ d) := by ring
      _ = 1190 * N ^ (6 * η) * N ^ (-ε / 8) := by rw [hHdi, hK6]; ring
  have hmain : (N ^ (-η) / 4) ^ 2 * (N ^ (-(ε / 16)) * H) / H =
      N ^ (-2 * η) * N ^ (-ε / 16) / 16 := by
    have e : N ^ (-2 * η) = (N ^ (-η)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    rw [e, show -(ε / 16) = -ε / 16 by ring]
    field_simp
    ring
  have hbr : N ^ (-2 * η) * N ^ (-ε / 16) / 32 ≤
      (N ^ (-η) / 4) ^ 2 * (N ^ (-(ε / 16)) * H) / H -
        groupCount K d H * ((2 * K / p₀ + 2) ^ 2 * (N ^ (-ε / 8) * p₀ ^ 2 * H ^ d) +
          N ^ (-ε / 8) * H ^ d) := by
    rw [hmain]
    have : 1190 * N ^ (6 * η) * N ^ (-ε / 8) ≤ N ^ (-2 * η) * N ^ (-ε / 16) / 32 := by
      linarith
    linarith
  unfold massL
  have hbr0 : 0 ≤ N ^ (-2 * η) * N ^ (-ε / 16) / 32 := by positivity
  calc N ^ (-ε / 4) ≤ N ^ (-ε / 8) / (6048 * N ^ (5 * η)) * (N ^ (-2 * η) * N ^ (-ε / 16) / 32) := by
        have e1 : N ^ (-ε / 8) / (6048 * N ^ (5 * η)) * (N ^ (-2 * η) * N ^ (-ε / 16) / 32) =
            N ^ (-3 * ε / 16) * N ^ (-7 * η) / 193536 := by
          have e2 : N ^ (-ε / 8) * N ^ (-ε / 16) = N ^ (-3 * ε / 16) := by
            rw [← Real.rpow_add hN0]; congr 1; ring
          have e3 : N ^ (-2 * η) = N ^ (-7 * η) * N ^ (5 * η) := by
            rw [← Real.rpow_add hN0]; congr 1; ring
          rw [e3, ← e2]
          have : 0 < N ^ (5 * η) := Real.rpow_pos_of_pos hN0 _
          field_simp
          ring
        rw [e1]; linarith
    _ ≤ N ^ (-ε / 8) * p₀ ^ 2 * H ^ d / (4 * C) *
        ((N ^ (-η) / 4) ^ 2 * (N ^ (-(ε / 16)) * H) / H -
          groupCount K d H * ((2 * K / p₀ + 2) ^ 2 * (N ^ (-ε / 8) * p₀ ^ 2 * H ^ d) +
            N ^ (-ε / 8) * H ^ d)) := by
        apply mul_le_mul hpre hbr hbr0 (by positivity)

set_option maxHeartbeats 1000000 in
/-- The cover at one large `N`, from the row fits at `N` and explicit power inequalities. -/
theorem cover_at_N {d c ε a η η₁ η₂ ε₁ N : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) (hc : 0 < c)
    (hε : 0 < ε) (ha : a = c * (64 / (1 - d))) (hη : 0 < η) (hε₁ : 0 < ε₁)
    (hε₁' : ε₁ ≤ ε / 16)
    (hRF₁ : RowFitAt d (a / 2) (2 * a) η₁ ε₁ N) (hRF₂ : RowFitAt d (a / 2) (2 * a) η₂ (ε / 16) N)
    (n1 : 2 ≤ N) (n2 : 4 * N ^ η ≤ N ^ η₁) (n3 : 4 * N ^ η ≤ N ^ η₂)
    (n4 : 4 * N ^ η * N ^ ε₁ ≤ N ^ η₂) (n5 : 256 ≤ N ^ a) (n6 : 4 * N ^ (-a) ≤ N ^ (-η))
    (n7 : 12 * N ^ (2 * η) * N ^ (-a) ≤ 1)
    (n8 : 12096 * N ^ (5 * η) * N ^ (-a / 4) ≤ N ^ (-ε / 8))
    (n9 : 16 * N ^ η * N ^ (ε / 16) * N ^ (-a / 8) ≤ 1)
    (n10 : 5971968 * N ^ (11 * η) * N ^ (-6 * c) ≤ N ^ (-ε / 4))
    (n11 : 4 * N ^ (-2 * c) ≤ N ^ (-c))
    (n12a : 128 * N ^ (2 * η) * N ^ (-a / 8) ≤ N ^ (-c))
    (n12b : 32 * N ^ (ε / 16) * N ^ (-a / 8) ≤ N ^ (-c))
    (n13 : 2 * N ^ (-a) ≤ N ^ (-c))
    (n14 : 38080 * N ^ (6 * η) * N ^ (-ε / 8) ≤ N ^ (-2 * η) * N ^ (-ε / 16))
    (n15 : 193536 * N ^ (-ε / 4) ≤ N ^ (-3 * ε / 16) * N ^ (-7 * η))
    (n16 : 8 * N ^ η * N ^ (ε / 4) ≤ N ^ ε)
    (n17 : 125737920 * N ^ (10 * η) * N ^ (ε / 16) * N ^ (ε / 2) ≤ N ^ ε)
    {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} [hν : IsProbabilityMeasure ν]
    {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ}
    (hD : Data ν y β γ E F d (N ^ η) ((N ^ (-c)) ^ (1000 / (1 - d)))) :
    Cover ν y β γ E F d N ε (N ^ (-c)) := by
  classical
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have h1d : 0 < 1 - d := by linarith
  have ha0 : 0 < a := by rw [ha]; positivity
  set K := N ^ η with hKdef
  have hK1 : 1 ≤ K := Real.one_le_rpow hN1 hη.le
  have hK0 : 0 < K := by linarith
  set w := N ^ (-c) with hwdef
  have hw0 : 0 < w := Real.rpow_pos_of_pos hN0 _
  set ζ := w ^ (1000 / (1 - d)) with hζdef
  have hζ0 : 0 < ζ := Real.rpow_pos_of_pos hw0 _
  have hζeq : ζ = N ^ (-(1000 / 64 * a)) := by
    rw [hζdef, hwdef, ← Real.rpow_mul hN0.le, ha]; congr 1; field_simp
  set δ := N ^ (-η) with hδdef
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hN0 _
  have hδK : δ = K⁻¹ := by rw [hδdef, hKdef, Real.rpow_neg hN0.le]
  -- preparation
  set E₂ := prepared ν E δ with hE₂def
  have hE₂m : MeasurableSet E₂ := measurableSet_prepared hD.measurableSet_E δ
  have hE₂E : E₂ ⊆ E := prepared_subset ν E δ
  have hE₂mass : ENNReal.ofReal (δ / 2) ≤ (ν.prod volume) E₂ :=
    prepared_mass hD.measurableSet_E hD.subset_E hδ0.le (by rw [hδK]; exact hD.mass)
  -- powers of `N`
  have hNa : 256 ≤ N ^ a := n5
  have hNa1 : 1 ≤ N ^ a := by linarith
  have hNma : N ^ (-a) ≤ 1 / 256 := by
    rw [Real.rpow_neg hN0.le]; rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hNma0 : 0 < N ^ (-a) := Real.rpow_pos_of_pos hN0 _
  -- the block
  set nH := ⌈N ^ a⌉₊ with hnHdef
  set H : ℝ := 1 / (nH : ℝ) with hHdef
  obtain ⟨hH0, hHlo, hHhi, hnH⟩ := blockLen_bounds hN0 hNa1
  have hH1 : H ≤ 1 := hHhi.trans (by linarith)
  obtain ⟨j, hj, hblock⟩ := exists_heavy_block (fun q hq => hD.subset_E (hE₂E hq)) hnH hE₂mass
  set t₀ : ℝ := (j : ℝ) / nH with ht₀def
  have hnHpos : (0 : ℝ) < nH := by exact_mod_cast hnH
  have ht₀H : ((j : ℝ) + 1) / nH = t₀ + H := by rw [ht₀def, hHdef, add_div]
  have ht₀0 : 0 ≤ t₀ := by positivity
  have ht₀1 : t₀ + H ≤ 1 := by
    rw [← ht₀H, div_le_one hnHpos]
    have : (j : ℝ) + 1 ≤ nH := by exact_mod_cast hj
    linarith
  rw [ht₀H] at hblock
  have hblockR : ENNReal.ofReal (δ * H / 2) ≤
      (ν.prod volume) (E₂ ∩ Set.univ ×ˢ Set.Icc t₀ (t₀ + H)) := by
    have e : δ * H / 2 = (δ / 2) / nH := by rw [hHdef]; ring
    rw [e, ENNReal.ofReal_div_of_pos hnHpos, ENNReal.ofReal_natCast]
    exact hblock
  -- comparisons of the losses
  have hη₁ : N ^ (-η₁) ≤ δ / 4 := by
    rw [hδdef, Real.rpow_neg hN0.le, Real.rpow_neg hN0.le, div_eq_mul_inv]
    have hp1 : 0 < N ^ η := Real.rpow_pos_of_pos hN0 _
    have hp2 : 0 < N ^ η₁ := Real.rpow_pos_of_pos hN0 _
    rw [inv_le_iff_one_le_mul₀ hp2]
    calc (1 : ℝ) = (N ^ η)⁻¹ * 4⁻¹ * (4 * N ^ η) := by field_simp
      _ ≤ (N ^ η)⁻¹ * 4⁻¹ * N ^ η₁ := by gcongr
  have hη₂ : N ^ (-η₂) ≤ δ / 4 := by
    rw [hδdef, Real.rpow_neg hN0.le, Real.rpow_neg hN0.le, div_eq_mul_inv]
    have hp1 : 0 < N ^ η := Real.rpow_pos_of_pos hN0 _
    have hp2 : 0 < N ^ η₂ := Real.rpow_pos_of_pos hN0 _
    rw [inv_le_iff_one_le_mul₀ hp2]
    calc (1 : ℝ) = (N ^ η)⁻¹ * 4⁻¹ * (4 * N ^ η) := by field_simp
      _ ≤ (N ^ η)⁻¹ * 4⁻¹ * N ^ η₂ := by gcongr
  have hKη₁ : K ≤ N ^ η₁ := by linarith
  have hKη₂ : K ≤ N ^ η₂ := by linarith
  -- block parameters for the row fits
  have hHlow : N ^ (-(2 * a)) ≤ H := by
    refine le_trans ?_ hHlo
    rw [show -(2 * a) = -a + -a by ring, Real.rpow_add hN0]
    nlinarith
  have hHup : H ≤ N ^ (-(a / 2)) :=
    hHhi.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hζH8 : ζ ≤ H ^ 8 := by
    have e8 : (N ^ (-a)) ^ (8 : ℕ) = N ^ (-8 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    have h8 : (N ^ (-a) / 2) ^ (8 : ℕ) ≤ H ^ (8 : ℕ) := pow_le_pow_left₀ (by positivity) hHlo 8
    rw [div_pow, e8] at h8
    have e1 : N ^ (-(1000 / 64 * a)) = N ^ (-8 * a) * N ^ (-(488 / 64 * a)) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hb : N ^ (-(488 / 64 * a)) ≤ N ^ (-a) := Real.rpow_le_rpow_of_exponent_le hN1
      (by nlinarith)
    have hc8 : 0 ≤ N ^ (-8 * a) := Real.rpow_nonneg hN0.le _
    rw [hζeq, e1]
    refine le_trans ?_ h8
    have : N ^ (-(488 / 64 * a)) ≤ 1 / 2 ^ 8 := by norm_num; linarith
    calc N ^ (-8 * a) * N ^ (-(488 / 64 * a)) ≤ N ^ (-8 * a) * (1 / 2 ^ 8) := by gcongr
      _ = N ^ (-8 * a) / 2 ^ 8 := by ring
  -- the first row fit
  have hD₂ : Data ν y β γ E₂ F d (N ^ η₁) ζ := hD.mono hKη₁ hζ0 hE₂m hE₂E (by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hE₂mass
    rw [← Real.rpow_neg hN0.le]; linarith)
  have htime₂ : ∀ t ∈ Set.Icc t₀ (t₀ + H), (∃ l, (l, t) ∈ E₂) →
      ENNReal.ofReal (δ / 4) ≤ timeMass ν E₂ t := by
    rintro t - ⟨l, hl⟩
    exact timeMass_of_mem_prepared hl
  obtain ⟨T₀, hT₀m, hT₀sub, hT₀lab, hT₀vol, a₀, A₀, hA₀, hfit₀⟩ := hRF₁ Ω ν hν y β γ E₂ F ζ hζ0
    hD₂ H t₀ hHlow hHup hζH8 ht₀0 ht₀1
    (by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hblockR
      have : N ^ (-η₁) * H ≤ δ / 4 * H := mul_le_mul_of_nonneg_right hη₁ hH0.le
      nlinarith)
    (fun t ht hl => le_trans (ENNReal.ofReal_le_ofReal hη₁) (htime₂ t ht hl)) 0
  -- restrict the block to the first fitting set
  set E₃ := E₂ \ (Set.univ ×ˢ (Set.Icc t₀ (t₀ + H) \ T₀)) with hE₃def
  have hE₃m : MeasurableSet E₃ :=
    hE₂m.diff (MeasurableSet.univ.prod (measurableSet_Icc.diff hT₀m))
  have hE₃E₂ : E₃ ⊆ E₂ := Set.diff_subset
  have hHδ : H ≤ δ / 4 := by
    have : 4 * H ≤ δ := le_trans (by linarith) n6
    linarith
  have hE₃mass : ENNReal.ofReal (δ / 4) ≤ (ν.prod volume) E₃ := by
    have hcov : E₂ ⊆ E₃ ∪ Set.univ ×ˢ Set.Icc t₀ (t₀ + H) := by
      intro q hq
      by_cases h : q ∈ Set.univ ×ˢ (Set.Icc t₀ (t₀ + H) \ T₀)
      · right; exact ⟨trivial, h.2.1⟩
      · left; exact ⟨hq, h⟩
    have h1 : (ν.prod volume) (Set.univ ×ˢ Set.Icc t₀ (t₀ + H)) = ENNReal.ofReal H := by
      rw [Measure.prod_prod, measure_univ, one_mul, Real.volume_Icc]; ring_nf
    have h2 := hE₂mass.trans ((measure_mono hcov).trans (measure_union_le _ _))
    rw [h1] at h2
    have h3 : ENNReal.ofReal (δ / 2) = ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    rw [h3] at h2
    have h4 : ENNReal.ofReal H ≤ ENNReal.ofReal (δ / 4) := ENNReal.ofReal_le_ofReal hHδ
    have h5 := h2.trans (add_le_add le_rfl h4)
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h5
  have hD₃ : Data ν y β γ E₃ F d (N ^ η₂) ζ := hD.mono hKη₂ hζ0 hE₃m (hE₃E₂.trans hE₂E) (by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hE₃mass
    rw [← Real.rpow_neg hN0.le]; exact hη₂)
  -- labeled times of the restricted block lie in `T₀`
  have hE₃time : ∀ t ∈ Set.Icc t₀ (t₀ + H), ∀ l, (l, t) ∈ E₃ → t ∈ T₀ := by
    intro t ht l hl
    by_contra hT
    exact hl.2 ⟨trivial, ht, hT⟩
  have hE₃slice : ∀ t ∈ T₀, timeMass ν E₃ t = timeMass ν E₂ t := by
    intro t ht
    unfold timeMass
    congr 1; ext l
    simp only [Set.mem_ofPred_eq, hE₃def, Set.mem_diff, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_diff, not_and, not_not]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun _ => ht⟩
  have hblock₃ : ENNReal.ofReal (N ^ (-η₂) * H) ≤
      (ν.prod volume) (E₃ ∩ Set.univ ×ˢ Set.Icc t₀ (t₀ + H)) := by
    have hsub : E₂ ∩ Set.univ ×ˢ T₀ ⊆ E₃ ∩ Set.univ ×ˢ Set.Icc t₀ (t₀ + H) := by
      rintro q ⟨hq, -, hqT⟩
      exact ⟨⟨hq, fun h => h.2.2 hqT⟩, trivial, hT₀sub hqT⟩
    refine le_trans ?_ (measure_mono hsub)
    refine le_trans ?_ (prod_inter_time_ge hE₂m hT₀m (m := ENNReal.ofReal (δ / 4))
      (fun t ht => by obtain ⟨l, hl⟩ := hT₀lab t ht; exact timeMass_of_mem_prepared hl))
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hT₀vol bot_le)
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    -- `N^(-η₂) ≤ (δ/4) N^(-ε₁)`
    have h1 : N ^ (-η₂) ≤ δ / 4 * N ^ (-ε₁) := by
      rw [hδdef, Real.rpow_neg hN0.le, Real.rpow_neg hN0.le, Real.rpow_neg hN0.le]
      have hp1 : 0 < N ^ η := Real.rpow_pos_of_pos hN0 _
      have hp2 : 0 < N ^ η₂ := Real.rpow_pos_of_pos hN0 _
      have hp3 : 0 < N ^ ε₁ := Real.rpow_pos_of_pos hN0 _
      rw [inv_le_iff_one_le_mul₀ hp2]
      calc (1 : ℝ) = (N ^ η)⁻¹ / 4 * (N ^ ε₁)⁻¹ * (4 * N ^ η * N ^ ε₁) := by field_simp
        _ ≤ (N ^ η)⁻¹ / 4 * (N ^ ε₁)⁻¹ * N ^ η₂ := by gcongr
    calc N ^ (-η₂) * H ≤ δ / 4 * N ^ (-ε₁) * H := mul_le_mul_of_nonneg_right h1 hH0.le
      _ = δ / 4 * (N ^ (-ε₁) * H) := by ring
  -- the second row fit
  obtain ⟨T₁, hT₁m, hT₁sub, hT₁lab, hT₁vol, a₁, A₁, hA₁, hfit₁⟩ := hRF₂ Ω ν hν y β γ E₃ F ζ hζ0
    hD₃ H t₀ hHlow hHup hζH8 ht₀0 ht₀1 hblock₃
    (by
      rintro t ht ⟨l, hl⟩
      have htT₀ := hE₃time t ht l hl
      rw [hE₃slice t htT₀]
      exact le_trans (ENNReal.ofReal_le_ofReal hη₂) (timeMass_of_mem_prepared (hE₃E₂ hl)))
    1
  have hT₁T₀ : T₁ ⊆ T₀ := by
    intro t ht
    obtain ⟨l, hl⟩ := hT₁lab t ht
    exact hE₃time t (hT₁sub ht) l hl
  -- the affine row on `T₁`
  set A : Fin 2 → ℝ := ![A₀, A₁] with hAdef
  set a' : Fin 2 → ℝ := ![a₀, a₁] with ha'def
  set KA : ℝ := N ^ (ε / 16) with hKAdef
  set Efit : ℝ := N ^ (ε / 16) * H ^ (5 / 4 : ℝ) with hEfitdef
  have hε₁N : N ^ ε₁ ≤ KA := Real.rpow_le_rpow_of_exponent_le hN1 hε₁'
  have hfit : ∀ t ∈ T₁, ∀ i, |F t i - (a' i + (t - t₀) * A i)| ≤ Efit := by
    intro t ht i
    fin_cases i
    · refine (hfit₀ t (hT₁T₀ ht)).trans ?_
      exact mul_le_mul_of_nonneg_right hε₁N (Real.rpow_nonneg hH0.le _)
    · exact hfit₁ t ht
  have hA : ∀ i, |A i| ≤ KA := by
    intro i
    fin_cases i
    · exact hA₀.trans hε₁N
    · exact hA₁
  have hKA0 : 0 ≤ KA := Real.rpow_nonneg hN0.le _
  have hEfit0 : 0 ≤ Efit := by positivity
  -- the scales
  set p₀ : ℝ := H ^ (1 / 8 : ℝ) with hp₀def
  set w' : ℝ := H ^ ((1 - d) / 32) with hw'def
  set f : ℝ := N ^ (-ε / 8) * p₀ ^ 2 * H ^ d with hfdef
  set μ₀ : ℝ := N ^ (-ε / 8) * H ^ d with hμ₀def
  set lam : ℝ := N ^ (-(ε / 16)) * H with hlamdef
  set n : ℕ := ⌈Real.logb 2 (N ^ c)⌉₊ with hndef
  have hp₀0 : 0 < p₀ := Real.rpow_pos_of_pos hH0 _
  have hp₀1 : p₀ ≤ 1 := Real.rpow_le_one hH0.le hH1 (by norm_num)
  have hHp₀ : H ≤ p₀ := by
    calc H = H ^ (1 : ℝ) := (Real.rpow_one H).symm
      _ ≤ H ^ (1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hH0 hH1 (by norm_num)
  have hH8H : H ^ 8 ≤ H := by
    calc H ^ 8 ≤ H ^ 1 := pow_le_pow_of_le_one hH0.le hH1 (by norm_num)
      _ = H := pow_one H
  have hζH : ζ ≤ H := hζH8.trans hH8H
  have hζq : ζ ≤ H * p₀ := by
    refine hζH8.trans ?_
    calc H ^ 8 ≤ H ^ 2 := pow_le_pow_of_le_one hH0.le hH1 (by norm_num)
      _ = H * H := sq H
      _ ≤ H * p₀ := mul_le_mul_of_nonneg_left hHp₀ hH0.le
  -- powers
  have hKpow : ∀ m : ℕ, K ^ m = N ^ ((m : ℝ) * η) := by
    intro m
    rw [hKdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, mul_comm]
  have hHle : ∀ q : ℝ, 0 ≤ q → H ^ q ≤ N ^ (-a * q) := by
    intro q hq
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow hH0.le hHhi hq
  have hHd0 : 0 < H ^ d := Real.rpow_pos_of_pos hH0 _
  have hp₀sq : p₀ ^ 2 = H ^ (1 / 4 : ℝ) := by
    rw [hp₀def, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]; congr 1; norm_num
  have hp₀N : p₀ ≤ N ^ (-a / 8) := by
    rw [show -a / 8 = -a * (1 / 8) by ring]; exact hHle _ (by norm_num)
  have hnum_r1 : 2 * (4 * K ^ 2 + K + 1) * H ≤ 1 := by
    have h1 : 4 * K ^ 2 + K + 1 ≤ 6 * K ^ 2 := by nlinarith
    have h2 : K ^ 2 = N ^ (2 * η) := by rw [hKpow 2]; norm_num
    have h3 : H ≤ N ^ (-a) := hHhi
    calc 2 * (4 * K ^ 2 + K + 1) * H ≤ 2 * (6 * K ^ 2) * H := by gcongr
      _ = 12 * N ^ (2 * η) * H := by rw [h2]; ring
      _ ≤ 12 * N ^ (2 * η) * N ^ (-a) := by gcongr
      _ ≤ 1 := n7
  have hbig : 8 * (cnt1 K d p₀ * cap2 K d H p₀) ≤ μ₀ := by
    have h1 := cnt1_cap2_le hK1 hd0 hd1 hH0 hH1 hp₀0
    have h2 : K ^ 5 = N ^ (5 * η) := by rw [hKpow 5]; norm_num
    have h3 : p₀ ^ 2 ≤ N ^ (-a / 4) := by
      rw [hp₀sq, show -a / 4 = -a * (1 / 4) by ring]; exact hHle _ (by norm_num)
    calc 8 * (cnt1 K d p₀ * cap2 K d H p₀) ≤ 8 * (1512 * K ^ 5 * H ^ d * p₀ ^ 2) := by gcongr
      _ = 12096 * N ^ (5 * η) * p₀ ^ 2 * H ^ d := by rw [h2]; ring
      _ ≤ 12096 * N ^ (5 * η) * N ^ (-a / 4) * H ^ d := by gcongr
      _ ≤ N ^ (-ε / 8) * H ^ d := by gcongr
      _ = μ₀ := by rw [hμ₀def]
  have hfarN : cnt1 K d p₀ * (2 * (p₀ + 2 * (4 * K * Efit / H)) / w') * groupMass K d H ^ 2 <
      μ₀ ^ 2 / 2 := num_farN hN0 hN1 hη hd0 hd1 ha hH0 hH1 hHhi n9 n10
  have hρ : 2 * (w' + slopeVar K KA H p₀ ζ) ≤ w :=
    num_rho hN0 hN1 hη hd1 ha hH0 hH1 hHhi hζ0.le hζH n11 n12a n12b
  obtain ⟨hrw, hwr⟩ := num_dyadic hN1 hc
  have hmL : N ^ (-ε / 4) ≤ massL K d H p₀ f μ₀ δ lam :=
    num_massL hN0 hN1 hη hd0 hd1 hH0 hH1 n14 n15
  have hmL0 : 0 < massL K d H p₀ f μ₀ δ lam := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hmL
  have hHw : H ≤ w := by
    have : 0 < N ^ (-a) := hNma0
    linarith
  have hw1 : w ≤ 1 := rpow_neg_le_one hN1 hc.le
  have hHr : H ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
    have : 0 < N ^ (-a) := hNma0
    linarith
  have hT₁01 : T₁ ⊆ Set.Icc 0 1 := by
    intro t ht
    have := hT₁sub ht
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have htime : ∀ t ∈ T₁, ENNReal.ofReal (δ / 4) ≤ timeMass ν E₂ t := by
    intro t ht
    obtain ⟨l, hl⟩ := hT₁lab t ht
    exact timeMass_of_mem_prepared (hE₃E₂ hl)
  have hf0 : 0 < f := by positivity
  have hμ₀0 : 0 < μ₀ := by positivity
  have hw'0 : 0 < w' := Real.rpow_pos_of_pos hH0 _
  have hlam0 : 0 < lam := by positivity
  obtain ⟨ts, hts, L₁, hL₁m, hL₁mass, P, hP, hPmem⟩ := explicit_cover hD hK1 hd0 hζ0.le hδ0 hE₂m
    hE₂E (fun q hq => duration_of_mem_prepared hq) hH0 hH1 hζH hT₁m hT₁sub hT₁01 htime hlam0
    hT₁vol hEfit0 hKA0 hfit hA hp₀0 hp₀1 hζq hnum_r1 hf0 hμ₀0 hw'0 hbig hfarN hHw hw1 hrw hwr
    hHr hρ hmL0
  refine ⟨ts, hts, A, fun i => (hA i).trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)),
    L₁, hL₁m, le_trans (ENNReal.ofReal_le_ofReal ?_) hL₁mass, P, hP.trans ?_, fun l hl => hPmem l hl⟩
  · -- the mass
    have hNη : 0 < N ^ η := Real.rpow_pos_of_pos hN0 _
    have hNε4 : 0 < N ^ (ε / 4) := Real.rpow_pos_of_pos hN0 _
    have hNε : 0 < N ^ ε := Real.rpow_pos_of_pos hN0 _
    have e1 : N ^ (-ε) = (N ^ ε)⁻¹ := Real.rpow_neg hN0.le _
    have e2 : δ = (N ^ η)⁻¹ := Real.rpow_neg hN0.le _
    have e3 : N ^ (-ε / 4) = (N ^ (ε / 4))⁻¹ := by
      rw [show -ε / 4 = -(ε / 4) by ring]; exact Real.rpow_neg hN0.le _
    calc N ^ (-ε) = (N ^ ε)⁻¹ := e1
      _ ≤ (8 * N ^ η * N ^ (ε / 4))⁻¹ := by
          apply inv_anti₀ (by positivity) n16
      _ = δ / 4 * (N ^ (-ε / 4) / 2) := by rw [e2, e3]; field_simp; ring
      _ ≤ δ / 4 * (massL K d H p₀ f μ₀ δ lam / 2) := by gcongr
  · -- the count
    have hb := pairBound_le hK1 hKA0 hd0 hd1 hw0 hmL0
    have hK10 : K ^ 10 = N ^ (10 * η) := by rw [hKpow 10]; norm_num
    have hKA1 : 1 ≤ KA := Real.one_le_rpow hN1 (by positivity)
    have hwd : (1 / w) ^ d = w ^ (-d) := by
      rw [one_div, Real.inv_rpow hw0.le, Real.rpow_neg hw0.le]
    have hwd0 : 0 ≤ w ^ (-d) := Real.rpow_nonneg hw0.le _
    have hmL2 : 1 / massL K d H p₀ f μ₀ δ lam ^ 2 ≤ N ^ (ε / 2) := by
      have hNe : 0 < N ^ (-ε / 4) := Real.rpow_pos_of_pos hN0 _
      have e4 : N ^ (ε / 2) = 1 / (N ^ (-ε / 4)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, one_div, ← Real.rpow_neg hN0.le]
        congr 1; push_cast; ring
      rw [e4]
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ hNe.le hmL 2
    rw [hwd] at hb
    calc pairBound K KA d w (massL K d H p₀ f μ₀ δ lam)
        ≤ 13970880 * K ^ 10 * (4 * KA + 5) / massL K d H p₀ f μ₀ δ lam ^ 2 * w ^ (-d) := hb
      _ = 13970880 * K ^ 10 * (4 * KA + 5) * (1 / massL K d H p₀ f μ₀ δ lam ^ 2) * w ^ (-d) := by
          ring
      _ ≤ 13970880 * N ^ (10 * η) * (9 * KA) * N ^ (ε / 2) * w ^ (-d) := by
          rw [hK10]; gcongr; linarith
      _ = 125737920 * N ^ (10 * η) * N ^ (ε / 16) * N ^ (ε / 2) * w ^ (-d) := by
          rw [hKAdef]; ring
      _ ≤ N ^ ε * w ^ (-d) := by gcongr

theorem ev_rpow2 (C x y β : ℝ) (h : x + y < β) :
    ∀ᶠ N : ℝ in atTop, C * N ^ x * N ^ y ≤ N ^ β := by
  filter_upwards [ev_rpow C (x + y) β h, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  have e : C * N ^ x * N ^ y = C * N ^ (x + y) := by rw [Real.rpow_add hN0]; ring
  rw [e]; exact hN

theorem ev_rpow3 (C x y z β : ℝ) (h : x + y + z < β) :
    ∀ᶠ N : ℝ in atTop, C * N ^ x * N ^ y * N ^ z ≤ N ^ β := by
  filter_upwards [ev_rpow C (x + y + z) β h, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  have e : C * N ^ x * N ^ y * N ^ z = C * N ^ (x + y + z) := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0]; ring
  rw [e]; exact hN

theorem ev_rpow1r (C x u v : ℝ) (h : x < u + v) :
    ∀ᶠ N : ℝ in atTop, C * N ^ x ≤ N ^ u * N ^ v := by
  filter_upwards [ev_rpow C x (u + v) h, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  rw [← Real.rpow_add hN0]; exact hN

theorem ev_rpow2r (C x y u v : ℝ) (h : x + y < u + v) :
    ∀ᶠ N : ℝ in atTop, C * N ^ x * N ^ y ≤ N ^ u * N ^ v := by
  filter_upwards [ev_rpow2 C x y (u + v) h, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  rw [← Real.rpow_add hN0]; exact hN

/-- **The first-jet cover from the row fit.** -/
theorem firstJetCover_of_rowFit (hRF : RowFitComponent) : FirstJetCover := by
  intro d hd0 hd1 c hc ε₀ hε₀
  set ε := min ε₀ c with hεdef
  have hε : 0 < ε := lt_min hε₀ hc
  have hεc : ε ≤ c := min_le_right _ _
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have h1d : 0 < 1 - d := by linarith
  set a := c * (64 / (1 - d)) with ha
  have ha0 : 0 < a := by positivity
  have hac : 64 * c ≤ a := by
    have : 64 ≤ 64 / (1 - d) := by
      rw [le_div_iff₀ h1d]; nlinarith
    rw [ha]; nlinarith
  obtain ⟨η₂, hη₂, N₂, -, hRF₂⟩ := hRF d hd0 hd1 (a / 2) (2 * a) (by positivity) (by linarith)
    (ε / 16) (by positivity)
  set ε₁ := min (ε / 16) (η₂ / 4) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min (by positivity) (by positivity)
  have hε₁a : ε₁ ≤ ε / 16 := min_le_left _ _
  have hε₁b : ε₁ ≤ η₂ / 4 := min_le_right _ _
  obtain ⟨η₁, hη₁, N₁, -, hRF₁⟩ := hRF d hd0 hd1 (a / 2) (2 * a) (by positivity) (by linarith)
    ε₁ hε₁
  set η := min (min η₁ η₂) ε / 1000 with hηdef
  have hm0 : 0 < min (min η₁ η₂) ε := lt_min (lt_min hη₁ hη₂) hε
  have hη : 0 < η := div_pos hm0 (by norm_num)
  have hηη₁ : η ≤ η₁ / 1000 := by
    have : min (min η₁ η₂) ε ≤ η₁ := (min_le_left _ _).trans (min_le_left _ _)
    rw [hηdef]; linarith
  have hηη₂ : η ≤ η₂ / 1000 := by
    have : min (min η₁ η₂) ε ≤ η₂ := (min_le_left _ _).trans (min_le_right _ _)
    rw [hηdef]; linarith
  have hηε : η ≤ ε / 1000 := by
    have : min (min η₁ η₂) ε ≤ ε := min_le_right _ _
    rw [hηdef]; linarith
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
    ((eventually_ge_atTop (2 : ℝ)).and <|
     (ev_rpow 4 η η₁ (by linarith)).and <|
     (ev_rpow 4 η η₂ (by linarith)).and <|
     (ev_rpow2 4 η ε₁ η₂ (by linarith)).and <|
     (ev_rpow 256 0 a ha0).and <|
     (ev_rpow 4 (-a) (-η) (by linarith)).and <|
     (ev_rpow2 12 (2 * η) (-a) 0 (by linarith)).and <|
     (ev_rpow2 12096 (5 * η) (-a / 4) (-ε / 8) (by linarith)).and <|
     (ev_rpow3 16 η (ε / 16) (-a / 8) 0 (by linarith)).and <|
     (ev_rpow2 5971968 (11 * η) (-6 * c) (-ε / 4) (by linarith)).and <|
     (ev_rpow 4 (-2 * c) (-c) (by linarith)).and <|
     (ev_rpow2 128 (2 * η) (-a / 8) (-c) (by linarith)).and <|
     (ev_rpow2 32 (ε / 16) (-a / 8) (-c) (by linarith)).and <|
     (ev_rpow 2 (-a) (-c) (by linarith)).and <|
     (ev_rpow2r 38080 (6 * η) (-ε / 8) (-2 * η) (-ε / 16) (by linarith)).and <|
     (ev_rpow1r 193536 (-ε / 4) (-3 * ε / 16) (-7 * η) (by linarith)).and <|
     (ev_rpow2 8 η (ε / 4) ε (by linarith)).and <|
     (ev_rpow3 125737920 (10 * η) (ε / 16) (ε / 2) ε (by linarith)))
  refine ⟨η, hη, max (max N₁ N₂) (max N₃ 2), le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro N hN Ω _ ν hν y β γ E F hD
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₃' : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12a, n12b, n13, n14, n15, n16, n17⟩ :=
    hN₃ N hN₃'
  rw [Real.rpow_zero, mul_one] at n5
  rw [Real.rpow_zero] at n7 n9
  have hcov := cover_at_N hd0 hd1 hc hε ha hη hε₁ hε₁a (hRF₁ N hN₁') (hRF₂ N hN₂') n1 n2 n3 n4
    n5 n6 n7 n8 n9 n10 n11 n12a n12b n13 n14 n15 n16 n17 hD
  exact Cover.mono (by linarith) hεε₀
    (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _) hcov

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
