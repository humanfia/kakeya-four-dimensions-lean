import Mathlib
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.TrueSystem

/-!
# Asymptotic choice of the conversion parameters

Along an exact sequence with `N_k → ∞` and subpower `K_k`, the explicit inequalities of the
single-sample conversion hold eventually for a suitable choice of the velocity depth `u`, the
density tolerances and the slack exponent `κ`. Consequently true terminal systems of every
horizon and every slack exponent, at arbitrarily late samples, give the frozen packet output.
-/

namespace Submission.Obl.k4_scalar_terminal_chart_packet_extraction

open MeasureTheory Set Filter
open scoped ENNReal

lemma eventually_const_le_rpow {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) (C : ℝ) {e : ℝ}
    (he : 0 < e) : ∀ᶠ k in atTop, C ≤ N k ^ e :=
  ((tendsto_rpow_atTop he).comp hN).eventually_ge_atTop C

/-! ### The explicit inequalities -/

lemma rpow_three_mul {N κ : ℝ} (hN : 0 < N) : (N ^ κ) ^ 3 = N ^ (3 * κ) := by
  rw [mul_comm, Real.rpow_mul hN.le, ← Real.rpow_natCast]; norm_num

lemma cond_P1 {N κ a fL : ℝ} (hN : 1 ≤ N) (hκ : 0 ≤ κ) (h80 : 80 ≤ N ^ (a - 3 * κ)) :
    16 * (N ^ κ) ^ 2 * (2 * N ^ κ + 3) * N ^ (-fL - a) ≤ N ^ (-fL) := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have hΛ : 1 ≤ N ^ κ := Real.one_le_rpow hN hκ
  have h1 : 16 * (N ^ κ) ^ 2 * (2 * N ^ κ + 3) ≤ 80 * (N ^ κ) ^ 3 := by nlinarith
  have h2 : 80 * (N ^ κ) ^ 3 ≤ N ^ a := by
    rw [rpow_three_mul hN0]
    calc 80 * N ^ (3 * κ) ≤ N ^ (a - 3 * κ) * N ^ (3 * κ) := by gcongr
      _ = N ^ a := by rw [← Real.rpow_add hN0]; ring_nf
  have h3 : N ^ a * N ^ (-fL - a) = N ^ (-fL) := by rw [← Real.rpow_add hN0]; ring_nf
  calc 16 * (N ^ κ) ^ 2 * (2 * N ^ κ + 3) * N ^ (-fL - a)
      ≤ N ^ a * N ^ (-fL - a) := by gcongr; exact h1.trans h2
    _ = N ^ (-fL) := h3

lemma cond_P2 {N κ ε u h : ℝ} (hN : 1 ≤ N) (h4 : 4 ≤ N ^ (ε - u - h - 2 * κ)) :
    4 * (N ^ κ) ^ 2 * N ^ (-ε) ≤ N ^ (-u) * N ^ (-h) := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have e1 : (N ^ κ) ^ 2 = N ^ (2 * κ) := by
    rw [mul_comm, Real.rpow_mul hN0.le, ← Real.rpow_natCast]; norm_num
  rw [e1]
  calc 4 * N ^ (2 * κ) * N ^ (-ε) ≤ N ^ (ε - u - h - 2 * κ) * N ^ (2 * κ) * N ^ (-ε) := by
        gcongr
    _ = N ^ (-u) * N ^ (-h) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf

lemma cond_P4 {N κ ε u h τL L K : ℝ} (hN : 1 ≤ N) (hκ : 0 ≤ κ) (hu : 0 ≤ u) (hh : 0 ≤ h)
    (hL : 0 ≤ L) (hK1 : 1 ≤ K) (hK : K ≤ N ^ κ)
    (hC : 186624 * 4 * 256 * 160000 ≤ N ^ (ε - (15 * κ + 2 * h + 2 * u + 4 * τL))) :
    186624 * (3 * K + N ^ κ * N ^ (-L)) * (4 + (1 + 2 * K) * (4 * N ^ h / N ^ (-u))) ^ 2 /
      (N ^ (-τL) / (4 * (N ^ κ) ^ 2 * (2 * N ^ κ + 3))) ^ 4 ≤ N ^ ε := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  set Λ := N ^ κ with hΛdef
  have hΛ : 1 ≤ Λ := Real.one_le_rpow hN hκ
  set H := N ^ (h + u) with hHdef
  have hH : 1 ≤ H := Real.one_le_rpow hN (by linarith)
  have hNL : N ^ (-L) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hNL0 : 0 ≤ N ^ (-L) := (Real.rpow_pos_of_pos hN0 _).le
  set R := N ^ τL with hRdef
  have hR0 : 0 < R := Real.rpow_pos_of_pos hN0 _
  have hRinv : N ^ (-τL) = R⁻¹ := Real.rpow_neg hN0.le τL
  -- the three factors
  have f1 : 3 * K + Λ * N ^ (-L) ≤ 4 * Λ := by nlinarith
  have hdiv : 4 * N ^ h / N ^ (-u) = 4 * H := by
    rw [hHdef, Real.rpow_add hN0, Real.rpow_neg hN0.le]; field_simp
  have f2 : 4 + (1 + 2 * K) * (4 * N ^ h / N ^ (-u)) ≤ 16 * Λ * H := by
    rw [hdiv]; nlinarith
  have hD : 0 < 4 * Λ ^ 2 * (2 * Λ + 3) := by positivity
  have f3 : (N ^ (-τL) / (4 * Λ ^ 2 * (2 * Λ + 3))) ^ 4 ≥ (R⁻¹ / (20 * Λ ^ 3)) ^ 4 := by
    rw [hRinv]
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_left (by positivity) hD
    nlinarith
  have hlam0 : 0 < (R⁻¹ / (20 * Λ ^ 3)) ^ 4 := by positivity
  have hA0 : 0 ≤ 3 * K + Λ * N ^ (-L) := by positivity
  have hB0 : 0 ≤ 4 + (1 + 2 * K) * (4 * N ^ h / N ^ (-u)) := by
    rw [hdiv]; positivity
  calc 186624 * (3 * K + Λ * N ^ (-L)) * (4 + (1 + 2 * K) * (4 * N ^ h / N ^ (-u))) ^ 2 /
        (N ^ (-τL) / (4 * Λ ^ 2 * (2 * Λ + 3))) ^ 4
      ≤ 186624 * (4 * Λ) * (16 * Λ * H) ^ 2 / (R⁻¹ / (20 * Λ ^ 3)) ^ 4 := by
        gcongr
    _ = (186624 * 4 * 256 * 160000) * (Λ ^ 15 * H ^ 2 * R ^ 4) := by
        field_simp
        ring
    _ ≤ N ^ (ε - (15 * κ + 2 * h + 2 * u + 4 * τL)) * (Λ ^ 15 * H ^ 2 * R ^ 4) := by
        gcongr
    _ = N ^ ε := by
        have e1 : Λ ^ 15 = N ^ (15 * κ) := by
          rw [hΛdef, mul_comm, Real.rpow_mul hN0.le, ← Real.rpow_natCast]; norm_num
        have e2 : H ^ 2 = N ^ (2 * h + 2 * u) := by
          rw [hHdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
        have e3 : R ^ 4 = N ^ (4 * τL) := by
          rw [hRdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
        rw [e1, e2, e3, ← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
        ring_nf

lemma rpow_neg_le_div_five {N a b : ℝ} (hN : 0 < N) (h5 : 5 ≤ N ^ (a - b)) :
    N ^ (-a) ≤ N ^ (-b) / 5 := by
  have : N ^ (-b) = N ^ (-a) * N ^ (a - b) := by rw [← Real.rpow_add hN]; ring_nf
  rw [this, le_div_iff₀ (by norm_num)]
  have h0 : 0 ≤ N ^ (-a) := (Real.rpow_pos_of_pos hN _).le
  nlinarith

lemma cond_P5 {N κ ε cG cL : ℝ} (hN : 0 < N) {XG XL : ℝ≥0∞}
    (hXG : XG ≤ ENNReal.ofReal (N ^ (-cG))) (hXL : XL ≤ ENNReal.ofReal (N ^ (-cL)))
    (h5ε : 5 ≤ N ^ (ε - κ)) (h5G : 5 ≤ N ^ (cG - κ)) (h5L : 5 ≤ N ^ (cL - κ)) :
    ENNReal.ofReal (N ^ (-ε)) + (2 * XG + 2 * XL) ≤ ENNReal.ofReal (N ^ κ)⁻¹ := by
  have e1 := rpow_neg_le_div_five hN h5ε
  have e2 := rpow_neg_le_div_five hN h5G
  have e3 := rpow_neg_le_div_five hN h5L
  have hk : (N ^ κ)⁻¹ = N ^ (-κ) := (Real.rpow_neg hN.le κ).symm
  have h0 : ∀ x : ℝ, 0 ≤ N ^ x := fun x => (Real.rpow_pos_of_pos hN x).le
  calc ENNReal.ofReal (N ^ (-ε)) + (2 * XG + 2 * XL)
      ≤ ENNReal.ofReal (N ^ (-ε)) + (2 * ENNReal.ofReal (N ^ (-cG)) +
          2 * ENNReal.ofReal (N ^ (-cL))) := by gcongr
    _ = ENNReal.ofReal (N ^ (-ε) + (2 * N ^ (-cG) + 2 * N ^ (-cL))) := by
        rw [ENNReal.ofReal_add (h0 _) (by positivity), ENNReal.ofReal_add (by positivity)
          (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal (N ^ κ)⁻¹ := by
        apply ENNReal.ofReal_le_ofReal
        rw [hk]
        linarith

/-! ### The asymptotic conversion -/

/-- **True systems of every horizon give the frozen packets.** Along an exact sequence, if
for every horizon `h` and slack exponent `κ` there are true terminal systems with slack
`N_k^κ` at arbitrarily late samples, then for every `h, ε` there are frozen packets at
arbitrarily late samples. -/
theorem packets_of_trueSystems
    (N K : ℕ → ℝ) (hN2 : ∀ k, 2 ≤ N k) (hNtop : Tendsto N atTop atTop)
    (hK1 : ∀ k, 1 ≤ K k) (hKsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {L fL S U : ℝ} (hL : 0 ≤ L) (hS : 0 < S) (hU : 0 < U)
    (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (μ : (k : ℕ) → Fin (W k) → Measure (Coeff × ℝ))
    (hcoef : ∀ k g, μ k g {p | ∃ e, K k < |p.1.2 e|} = 0)
    (hpt : ∀ k g t, μ k g (univ ×ˢ {t}) = 0)
    (hfin : ∀ k g, μ k g univ ≠ ⊤)
    (gL : (k : ℕ) → Fin (W k) → (Fin 2 → ℝ) × ℤ → ℝ≥0∞)
    (hgL : ∀ k g, Measurable (gL k g) ∧ Measure.map (obsL (N k ^ (-L))) (μ k g) =
      (volume.prod Measure.count).withDensity (gL k g))
    (GG : (k : ℕ) → Fin (W k) → ℝ → ((Fin 2 → ℝ) × ℤ) × ℤ → ℝ≥0∞)
    (hGG : ∀ k g u, 0 < u → u ≤ U → Measurable (GG k g u) ∧
      Measure.map (obsG (N k ^ (-L)) (N k ^ (-u))) (μ k g) =
        ((volume.prod Measure.count).prod Measure.count).withDensity (GG k g u))
    (htypL : ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∑ g, ENNReal.ofReal (ω k g) * μ k g
        {p | ENNReal.ofReal (N k ^ (-fL + τ)) < gL k g (obsL (N k ^ (-L)) p)} ≤
        ENNReal.ofReal (N k ^ (-c)))
    (htypG : ∀ u τ : ℝ, 0 < u → u ≤ U → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∑ g, ENNReal.ofReal (ω k g) * μ k g
        {p | ENNReal.ofReal (N k ^ (-fL - S * u + τ)) <
          GG k g u (obsG (N k ^ (-L)) (N k ^ (-u)) p)} ≤ ENNReal.ofReal (N k ^ (-c)))
    (hsys : ∀ h κ : ℝ, 0 < h → 0 < κ →
      ∃ᶠ k in atTop, HasTrueSystem (N k) (W k) (ω k) (μ k) L fL h (N k ^ κ)) :
    ∀ h ε : ℝ, 0 < h → 0 < ε →
      ∃ᶠ k in atTop, HasPackets (N k) (W k) (ω k) (μ k) L fL h ε := by
  intro h ε hh hε
  set u := min U (ε / 8) with hudef
  have hu : 0 < u := lt_min hU (by positivity)
  have huU : u ≤ U := min_le_left _ _
  have huε : u ≤ ε / 8 := min_le_right _ _
  set τG := S * u / 2 with hτGdef
  have hτG : 0 < τG := by positivity
  obtain ⟨cG, hcG, hevG⟩ := htypG u τG hu huU hτG
  set τL := ε / 16 with hτLdef
  have hτL : 0 < τL := by positivity
  obtain ⟨cL, hcL, hevL⟩ := htypL τL hτL
  set κ := min (ε / 100) (min (cG / 4) (min (cL / 4) (S * u / 12))) with hκdef
  have hκ : 0 < κ := lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  have hκε : κ ≤ ε / 100 := min_le_left _ _
  have hκG : κ ≤ cG / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hκL : κ ≤ cL / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκS : κ ≤ S * u / 12 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set h' := min h (ε / 8) with hh'def
  have hh' : 0 < h' := lt_min hh (by positivity)
  have hh'h : h' ≤ h := min_le_left _ _
  have hh'ε : h' ≤ ε / 8 := min_le_right _ _
  -- the eventual inequalities
  have ev1 := eventually_const_le_rpow hNtop 80 (show 0 < S * u / 2 - 3 * κ by linarith)
  have ev2 := eventually_const_le_rpow hNtop 4 (show 0 < ε - u - h' - 2 * κ by linarith)
  have ev4 := eventually_const_le_rpow hNtop (186624 * 4 * 256 * 160000)
    (show 0 < ε - (15 * κ + 2 * h' + 2 * u + 4 * τL) by linarith)
  have ev5a := eventually_const_le_rpow hNtop 5 (show 0 < ε - κ by linarith)
  have ev5b := eventually_const_le_rpow hNtop 5 (show 0 < cG - κ by linarith)
  have ev5c := eventually_const_le_rpow hNtop 5 (show 0 < cL - κ by linarith)
  have evK := hKsub κ hκ
  have hev := ev1.and (ev2.and (ev4.and (ev5a.and (ev5b.and (ev5c.and (evK.and
    (hevG.and hevL)))))))
  refine ((hsys h' κ hh' hκ).and_eventually hev).mono ?_
  rintro k ⟨hts, e1, e2, e4, e5a, e5b, e5c, eK, eG, eL⟩
  have hN1 : 1 ≤ N k := le_trans (by norm_num) (hN2 k)
  have hN0 : 0 < N k := lt_of_lt_of_le one_pos hN1
  have hΛ : 1 ≤ N k ^ κ := Real.one_le_rpow hN1 hκ.le
  set Λ := N k ^ κ with hΛdef
  have hθL : 0 ≤ N k ^ (-fL + τL) := (Real.rpow_pos_of_pos hN0 _).le
  have hθG : 0 ≤ N k ^ (-fL - S * u + τG) := (Real.rpow_pos_of_pos hN0 _).le
  set lam := N k ^ (-τL) / (4 * Λ ^ 2 * (2 * Λ + 3)) with hlamdef
  have hlam : 0 < lam := by
    have := Real.rpow_pos_of_pos hN0 (-τL)
    positivity
  have hp := packets_of_trueSystem (N := N k) (L := L) (fL := fL) (h := h') (ε := ε) (Λ := Λ)
    (K := K k) (b := N k ^ (-u)) (θL := N k ^ (-fL + τL)) (θG := N k ^ (-fL - S * u + τG))
    (lam := lam) hN0 hΛ (le_trans zero_le_one (hK1 k)) (Real.rpow_pos_of_pos hN0 _) hθL hθG
    hlam (hcoef k) (hpt k) (hfin k) (gL k) (fun g => (hgL k g).1) (fun g => (hgL k g).2)
    (fun g => GG k g u) (fun g => (hGG k g u hu huU).1) (fun g => (hGG k g u hu huU).2)
    ?P1 ?P2 ?P3 ?P4 ?P5 ?P6 hts
  · exact hp.mono hN1 hh'h le_rfl
  · -- P1
    have : -fL - S * u + τG = -fL - S * u / 2 := by rw [hτGdef]; ring
    rw [this]
    exact cond_P1 hN1 hκ.le e1
  · -- P2
    exact cond_P2 hN1 e2
  · -- P3
    have hD : 0 < 4 * Λ ^ 2 * (2 * Λ + 3) := by positivity
    have e : N k ^ (-τL) * N k ^ (-fL + τL) = N k ^ (-fL) := by
      rw [← Real.rpow_add hN0]; ring_nf
    apply le_of_eq
    rw [← e, hlamdef]
    field_simp
  · -- P4
    exact cond_P4 hN1 hκ.le hu.le hh'.le hL (hK1 k) eK e4
  · -- P5
    exact cond_P5 hN0 eG eL e5a e5b e5c
  · -- P6
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

end Submission.Obl.k4_scalar_terminal_chart_packet_extraction
