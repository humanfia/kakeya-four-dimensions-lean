import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.TransferApply

/-!
# The cover from one fitted block

`explicit_cover`: on a block `[t₀, t₀ + H]` with a fitting set `T` (both row components affine
up to `Efit`, every time of `T` carrying prepared labeled mass `≥ δ/4`, every prepared
trajectory of labeled duration `≥ δ/4`), the reading time, the group windows and the transfer
give one time `ts`, a set `L₁` of labeled incidence mass `≥ (δ/4)(mL/2)` and at most
`pairBound` pairs `(⌊S(ts)/w⌋, ⌊(γ - A · y)/w⌋)`, where
`mL = (f / (4 C₁ C₂)) ((δ/4)² λ / H - NG ((2K/p₀ + 2)² f + μ₀))` and `λ ≤ |T|`.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The mass of `L₀` guaranteed by the group sum. -/
def massL (K d H p₀ f μ₀ δ lam : ℝ) : ℝ :=
  f / (4 * (cnt1 K d p₀ * cap2 K d H p₀)) *
    ((δ / 4) ^ 2 * lam / H - groupCount K d H * ((2 * K / p₀ + 2) ^ 2 * f + μ₀))

theorem explicit_cover {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Fin 2 → ℝ}
    {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (h : Data ν y β γ E F d K ζ) (hK : 1 ≤ K) (hd : 0 ≤ d) (hζ0 : 0 ≤ ζ)
    {δ : ℝ} (hδ : 0 < δ) {E' : Set (Ω × ℝ)} (hE' : MeasurableSet E') (hE'E : E' ⊆ E)
    (hlong : ∀ q ∈ E', ENNReal.ofReal (δ / 4) ≤ duration E q.1)
    {t₀ H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hζH : ζ ≤ H)
    {T : Set ℝ} (hT : MeasurableSet T) (hTsub : T ⊆ Icc t₀ (t₀ + H)) (hT01 : T ⊆ Icc 0 1)
    (htime : ∀ t ∈ T, ENNReal.ofReal (δ / 4) ≤ timeMass ν E' t)
    {lam : ℝ} (hlam : 0 < lam) (hTvol : ENNReal.ofReal lam ≤ volume T)
    {a A : Fin 2 → ℝ} {Efit KA : ℝ} (hEfit : 0 ≤ Efit) (hKA : 0 ≤ KA)
    (hfit : ∀ t ∈ T, ∀ i, |F t i - (a i + (t - t₀) * A i)| ≤ Efit) (hA : ∀ i, |A i| ≤ KA)
    {w p₀ f μ₀ w' : ℝ} {n : ℕ} (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hζq : ζ ≤ H * p₀)
    (hr1 : 2 * (4 * K ^ 2 + K + 1) * H ≤ 1) (hf : 0 < f) (hμ₀ : 0 < μ₀) (hw' : 0 < w')
    (hbig : 8 * (cnt1 K d p₀ * cap2 K d H p₀) ≤ μ₀)
    (hfarN : cnt1 K d p₀ * (2 * (p₀ + 2 * (4 * K * Efit / H)) / w') * groupMass K d H ^ 2 <
      μ₀ ^ 2 / 2)
    (hHw : H ≤ w) (hw1 : w ≤ 1) (hrw : (2 : ℝ) ^ (-(n : ℤ)) ≤ w)
    (hwr : w ≤ 2 * (2 : ℝ) ^ (-(n : ℤ))) (hHr : H ≤ (2 : ℝ) ^ (-(n : ℤ)))
    (hρ : 2 * (w' + slopeVar K KA H p₀ ζ) ≤ w)
    (hmL : 0 < massL K d H p₀ f μ₀ δ lam) :
    ∃ ts ∈ Icc (0 : ℝ) 1, ∃ L₁ : Set Ω, MeasurableSet L₁ ∧
      ENNReal.ofReal (δ / 4 * (massL K d H p₀ f μ₀ δ lam / 2)) ≤
        (ν.prod volume) (E ∩ L₁ ×ˢ univ) ∧
      ∃ P : Finset (ℤ × ℤ), (P.card : ℝ) ≤ pairBound K KA d w (massL K d H p₀ f μ₀ δ lam) ∧
        ∀ l ∈ L₁, (⌊scal y β γ F l ts / w⌋, ⌊resSlope y γ A l / w⌋) ∈ P := by
  have hK0 : 0 ≤ K := by linarith
  have hTfin : volume T ≠ ⊤ := ne_top_of_le_ne_top (b := volume (Icc t₀ (t₀ + H)))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (measure_mono hTsub)
  have hT0 : volume T ≠ 0 := by
    intro h0; rw [h0] at hTvol; exact absurd (ENNReal.ofReal_eq_zero.mp (le_antisymm hTvol bot_le))
      (not_le.mpr hlam)
  obtain ⟨ts, htsT, hread⟩ := exists_reading_time hE' hT hTfin hT0 htime
  have htsI := hTsub htsT
  have hts0 : ts - t₀ ∈ Icc (0 : ℝ) H := ⟨by linarith [htsI.1], by linarith [htsI.2]⟩
  obtain ⟨L₀, κ, hL₀m, hL₀E, hwin, hineq⟩ := dense_slope_lines h hK hd hζ0 hE' hE'E hH hH1 hζH
    hT hTsub hT01 hEfit hKA hfit hA htsT hp₀ hp₀1 hζq hr1 hf hμ₀ hw' hbig hfarN
  -- the mass of `L₀`
  set C := cnt1 K d p₀ * cap2 K d H p₀ with hCdef
  have hC : 0 < C := by
    rw [hCdef]; unfold cnt1 cap2
    have : 0 < 4 * K ^ 2 + K + 1 := by positivity
    positivity
  set GC := groupCount K d H * ((2 * K / p₀ + 2) ^ 2 * f + μ₀) with hGC
  have hlow : ENNReal.ofReal ((δ / 4) ^ 2 * lam / H) ≤
      ENNReal.ofReal H⁻¹ * ∫⁻ l, {l | (l, ts) ∈ E'}.indicator (durIn E' T) l ∂ν := by
    calc ENNReal.ofReal ((δ / 4) ^ 2 * lam / H)
        = ENNReal.ofReal H⁻¹ * (ENNReal.ofReal (δ / 4) ^ 2 * ENNReal.ofReal lam) := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
      _ ≤ ENNReal.ofReal H⁻¹ * (ENNReal.ofReal (δ / 4) ^ 2 * volume T) := by gcongr
      _ ≤ _ := by gcongr
  have hmassL : ENNReal.ofReal (massL K d H p₀ f μ₀ δ lam) ≤ ν L₀ := by
    have h1 := hlow.trans hineq
    rcases eq_or_ne (ν L₀) ⊤ with htop | htop
    · rw [htop]; exact le_top
    · rw [← ENNReal.ofReal_toReal htop] at h1 ⊢
      have hα : 0 ≤ 4 * C / f := div_nonneg (by linarith) hf.le
      have hGC0 : 0 ≤ GC := by
        rw [hGC]; unfold groupCount
        have : (0 : ℝ) ≤ (1 / H) ^ d := Real.rpow_nonneg (by positivity) _
        positivity
      rw [← ENNReal.ofReal_mul hα, ← ENNReal.ofReal_add (mul_nonneg hα ENNReal.toReal_nonneg)
        hGC0] at h1
      have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
      apply ENNReal.ofReal_le_ofReal
      unfold massL
      rw [← hCdef, ← hGC]
      have h3 : (δ / 4) ^ 2 * lam / H - GC ≤ 4 * C / f * (ν L₀).toReal := by linarith
      calc f / (4 * C) * ((δ / 4) ^ 2 * lam / H - GC) ≤ f / (4 * C) * (4 * C / f * (ν L₀).toReal) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (ν L₀).toReal := by field_simp
  obtain ⟨L₁, hL₁L₀, hL₁m, hL₁mass, P, hP, hPmem⟩ := cover_pairs h hK hd hH hζH hHw hw1
    (hT01 htsT) hts0 hrw hwr hHr hKA hA hL₀m (fun l hl => hE'E (hL₀E l hl)) hρ hwin hmL hmassL
  refine ⟨ts, hT01 htsT, L₁, hL₁m, ?_, P, hP, hPmem⟩
  -- every trajectory of `L₁` has labeled duration `≥ δ/4`
  rw [Measure.prod_apply (h.measurableSet_E.inter (hL₁m.prod MeasurableSet.univ))]
  calc ENNReal.ofReal (δ / 4 * (massL K d H p₀ f μ₀ δ lam / 2))
      = ENNReal.ofReal (δ / 4) * ENNReal.ofReal (massL K d H p₀ f μ₀ δ lam / 2) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (δ / 4) * ν L₁ := by gcongr
    _ = ∫⁻ l in L₁, ENNReal.ofReal (δ / 4) ∂ν := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ l in L₁, volume (Prod.mk l ⁻¹' (E ∩ L₁ ×ˢ univ)) ∂ν := by
        apply setLIntegral_mono (measurable_measure_prodMk_left
          (h.measurableSet_E.inter (hL₁m.prod MeasurableSet.univ)))
        intro l hl
        refine (hlong (l, ts) (hL₀E l (hL₁L₀ hl))).trans (le_of_eq ?_)
        unfold duration
        congr 1; ext t; simp [hl]
    _ ≤ ∫⁻ l, volume (Prod.mk l ⁻¹' (E ∩ L₁ ×ˢ univ)) ∂ν := setLIntegral_le_lintegral _ _

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
