-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/PacketNumerics.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Numerical choices for `frozen_packet_from_switching`: with
`Λ' = 8 K⁵`, duration threshold `h / (48 K)`, `Λ = 8 (48 K Kr)⁶` and the curl
threshold `θ = a ζ / (2 h (G₀ Λ'^cCurl + 1))`, the switching budget and the
potential error budget hold as soon as the census height mesh satisfies one
smallness condition `wc^(1-d₁) ≤ ζ rp⁹ / C` and the qualified fit error is
below `a ζ / 2` after the Remez loss.
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.FrozenPacket

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory
open Submission.Obl.k4_physical_row_packet_potential.PotentialFits

noncomputable section

namespace PacketSwitching

/-- The coefficient of the curl in the potential error. -/
def curlWeight (D : ℕ) (U V : ℝ) : ℝ := 9 * ((D + 1 : ℕ) : ℝ) ^ 2 * (max 1 (3 * U)) ^ D * V

/-- The constant of the census smallness condition. -/
def censusConstant (D cNorm cCurl : ℕ) (K Kr U V pv : ℝ) : ℝ :=
  8 * (48 * K * Kr) ^ 6 * (9216 * ((D : ℝ) + 2)) * K * (max 1 (K + pv)) ^ 4 *
    (8 * (48 * K * Kr) ^ 6) ^ cNorm * (2 * (curlWeight D U V * (8 * K ^ 5) ^ cCurl + 1))

theorem gradientBudget_eq (D : ℕ) (U curl V : ℝ) :
    3 * gradientBudget D U curl * V = curlWeight D U V * curl := by
  unfold gradientBudget curlWeight
  ring

theorem packet_numerics (D cNorm cCurl : ℕ)
    {K Kr U V a h ζ d₁ m νA pc wc rp pv η err : ℝ}
    (hK : 2 ≤ K) (hKr : 1 ≤ Kr) (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : 0 < a) (hh : 0 < h)
    (hζ : 0 < ζ) (hd₁ : d₁ < 1) (hm : 0 < m) (hνA : 0 ≤ νA) (hmass : h * νA ≤ K * m)
    (hpc : 0 < pc) (hwc : 0 < wc) (hrp : 0 < rp) (hpv : 0 ≤ pv)
    (hsmall : wc ^ (1 - d₁) * censusConstant D cNorm cCurl K Kr U V pv ≤ ζ * rp ^ 9)
    (herr : h * ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err) ≤ a * ζ / 2) :
    let Λ := 8 * (48 * K * Kr) ^ 6
    let Λ' := 8 * K ^ 5
    let qd := h / (48 * K)
    let θ := a * ζ / (2 * h * (curlWeight D U V * Λ' ^ cCurl + 1))
    0 < qd ∧ qd ≤ h ∧ 0 < θ ∧ 2 ≤ Λ ∧ 2 ≤ Λ' ∧
    (Kr * (h / qd)) ^ 6 *
        (Λ⁻¹ + 9216 * ((D : ℝ) + 2) * (K / (pc ^ (3 : ℕ) * wc ^ d₁)) * pc ^ 3 *
          (a / h) * wc * (max 1 (K + pv)) ^ 4 * Λ ^ cNorm / (θ * rp ^ 9)) +
      6 * (qd * νA / m + 1 / 1000000000000) + K * (h * νA) * K ^ 3 / (m * Λ') < 1 ∧
    h * ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err +
      3 * gradientBudget D U (Λ' ^ cCurl * θ) * V) ≤ a * ζ := by
  intro Λ Λ' qd θ
  have hK0 : 0 < K := by linarith
  have hG0 : 0 ≤ curlWeight D U V := by unfold curlWeight; positivity
  have hΛ'0 : 0 < Λ' := by positivity
  have hΛ0 : 0 < Λ := by positivity
  have hW0 : 0 < curlWeight D U V * Λ' ^ cCurl + 1 := by positivity
  have hθ0 : 0 < θ := by positivity
  have hqd : 0 < qd := by positivity
  have hhqd : h / qd = 48 * K := by
    simp only [qd]
    field_simp
  refine ⟨hqd, ?_, hθ0, ?_, ?_, ?_, ?_⟩
  · simp only [qd]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · simp only [Λ]
    have : (1 : ℝ) ≤ (48 * K * Kr) ^ 6 := one_le_pow₀ (by nlinarith)
    linarith
  · simp only [Λ']
    have : (1 : ℝ) ≤ K ^ 5 := one_le_pow₀ (by linarith)
    linarith
  · -- the budget
    rw [hhqd]
    set R := (48 * K * Kr) ^ 6 with hR
    have hR1 : (1 : ℝ) ≤ R := one_le_pow₀ (by nlinarith)
    -- first part: Λ⁻¹
    have hpart1 : (Kr * (48 * K)) ^ 6 * Λ⁻¹ = 1 / 8 := by
      simp only [Λ]
      field_simp
    -- the census part
    have hwpow : wc / wc ^ d₁ = wc ^ (1 - d₁) := by
      rw [Real.rpow_sub hwc, Real.rpow_one]
    have hX : 9216 * ((D : ℝ) + 2) * (K / (pc ^ (3 : ℕ) * wc ^ d₁)) * pc ^ 3 * (a / h) * wc *
        (max 1 (K + pv)) ^ 4 * Λ ^ cNorm / (θ * rp ^ 9) =
        9216 * ((D : ℝ) + 2) * K * (max 1 (K + pv)) ^ 4 * Λ ^ cNorm *
          (2 * (curlWeight D U V * Λ' ^ cCurl + 1)) * wc ^ (1 - d₁) / (ζ * rp ^ 9) := by
      rw [← hwpow]
      have hwd : 0 < wc ^ d₁ := Real.rpow_pos_of_pos hwc d₁
      simp only [θ]
      field_simp
    have hpart2 : (Kr * (48 * K)) ^ 6 *
        (9216 * ((D : ℝ) + 2) * K * (max 1 (K + pv)) ^ 4 * Λ ^ cNorm *
          (2 * (curlWeight D U V * Λ' ^ cCurl + 1)) * wc ^ (1 - d₁) / (ζ * rp ^ 9)) ≤ 1 / 8 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have hc : censusConstant D cNorm cCurl K Kr U V pv =
          8 * (Kr * (48 * K)) ^ 6 * (9216 * ((D : ℝ) + 2)) * K * (max 1 (K + pv)) ^ 4 *
            Λ ^ cNorm * (2 * (curlWeight D U V * Λ' ^ cCurl + 1)) := by
        simp only [censusConstant, Λ, Λ']
        ring
      rw [hc] at hsmall
      nlinarith [hsmall]
    -- second part
    have hpart3 : qd * νA / m ≤ 1 / 48 := by
      simp only [qd]
      rw [div_le_iff₀ hm]
      have : h / (48 * K) * νA = h * νA / (48 * K) := by ring
      rw [this, div_le_iff₀ (by positivity)]
      nlinarith
    -- third part
    have hpart4 : K * (h * νA) * K ^ 3 / (m * Λ') ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      simp only [Λ']
      have h1 : K * (h * νA) * K ^ 3 ≤ K * (K * m) * K ^ 3 := by gcongr
      nlinarith [h1]
    rw [mul_add, hpart1, hX]
    nlinarith [hpart2, hpart3, hpart4]
  · -- the error budget
    rw [gradientBudget_eq]
    have h1 : h * (curlWeight D U V * (Λ' ^ cCurl * θ)) ≤ a * ζ / 2 := by
      simp only [θ]
      rw [show h * (curlWeight D U V * (Λ' ^ cCurl *
          (a * ζ / (2 * h * (curlWeight D U V * Λ' ^ cCurl + 1))))) =
          a * ζ / 2 * (curlWeight D U V * Λ' ^ cCurl / (curlWeight D U V * Λ' ^ cCurl + 1)) by
        field_simp]
      apply mul_le_of_le_one_right (by positivity)
      rw [div_le_one hW0]
      linarith
    nlinarith [herr, h1]

/-- **The frozen packet of one old block, numerics discharged.** Besides the
clauses, palette domination and the field, only two smallness conditions
remain: the census height mesh `wc` and the qualified fit error `err`. -/
theorem frozen_packet (D : ℕ) : ∃ cNorm cCurl : ℕ,
    ∀ (q : ℕ) (precision loss Nk L d₁ gain κ : ℝ) (ν : Measure Ln) [IsProbabilityMeasure ν]
      (B r : ℝ) (T j : ℕ) (c u : P2) (P : Po) (hP : P.totalDegree ≤ 2)
      (A : Set Ln) (hA : MeasurableSet A) (F H : Set Ev)
      (K ε : ℝ) (S : Set Ev)
      (hε : 0 < ε) (hεζ : ε ≤ δ Nk (precision * gain * L))
      (hεa : ε ≤ (δ Nk r / ((2:ℝ)^T)⁻¹) * δ Nk (precision * gain * L))
      (ha : 0 < δ Nk r) (haK : δ Nk r ≤ K * ((2:ℝ)^T)⁻¹)
      (hhζ : ((2:ℝ)^T)⁻¹ ≤ δ Nk (precision * gain * L))
      (hK2 : 2 ≤ K) (hκK : κ ≤ K) (hKN : K ≤ Nk ^ (loss * gain * L))
      (hS : MeasurableSet S) (hSHF : S ⊆ H ∩ F) (hSA : S ⊆ A ×ˢ univ)
      (hSunit : S ⊆ univ ×ˢ Icc (0 : ℝ) 1)
      (htime : ∀ z ∈ S, z.2 ∈ Icc (start T j) (start T j + clock T))
      (href : 0 < ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A)
      (hmass : ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A / ENNReal.ofReal K ≤
        ((ν.prod volume).restrict S) univ)
      (hpts : ∀ p ∈ S, ‖packetBase T j c u p‖ ≤ K ∧ ‖v p.1‖ ≤ K ∧
        (∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (xp p.1 t) P| ≤ K ∧
          |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 P)| ≤ K * B ∧
          |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤
            K * B ^ 2) ∧
        B / K ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 P)|)
      (hstrip : ∀ k : (Fin 3 → ℤ) × ℤ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
        ((ν.prod volume).restrict S)
            {p | physicalCode (packetBase T j c u) (fun p => packetSignal P p / δ Nk r) ε p = k ∧
              |inner ℝ n (v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤
          (1 / 1000000000000 : ENNReal) * ((ν.prod volume).restrict S)
            {p | physicalCode (packetBase T j c u) (fun p => packetSignal P p / δ Nk r) ε p = k})
      (hceil : ∀ U : Set P3, MeasurableSet U →
        ((ν.prod volume).restrict S) {p | packetBase T j c u p ∈ U} ≤
          ENNReal.ofReal K * (ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A) * volume U)
      (hband : ∀ (w : ℝ), ε ≤ w → w ≤ 1 → ∀ (U : Set P3), MeasurableSet U →
        ∀ f : P3 → ℝ, Measurable f →
        ((ν.prod volume).restrict S)
            {p | packetBase T j c u p ∈ U ∧ |packetSignal P p / δ Nk r - f (packetBase T j c u p)| ≤ w} ≤
          ENNReal.ofReal (K * w ^ d₁) * (ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A) * volume U)
      (hcount : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
        K ^ (100 : ℕ) * ((2:ℝ)^T)⁻¹ * p ≤ δ Nk r * w →
        Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
          (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
            ⌊packetSignal P e / δ Nk r / w⌋)) e = k} ∧
        (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
          (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
            ⌊packetSignal P e / δ Nk r / w⌋)) e = k}).ncard : ℝ) ≤ K / (p ^ (3 : ℕ) * w ^ d₁))
      {σ : Type*} [MeasurableSpace σ] [MeasurableSingletonClass σ] [Countable σ]
      [StandardBorelSpace σ] (st : Ev → σ) (hstm : Measurable st)
      (hrefine : ∀ z z', st z = st z' →
        packetState T j c u P (δ Nk r) ε z = packetState T j c u P (δ Nk r) ε z')
      (hstripSt : ∀ k (n : P2) (t : ℝ), ‖n‖ = 1 →
        ((ν.prod volume).restrict S) {p | st p = k ∧ |inner ℝ n (v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤
          (1 / 1000000000000 : ENNReal) * ((ν.prod volume).restrict S) {p | st p = k})
      (pv : ℝ) (hpv : 0 < pv) (π : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure π] (Kr : ℝ)
      (hKr : 1 ≤ Kr)
      (hrect : ∀ k (Aw : Set (Fin 2 → ℤ)), MeasurableSet Aw →
        (ν.prod volume) ({z | st z = k ∧ velBin pv z.1 ∈ Aw} ∩ S) ≤
          ENNReal.ofReal Kr * (ν.prod volume) (st ⁻¹' {k} ∩ S) * π Aw)
      (rp : ℝ) (hrp : 0 < rp) (hrw : 2 * (K + 1) * (rp + pv) ≤ K ^ (-100 : ℝ))
      (hr4 : rp + pv ≤ 1 / 4)
      (pc wc : ℝ) (hpc0 : ε ≤ pc) (hpc1 : pc ≤ 1) (hwc0 : ε ≤ wc) (hwc1 : wc ≤ 1)
      (hpw : K ^ (100 : ℕ) * ((2:ℝ)^T)⁻¹ * pc ≤ δ Nk r * wc)
      (Tf : Fin 3 → MvPolynomial (Fin 3) ℝ) (hT : ∀ i, (Tf i).totalDegree ≤ D) (hDq : D + 1 ≤ q)
      (AT : ℝ) (hAT : 0 ≤ AT) (hcoeffT : ∀ i m, |(Tf i).coeff m| ≤ AT)
      (hcoeffBudget : ((D + 1 : ℕ) : ℝ) * 3 * AT ≤ K)
      (Lines : Set Ln) (hLines : ∀ z ∈ S, z.1 ∈ Lines) (times : Ln → Set ℝ)
      (η err : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (herr0 : 0 ≤ err)
      (htimes : ∀ l ∈ Lines, times l ⊆ Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (times l))
      (hfitL : ∀ l ∈ Lines, ∀ s ∈ times l,
        |ParentSignal.rate P l (start T j + clock T * s) - ∑ i : Fin 3,
          direction l i * MvPolynomial.eval
            (fun i => packetBase T j c u (l, start T j + clock T * s) i) (Tf i)| ≤ err)
      (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
      (hbaseL : ∀ l ∈ Lines, ∀ t ∈ Icc (start T j) (start T j + clock T), ∀ i,
        |packetBase T j c u (l, t) i| ≤ U)
      (hvelL : ∀ l ∈ Lines, ∀ i, |direction l i| ≤ V)
      (hwidthH : simHeightError D (48 * K) ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err)
          (ε + ε * K) (pv / 2) (δ Nk r / clock T * ε + ε * (40 * K))
          ((D + 1 : ℕ) * (max 1 (3 * (K + K + 7 * (ε + ε * K + pv / 2)))) ^ D * AT)
          (max 1 (K + pv))
          (3 * ((D + 1 : ℕ) * (max 1 (3 * (K + K + 7 * (ε + ε * K + pv / 2)))) ^ D *
            ((D : ℝ) * AT))) ≤ δ Nk r / clock T * wc / 2)
      (hwidthB : 6 * (ε + ε * K + pv / 2) ≤ pc / 2)
      (hd₁ : d₁ < 1)
      (hsmall : wc ^ (1 - d₁) * censusConstant D cNorm cCurl K Kr U V pv ≤
        δ Nk (precision * gain * L) * rp ^ 9)
      (herr : clock T * ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err) ≤
        δ Nk r * δ Nk (precision * gain * L) / 2),
      PhysicalPotentialPacket q precision loss Nk L d₁ gain κ ν B r T j c u P A F H := by
  obtain ⟨cNorm, cCurl, hfp⟩ := frozen_packet_from_switching D
  refine ⟨cNorm, cCurl, ?_⟩
  intro q precision loss Nk L d₁ gain κ ν _ B r T j c u P hP A hA F H K ε S hε hεζ hεa ha haK hhζ
    hK2 hκK hKN hS hSHF hSA hSunit htime href hmass hpts hstrip hceil hband hcount σ _ _ _ _ st hstm
    hrefine hstripSt pv hpv π _ Kr hKr hrect rp hrp hrw hr4 pc wc hpc0 hpc1 hwc0 hwc1 hpw Tf hT
    hDq AT hAT hcoeffT hcoeffBudget Lines hLines times η err hη hη1 herr0 htimes hfitL U V hU hV
    hbaseL hvelL hwidthH hwidthB hd₁ hsmall herr
  have hh := clock_pos T
  have hK0 : 0 < K := by linarith
  have hε0 := hε
  -- the mass relation `h ν(A) ≤ K m`
  have hfin : (ν.prod volume) S ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1))
    · rw [Measure.prod_prod, Real.volume_Icc]; simp
    · exact measure_mono hSunit
  have hmassR : clock T * (ν A).toReal ≤ K * (ν.prod volume).real S := by
    rw [Measure.restrict_apply_univ] at hmass
    have h1 := ENNReal.toReal_mono hfin hmass
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal hK0.le, div_le_iff₀ hK0] at h1
    rw [measureReal_def]
    have : clock T = ((2:ℝ)^T)⁻¹ := rfl
    rw [this]
    linarith
  have hpos : 0 < (ν.prod volume).real S := by
    rw [measureReal_def]
    apply ENNReal.toReal_pos _ hfin
    intro h0
    rw [Measure.restrict_apply_univ, h0] at hmass
    exact (ENNReal.div_ne_zero.mpr ⟨href.ne', ENNReal.ofReal_ne_top⟩) (le_antisymm hmass bot_le)
  obtain ⟨hqd, hqdh, hθ, hΛ, hΛ', hbudget, herrB⟩ := packet_numerics D cNorm cCurl
    (K := K) (Kr := Kr) (U := U) (V := V) (a := δ Nk r) (h := clock T)
    (ζ := δ Nk (precision * gain * L)) (d₁ := d₁) (m := (ν.prod volume).real S)
    (νA := (ν A).toReal) (pc := pc) (wc := wc) (rp := rp) (pv := pv) (η := η) (err := err)
    hK2 hKr hU hV ha hh (lt_of_lt_of_le hε0 hεζ) hd₁ hpos ENNReal.toReal_nonneg hmassR
    (hε0.trans_le hpc0) (hε0.trans_le hwc0) hrp hpv.le hsmall herr
  have hqdeq : clock T / (clock T / (48 * K)) = 48 * K := by
    field_simp
  exact hfp q precision loss Nk L d₁ gain κ ν B r T j c u P hP A hA F H K ε S hε hεζ hεa ha haK
    hhζ hK2 hκK hKN hS hSHF hSA hSunit htime href hmass hpts hstrip hceil hband hcount st hstm
    hrefine hstripSt pv hpv π Kr (by linarith) hrect rp hrp hrw hr4 pc wc hpc0 hpc1 hwc0 hwc1 hpw Tf hT hDq AT hAT
    hcoeffT hcoeffBudget Lines hLines times η err hη hη1 herr0 htimes hfitL U V hU hV hbaseL
    hvelL (clock T / (48 * K)) hqd hqdh (by rw [hqdeq]; exact hwidthH) hwidthB _ _ _ hθ hΛ hΛ'
    hbudget herrB

end PacketSwitching

end

end Submission.Obl.k4_physical_row_packet_potential.Switch
