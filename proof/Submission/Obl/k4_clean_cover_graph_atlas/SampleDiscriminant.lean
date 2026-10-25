import Submission.Obl.k4_clean_cover_graph_atlas.SampleProjectionControl
import Submission.Obl.k4_clean_cover_graph_atlas.OriginalPacketDiscriminant

namespace Submission.Obl.k4_clean_cover_graph_atlas
open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets
section
variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
  {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
  {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {κ : ℝ} {C : ℕ}
  {lev : Fin C → ℕ} {par : Fin C → Fin C} {γ : Fin C → Fin W} {j : Fin C → ℕ}
  {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
  {R : Fin C → MvPolynomial (Fin 4) ℝ} {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
  {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)}

variable {Mpr Dpr Mg Dg : ℕ} {d₁ ρ gain τ ε : ℝ} {n : ℕ} {old : Fin n → Fin C}
  {R' : Fin n → MvPolynomial (Fin 4) ℝ} {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))}
  {V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {q : ℝ} {i : ℕ} {h : ℝ} {s₀ K : ℕ}

/-- Both original tests have one common normalized discriminant allowance,
obtained from each candidate's whole witness law before entry subdivision. -/
theorem sampleInput_discriminant_bounds {Cdisc : ℝ} (hCdisc : 0 < Cdisc)
    (hdisc : PacketDiscriminantBound Cdisc)
    (hNk : 1 ≤ Nk) (hL : 0 < L) (hgain : 0 < gain)
    (hd₁ : 0 ≤ d₁) (hd₁1 : d₁ ≤ 1) (hρ : 0 ≤ ρ) (hδ₀ : 0 ≤ δ₀) (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hlin : ∀ q, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L)
    (a : Fin n) :
    let fitExponent := 4 * ρ * gain * L + 4 * ε
    let loss := (12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ
    let frac := Nk ^ (-loss) / (64 * κ)
    let S := 8 * (κ + 1)
    let allowance := Cdisc * (96 / (frac / S ^ 3)) ^ 6 * (3 * ((Nk ^ fitExponent) ^ 2 + κ ^ 2))
    ∀ d,
      |(packetDiscriminant (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a))
        (B (γ (old a))) (R' a)).coeff d| ≤ allowance ∧
      |(packetDiscriminant (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a))
        (B (γ (old a))) (R (old a))).coeff d| ≤ allowance := by
  let fitExponent := 4 * ρ * gain * L + 4 * ε
  let loss := (12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ
  let frac := Nk ^ (-loss) / (64 * κ)
  let S := 8 * (κ + 1)
  let H := 32 * Nk ^ (-f q + τ + 2 * fitExponent) * (|(Q (old a)).det| / (2 : ℝ) ^ T i)
  let μ := ((ν (γ (old a))).prod volume).restrict (V a)
  have hNkpos : 0 < Nk := zero_lt_one.trans_le hNk
  obtain ⟨hH, hfrac, hfrac1, hS, hcap, hmass, hnorm⟩ :=
    sampleInput_original_packet_control hNk hL hgain hd₁ hd₁1 hρ hδ₀ hε hτ hsi hpath hlin a
  obtain ⟨hlev, _, hP, _, _, hA'A, _, htests, hVm, hVsub, _⟩ := hsi.2.2.2.2.2.2.2.1 a
  have hchart := (hpath.2.2.2.2.2.2.2 (old a)).2.2
  rw [hlev] at hchart
  obtain ⟨hQ, _, _, _, hR, _, _, _, _, hAtests, _, _⟩ := hchart
  have hB : 0 < B (γ (old a)) := (hsi.1.2.2.2 (γ (old a))).2.1
  have hκ : 0 ≤ κ := zero_le_one.trans hpath.1
  have htraceFine : ∀ᵐ p ∂μ,
      ‖normBase (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) p.1 p.2‖ ≤ S / 8 ∧
      |eval (gx p.1 p.2) (R' a)| ≤ Nk ^ fitExponent * δ Nk (r i + h * L) ∧
      |eval (gx p.1 p.2) (pderiv 3 (R' a))| ≤ Nk ^ fitExponent * B (γ (old a)) ∧
      |eval (gx p.1 p.2) (pderiv 3 (pderiv 3 (R' a)))| ≤
        Nk ^ fitExponent * B (γ (old a)) ^ 2 / δ Nk (r i + h * L) := by
    filter_upwards [hnorm, ae_restrict_mem hVm] with p hn hp
    have hsub := hVsub hp
    exact ⟨hn, htests p.1 hsub.2.1 p.2 hsub.2.2.1⟩
  have htraceOld : ∀ᵐ p ∂μ,
      ‖normBase (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) p.1 p.2‖ ≤ S / 8 ∧
      |eval (gx p.1 p.2) (R (old a))| ≤ κ * δ Nk (r i) ∧
      |eval (gx p.1 p.2) (pderiv 3 (R (old a)))| ≤ κ * B (γ (old a)) ∧
      |eval (gx p.1 p.2) (pderiv 3 (pderiv 3 (R (old a))))| ≤
        κ * B (γ (old a)) ^ 2 / δ Nk (r i) := by
    filter_upwards [hnorm, ae_restrict_mem hVm] with p hn hp
    have hsub := hVsub hp
    have ht := (hAtests p.1 (hA'A hsub.2.1)).2.2 p.2 hsub.2.2.1
    exact ⟨hn, ht.2⟩
  have hFine := hdisc (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) (B (γ (old a)))
    hQ hB (R' a) hP μ H frac S (δ Nk (r i + h * L)) (Nk ^ fitExponent)
    hH hfrac hfrac1 hS (gδ_pos Nk _) (Real.rpow_nonneg hNkpos.le _) hcap hmass htraceFine
  have hOld := hdisc (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) (B (γ (old a)))
    hQ hB (R (old a)) hR μ H frac S (δ Nk (r i)) κ
    hH hfrac hfrac1 hS (gδ_pos Nk _) hκ hcap hmass htraceOld
  have hpref : 0 ≤ Cdisc * (96 / (frac / S ^ 3)) ^ 6 := by positivity
  dsimp only
  intro d
  constructor
  · exact (hFine d).trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg κ]) hpref)
  · exact (hOld d).trans (mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg (Nk ^ fitExponent)]) hpref)

end
end Submission.Obl.k4_clean_cover_graph_atlas
