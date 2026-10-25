import Submission.Obl.k4_clean_cover_graph_atlas.DiscriminantNumerics
import Submission.Obl.k4_clean_cover_graph_atlas.SampleScales
import Submission.Obl.k4_clean_cover_graph_atlas.SampleDiscriminant

namespace Submission.Obl.k4_clean_cover_graph_atlas

/-- The common sheet scale also bounds the original (unpruned) packet
 discriminants. The exponent six is fixed before all sample parameters. -/
theorem sheetScale_dominates_original_discriminant
    {N κ σ Cdisc ρ gain L δ₀ ε τ : ℝ}
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hκN : κ ≤ N ^ σ) (hσ : 0 ≤ σ)
    (hC : 0 ≤ Cdisc) (hρ : 0 ≤ ρ) (hgain : 0 ≤ gain) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hτ : 0 ≤ τ) (hδρ : δ₀ ≤ ρ * gain) :
    discriminantAllowance Cdisc N κ ((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ)
      (4 * ρ * gain * L + 4 * ε) ≤
      sheetScale (discriminantConstant Cdisc) 6 N (N ^ (greedySlack ρ gain L ε)) κ
        (slackTot ρ gain L ε σ τ) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  let S := slackTot ρ gain L ε σ τ
  let U := N ^ greedySlack ρ gain L ε
  let Kd := discriminantConstant Cdisc
  have hS : 0 ≤ S := by dsimp [S, slackTot]; positivity
  have hU : 1 ≤ U := Real.one_le_rpow hN (by dsimp [greedySlack]; positivity)
  have hKd : 0 ≤ Kd := by dsimp [Kd, discriminantConstant]; positivity
  have hfl : discFloor N S ^ (-(6 : ℝ)) = (2 : ℝ) ^ (60 : ℕ) * N ^ (150 * S) := by
    unfold discFloor
    rw [Real.div_rpow (Real.rpow_nonneg hNpos.le _) (by positivity),
      ← Real.rpow_mul hNpos.le]
    have h2 : ((2 : ℝ) ^ (10 : ℕ)) ^ (-(6 : ℝ)) = (2 : ℝ) ^ (-(60 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h2, Real.rpow_neg (by norm_num), div_inv_eq_mul,
      show -(25 * S) * -(6 : ℝ) = 150 * S by ring]
    norm_num only [Real.rpow_ofNat]
    ring
  have hexp : 110 * ρ * gain * L + 80 * ε + 6 * τ + 26 * σ ≤ 150 * S := by
    dsimp [S, slackTot]
    nlinarith [mul_nonneg (mul_nonneg hρ hgain) hL]
  have hcoef : Kd ≤ 3 * Kd * 6 * (U + κ) ^ 2 * (2 : ℝ) ^ (60 : ℕ) := by
    have hsq : 1 ≤ (U + κ) ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ 2 ^ (60 : ℕ) := by norm_num
    calc
      Kd ≤ 3 * Kd * 6 * (U + κ) ^ 2 := by nlinarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) h2
  calc
    _ ≤ Kd * N ^ (110 * ρ * gain * L + 80 * ε + 6 * τ + 26 * σ) :=
      sample_discriminant_exponent_bound (τ := τ) hN hκ hκN hσ hC hρ hgain hL hε hδρ
    _ ≤ Kd * N ^ (150 * S) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN hexp) hKd
    _ ≤ (3 * Kd * 6 * (U + κ) ^ 2 * (2 : ℝ) ^ (60 : ℕ)) * N ^ (150 * S) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = 3 * Kd * 6 * (U + κ) ^ 2 * discFloor N S ^ (-(6 : ℝ)) := by rw [hfl]; ring
    _ ≤ _ := (sheetScale_ge hNpos hKd (by norm_num) (by linarith : 0 ≤ U)
      (zero_le_one.trans hκ)).2.2.2.2

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

/-- Both fitting thicknesses are at most one, directly from the sampled
positive path depth. -/
theorem sampleInput_thickness_bounds (hNk : 1 ≤ Nk) (hL : 0 ≤ L) (hgain : 0 ≤ gain)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst) :
    δ Nk (r i + h * L) ≤ 1 ∧ δ Nk (r i) ≤ 1 := by
  have hi : i < m := hsi.2.1
  have hri : 0 < r i := (hpath.2.2.2.2.1 i hi).2.1
  have hh : 0 ≤ h := hgain.trans hsi.2.2.1
  have hzero : δ Nk 0 = 1 := by simp [δ, Submission.Lib.K4XInterface.gδ]
  constructor
  · exact (delta_antitone hNk (by positivity : 0 ≤ r i + h * L)).trans_eq hzero
  · exact (delta_antitone hNk hri.le).trans_eq hzero

/-- Common scale and coefficient certificates for every original candidate,
prior to any entry subdivision or light-entry pruning. -/
theorem sampleInput_sheetScale_bounds {Cdisc : ℝ} (hCdisc : 0 < Cdisc)
    (hdisc : PacketDiscriminantBound Cdisc)
    (hNk : 1 ≤ Nk) (hL : 0 < L) (hgain : 0 < gain)
    (hd₁ : 0 ≤ d₁) (hd₁1 : d₁ ≤ 1) (hρ : 0 ≤ ρ) (hδ₀ : 0 ≤ δ₀)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hδρ : δ₀ ≤ ρ * gain)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hlin : ∀ q, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) :
    let U := Nk ^ greedySlack ρ gain L ε
    let Abound := sheetScale (discriminantConstant Cdisc) 6 Nk U κ (slackTot ρ gain L ε σ τ)
    2 ≤ Abound ∧ 4 * U ≤ Abound ∧ 4 * κ ≤ Abound ∧ κ + 1 ≤ Abound ∧
      ∀ a : Fin n, ∀ d,
        |(packetDiscriminant (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a))
          (B (γ (old a))) (R' a)).coeff d| ≤ Abound ∧
        |(packetDiscriminant (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a))
          (B (γ (old a))) (R (old a))).coeff d| ≤ Abound := by
  have hκ : 1 ≤ κ := hpath.1
  have hκN : κ ≤ Nk ^ σ := hpath.2.1
  have hKd : 0 ≤ discriminantConstant Cdisc := by unfold discriminantConstant; positivity
  have hscale := sheetScale_ge (S := slackTot ρ gain L ε σ τ)
    (zero_lt_one.trans_le hNk) hKd (by norm_num : (0 : ℝ) ≤ 6)
    (by positivity : 0 ≤ Nk ^ greedySlack ρ gain L ε) (zero_le_one.trans hκ)
  dsimp only
  refine ⟨hscale.2.2.2.1, hscale.1, hscale.2.1, hscale.2.2.1, ?_⟩
  have hbound := sheetScale_dominates_original_discriminant hNk hκ hκN hσ hCdisc.le hρ
    hgain.le hL.le hε hτ hδρ
  intro a d
  have hcert := sampleInput_discriminant_bounds hCdisc hdisc hNk hL hgain hd₁ hd₁1 hρ hδ₀ hε hτ
    hsi hpath hlin a d
  exact ⟨hcert.1.trans hbound, hcert.2.trans hbound⟩

end
end Submission.Obl.k4_clean_cover_graph_atlas
