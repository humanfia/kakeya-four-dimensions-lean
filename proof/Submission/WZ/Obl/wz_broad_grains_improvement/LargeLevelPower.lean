-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.LargeLevelPower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.LargeLevelTerminal
import Submission.WZ.Obl.wz_coarse_tube_grains.Main

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory

/-- The local count coefficient is below the stopping threshold as soon as
`m c²` exceeds `δ^(ζ/2)`, with a fixed constant absorbed at small scales. -/
theorem grain_coefficient_le_of_power
    {δ h ζ m c : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ ζ / 8)
    (hsmall : 7962624000 * δ ^ (ζ / 4) ≤ 1)
    (hlarge : δ ^ (ζ / 2) ≤ m * c ^ 2) :
    3981312000 * δ ^ (-h) / (m * (δ ^ h / 2) * c ^ 2) ≤ δ ^ (-ζ) := by
  have hmc : 0 < m * c ^ 2 := (Real.rpow_pos_of_pos hδ _).trans_le hlarge
  have hden : 0 < m * (δ ^ h / 2) * c ^ 2 := by
    rw [show m * (δ ^ h / 2) * c ^ 2 = (m * c ^ 2) * δ ^ h / 2 by ring]
    positivity
  apply (div_le_iff₀ hden).mpr
  have hpow : 7962624000 * δ ^ (ζ / 2 - 2 * h) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
      (by norm_num : (0 : ℝ) ≤ 7962624000)).trans hsmall
  have haux : 7962624000 * δ ^ (-h) ≤ δ ^ (h - ζ / 2) := by
    calc
      _ = (7962624000 * δ ^ (ζ / 2 - 2 * h)) * δ ^ (h - ζ / 2) := by
        rw [mul_assoc, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ 1 * δ ^ (h - ζ / 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hδ.le _)
      _ = _ := one_mul _
  have haux' : δ ^ (h - ζ / 2) ≤ δ ^ (-ζ) * (m * c ^ 2) * δ ^ h := by
    calc
      _ = δ ^ (-ζ) * δ ^ (ζ / 2) * δ ^ h := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ _ := by gcongr
  nlinarith [haux.trans haux']

/-- A uniform power threshold for the terminal step. This retains the original
indices and keeps the existing coarse scale and grain length. -/
theorem stage_three_of_power_large_grain_level
    {ω ζ ε : ℝ} (hω : 0 < ω) (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ {δ h ρ a c g m : ℝ} {n N L : ℕ}
        {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
        {y w : Fin N → V} {f : Fin n → Fin N}
        {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
        {G : Fin L → Set V} {γ : Fin L → Fin N},
      0 < δ → δ ≤ d₀ → h ≤ ε / 2 → h ≤ ζ / 8 →
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      C δ h n x v Y S Z ρ N y w f True →
      HB δ h n x v S Z ρ N y w f a c 0 g L z e G γ m →
      δ ^ (1 - ω / 100) ≤ ρ → ρ ≤ δ ^ (ω / 100) →
      δ ^ ζ * (ρ / δ) * N / n ≤ c →
      (∀ (k : Fin N) (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
        q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i-u‖ ‖v i+u‖ ≤ r} ≤
          δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}) →
      δ ^ (ζ / 2) ≤ m * c ^ 2 → J ω ζ δ ε ρ c n x v Y 3 := by
  obtain ⟨d₁, hd₁, h₁⟩ := wz_coarse_tube_grains.exists_small_mul_rpow
    (C := 7962624000) (a := ζ / 4) (by norm_num) (by positivity)
  obtain ⟨d₂, hd₂, h₂⟩ := wz_coarse_tube_grains.exists_small_mul_rpow
    (C := 4) (a := ε / 2) (by norm_num) (by positivity)
  obtain ⟨d₃, hd₃, h₃⟩ := wz_coarse_tube_grains.exists_small_mul_rpow
    (C := 4) (a := ω / 100) (by norm_num) (by positivity)
  refine ⟨min (1 / 100) (min d₁ (min d₂ d₃)), by positivity, min_le_left _ _, ?_⟩
  intro δ h ρ a c g m n N L x v Y Z S y w f z e G γ
    hδ hδd hhε hhζ hA hC hH hρlow hρup hlen hbr hlarge
  have hδ100 : δ ≤ 1 / 100 := hδd.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hdall := hδd.trans (min_le_right _ _)
  have hsmall := h₁ δ hδ (hdall.trans (min_le_left _ _))
  have hbudget0 := h₂ δ hδ ((hdall.trans (min_le_right _ _)).trans (min_le_left _ _))
  have hρsmall := h₃ δ hδ ((hdall.trans (min_le_right _ _)).trans (min_le_right _ _))
  have hbudget : 4 * δ ^ ε ≤ δ ^ h := by
    calc
      _ = (4 * δ ^ (ε / 2)) * δ ^ (ε / 2) := by
        rw [mul_assoc, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ 1 * δ ^ (ε / 2) :=
        mul_le_mul_of_nonneg_right hbudget0 (Real.rpow_nonneg hδ.le _)
      _ ≤ δ ^ h := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhε
  have hc : 0 < c := hδ.trans_le (hH.1.trans (hH.2.1.trans hH.2.2.1))
  have h4 : 4 * δ ≤ c := by
    have hdc : δ ≤ ρ * c := hH.1.trans hH.2.1
    have h4ρ : 4 * ρ ≤ 1 := (mul_le_mul_of_nonneg_left hρup (by norm_num)).trans hρsmall
    nlinarith
  have hm : 0 < m := by
    have : 0 < m * c ^ 2 := (Real.rpow_pos_of_pos hδ _).trans_le hlarge
    exact pos_of_mul_pos_left this (sq_nonneg _)
  exact stage_three_of_large_grain_level hδ hδ1 (by linarith) hbudget h4 hm
    (Real.rpow_nonneg hδ.le _) (fun i => (hA.2.1 i).1) (fun i => (hA.2.1 i).2.2.2)
    hA.2.2.2.2.1 hC hH hρlow hρup hlen hbr
    (grain_coefficient_le_of_power hδ hδ1 hhζ hsmall hlarge)

end WangZahlLot.Obl.wz_broad_grains_improvement
