/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/Sequence.lean.
Earlier source credits are retained below. -/

import Submission.Obl.k4_scalar_heavy_intercept_selection.Certificates
import Submission.Obl.k4_scalar_heavy_intercept_selection.ScalarHeavy
import Submission.Obl.k4_scalar_heavy_intercept_selection.SlowPalette

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open Set MeasureTheory Filter MvPolynomial
open Submission.Lib.K4ContinuousKakeya

noncomputable section

def ScalarPureCapsAt (N K d R : ℝ) (ρ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) : Prop :=
  ∀ r s : ℝ, R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R →
    ∀ (q : Fin 2 → ℤ) (j : ℤ),
      ρ {p | (fun i => (⌊(![p.2, Cons.yL p.1 p.2] : Fin 2 → ℝ) i / (N ^ (-r))⌋ : ℤ)) = q ∧
        (⌊Cons.xL p.1 p.2 / (N ^ (-s))⌋ : ℤ) = j} ≤
          ENNReal.ofReal (K * N ^ (-2 * r - d * s))

/-- Close the heavy side along the original sequence. One slow compact
range supplies both the packet witnesses and the angular breadth, and
its inverse angular radius remains subpower. -/
theorem heavy_sequence_of_intercepts
    (N K0 Hf Hp : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK0 : (∀ k, 1 ≤ K0 k) ∧ ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, K0 k ≤ N k ^ e)
    (hHf : (∀ k, 1 ≤ Hf k) ∧ ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, Hf k ≤ N k ^ e)
    (hHp : (∀ k, 1 ≤ Hp k) ∧ ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, Hp k ≤ N k ^ e)
    {d κ S Z B C : ℝ} (hd : 0 ≤ d) (hd₁ : d < 1) (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hS : 0 < S) (hZ : 10 ≤ Z) (hB : Z + 10 ≤ B) (hC : 0 < C) (hMK : FiniteMK 2 C)
    (Df Dp : ℕ) (W : ℕ → ℕ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ) (T n : ℕ → ℝ → ℕ)
    (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k))
    (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ)))
    (hPure : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ g : Fin (W k),
      ScalarPureCapsAt (N k) (K0 k) d R (ρ k g))
    (hFP : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∃ (i : Fin (n k 1))
      (μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z : Fin 2 → ℝ)
      (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (P : MvPolynomial (Fin 2) ℝ)
      (c : (ℕ × (Fin 5 → ℝ)) → ℝ),
      Cons.FieldAt (N k) (Hf k) d κ S Z B R Df (ν k (γ k 1 i)) (π k (γ k 1 i))
        (ρ k (γ k 1 i)) (A k 1 i) (T k 1) (j k 1 i) μ z 𝒯 ∧
      Cons.PotAt (N k) (Hp k) (κ * (1 - d) / 1000) Dp (T k 1) (j k 1 i) μ z P c) :
    ∃ L : ℕ → ℝ,
      ((∀ k, 1 ≤ L k) ∧ ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, L k ≤ N k ^ e) ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∃ (i : Fin (n k 1))
        (σ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z : Fin 2 → ℝ) (P : MvPolynomial (Fin 2) ℝ),
        HeavyAt (N k) (L k) d κ S Z B R (κ * (1 - d) / 1000) Dp (T k 1) (j k 1 i)
          (ν k (γ k 1 i)) (π k (γ k 1 i)) (ρ k (γ k 1 i)) σ (A k 1 i) z P := by
  let H := fun k => max (K0 k) (max (Hf k) (Hp k))
  have hH := Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hK0
    (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hHf hHp)
  have hK0H (k : ℕ) : K0 k ≤ H k := le_max_left _ _
  have hHfH (k : ℕ) : Hf k ≤ H k := (le_max_left _ _).trans (le_max_right _ _)
  have hHpH (k : ℕ) : Hp k ≤ H k := (le_max_right _ _).trans (le_max_right _ _)
  have hN₁ (k : ℕ) : 1 ≤ N k := by linarith [hN k]
  let cstar := κ * (1 - d) / 1000
  have hcstar : 0 < cstar := by
    have hdim : 0 < 1 - d := by linarith
    dsimp [cstar]
    positivity
  have hcκ : cstar ≤ κ / 1000 := by
    dsimp [cstar]
    nlinarith [mul_nonneg hκ.le hd]
  have hc₁ : cstar ≤ 1 := by linarith
  let Requirements : ℕ → ℕ → Prop := fun m k =>
    (∃ (i : Fin (n k 1)) (μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z : Fin 2 → ℝ)
      (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (P : MvPolynomial (Fin 2) ℝ)
      (c : (ℕ × (Fin 5 → ℝ)) → ℝ),
      Cons.FieldAt (N k) (Hf k) d κ S Z B ((m : ℝ) + 2) Df (ν k (γ k 1 i)) (π k (γ k 1 i))
        (ρ k (γ k 1 i)) (A k 1 i) (T k 1) (j k 1 i) μ z 𝒯 ∧
      Cons.PotAt (N k) (Hp k) cstar Dp (T k 1) (j k 1 i) μ z P c) ∧
    ∀ g : Fin (W k), ScalarPureCapsAt (N k) (K0 k) d ((m : ℝ) + 2) (ρ k g)
  have hReq (m : ℕ) : ∀ᶠ k in atTop, Requirements m k := by
    have hr : (1 : ℝ) < (m : ℝ) + 2 := by have hm := Nat.cast_nonneg (α := ℝ) m; linarith
    filter_upwards [hFP _ hr, hPure _ hr] with k hp hc
    exact ⟨hp, hc⟩
  obtain ⟨J, hJmono, hJ, hQ, hSlow⟩ := exists_slow_palette_scale N H hN₁ hNt hH.1 hH.2
    S 14000 1 hS (by norm_num) (by norm_num) 2 Requirements hReq
  let Q := fun k => N k ^ (1 / ((J k : ℝ) + 2))
  let L := fun k => heavyOutputLoss C (H k) (Q k)
  have hL := heavy_output_loss_subpower N H Q hN₁ hNt hH hQ hC
  let polyConst : ℝ := (2 : ℝ) * (Dp + 1 : ℕ) * (2 : ℝ) ^ Dp * (Dp : ℝ)
  have hPoly : 0 ≤ polyConst := by dsimp [polyConst]; positivity
  have hMargins := eventually_heavy_packet_margins N H hN₁ hNt hH.1 hH.2
    hκ hκ₁ hcstar hcκ hZ hB hPoly (Dp + 1)
  have hHN : ∀ᶠ k in atTop, H k ≤ N k := by
    filter_upwards [hH.2 1 (by norm_num)] with k hk
    simpa only [Real.rpow_one] using hk
  refine ⟨L, hL, ?_⟩
  intro R hR
  filter_upwards [hSlow, hMargins, hHN, eventually_radius_ge J hJ R,
    eventually_radius_ge J hJ (Z + κ + 1)] with k hs hm hHN hCover hMeshCover
  let Rf : ℝ := (J k : ℝ) + 2
  let r₀ : ℝ := 1 / Rf
  let η : ℝ := N k ^ (-r₀)
  have hNk : 1 < N k := by linarith [hN k]
  have hNk₀ : 0 < N k := by linarith
  have hHk : 1 ≤ H k := hH.1 k
  have hHk₀ : 0 < H k := by linarith
  have hHfk₀ : 0 < Hf k := by linarith [hHf.1 k]
  have hη : 0 < η := Real.rpow_pos_of_pos hNk₀ _
  have hJ₀ : (0 : ℝ) ≤ (J k : ℝ) := Nat.cast_nonneg _
  have hRf₂ : 2 ≤ Rf := by dsimp [Rf]; linarith
  have hRf₁ : 1 < Rf := by linarith
  have hr₀ : Rf⁻¹ ≤ r₀ := by simp only [r₀, one_div, le_refl]
  have hr₁ : r₀ ≤ Rf := by
    have ht : r₀ ≤ 1 := (div_le_iff₀ (show 0 < Rf by linarith)).2 (by linarith)
    exact ht.trans hRf₁.le
  have hηQ : η⁻¹ = Q k := by
    dsimp [η, Q, r₀, Rf]
    rw [Real.rpow_neg hNk₀.le, inv_inv]
  have hsmall : 14000 * H k ^ 2 * N k ^ (-S * r₀) ≤ 1 := by
    simpa only [r₀, Rf, one_div, div_eq_mul_inv, one_mul] using hs.2
  have hNow := hs.1 (J k) le_rfl
  have hOriginal := hNow.2
  obtain ⟨i, μ, z, 𝒯, P, c, hField, hPot⟩ := hNow.1
  let h := ((2 : ℝ) ^ T k 1)⁻¹
  have hFieldCopy := hField
  rcases hFieldCopy with ⟨_, _, _, _, hlo, hup, hh, hTail⟩
  have hloH : N k ^ (-κ) / H k ≤ h :=
    (div_le_div_of_nonneg_left (Real.rpow_nonneg hNk₀.le _) hHfk₀ (hHfH k)).trans hlo
  have hupH : h ≤ H k * N k ^ (-κ) :=
    hup.trans (mul_le_mul_of_nonneg_right (hHfH k) (Real.rpow_nonneg hNk₀.le _))
  obtain ⟨hassign, herr, hfine, hcoarse, hjointlo, hjointhi, hξ₁⟩ :=
    heavy_packet_scale_inequalities (Dp + 1) (hN₁ k) hHk hh hcstar (by linarith)
      hPoly hloH hupH hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2.1 hm.2.2.2.2.2
  have hRect := original_rectangle_at_target_mesh (ρ k (γ k 1 i))
    (fun p => (![p.2, Cons.yL p.1 p.2] : Fin 2 → ℝ)) (fun p => Cons.xL p.1 p.2)
    hNk hHk₀ hHN hh hκ.le (by linarith : 2 ≤ Z) hRf₂ hMeshCover hcstar.le hc₁
    (hK0H k) hloH hupH (hOriginal (γ k 1 i))
  let KNN : NNReal := NNReal.mk (H k) hHk₀.le
  have hKNN : 1 ≤ KNN := by exact_mod_cast hHk
  obtain ⟨σ, P', hSelected⟩ : ∃ (σ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
      (P' : MvPolynomial (Fin 2) ℝ),
      SelectedAt (N k) (H k) C η d Z B Rf cstar Dp (T k 1) (j k 1 i)
        (ν k (γ k 1 i)) (π k (γ k 1 i)) (A k 1 i) μ σ z P' := by
    exact scalar_heavy_packet hNk (hHf.1 k) KNN hKNN (hHfH k) (hHpH k) hC hMK Df Dp
      (T k 1) (j k 1 i) (ν k (γ k 1 i)) (π k (γ k 1 i)) (ρ k (γ k 1 i)) μ (A k 1 i)
      z 𝒯 P c hField hPot hr₀ hr₁ hsmall hassign hξ₁ herr hfine hcoarse hjointlo hjointhi hRect
  have hOut := heavy_output_loss_bounds hC hHk (hQ.1 k)
  have hMassLoss : 13478400 * C * H k ^ 6 * (H k + 1) ^ 2 * η⁻¹ ≤ L k := by
    rw [hηQ]
    exact hOut.2.2.2.2
  refine ⟨i, σ, z, P', ?_⟩
  exact heavy_certificate_of_selected_packet hNk (hHf.1 k) hHk (hHfH k) hC hη hcstar.le
    (by linarith : 0 < R) hCover hOut.2.1 hOut.2.2.1 hOut.2.2.2.1 hMassLoss Df Dp
    (T k 1) (j k 1 i) (ν k (γ k 1 i)) (π k (γ k 1 i)) (ρ k (γ k 1 i)) μ σ
    (A k 1 i) z 𝒯 P' hField hSelected

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
