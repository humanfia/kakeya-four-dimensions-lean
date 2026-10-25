import Submission.Obl.k4_wide_three_layer_scalar_inputs.KeyOffsets
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.ShortKey

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MeasureTheory Finset
open Inherited.Native Inherited.Core Inherited.MatchGML2D

noncomputable section

open scoped Classical in
/-- Count finer predictors through their earlier marginal floors on the
same coarse short key. The current source/target intersections supply only
the offset and freezing tests, and need no separate mass floor. -/
theorem count_frozen_sheet_offsets {α : Type} [MeasurableSpace α]
    {μ ρs : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (hρμ : ρs ≤ μ)
    {η R₀ d N K r v' Rc s₁ t₀ q m ζ Lv a Xb K₁ T B W₁ W₂ δ Mst A w : ℝ}
    {κ : Fin 3 → ℤ}
    (hn : KeyNum N K d r v' Rc s₁ t₀ q m ζ Lv a Xb K₁ B W₁ W₂ δ Mst A w η R₀ κ)
    (hcap : ∀ s', 0 ≤ s' → s' ≤ Rc → JointCapAt μ π b N K d r s' v')
    (hT : T = q * N ^ (-v') * m * a ^ d * (π {v | ⌊v / N ^ (-v')⌋ = κ 0}).toReal)
    (hTpos : 0 < T) (hπfin : π {v | ⌊v / N ^ (-v')⌋ = κ 0} ≠ ⊤)
    (hnull : ρs (horizSet b ζ)ᶜ = 0)
    {ι : Type} (C : ι → Set α) (Gi : ι → MvPolynomial (Fin 2) ℝ)
    (G₀ : MvPolynomial (Fin 2) ℝ) (hG₀ : G₀.totalDegree ≤ 2)
    (hGi : ∀ i, (Gi i).totalDegree ≤ 2)
    (hC : ∀ i, MeasurableSet (C i))
    (hdisj : ∀ i i', i ≠ i' → Disjoint (C i) (C i'))
    (hfl : ∀ i, ENNReal.ofReal (T / K₁) ≤ ρs (C i ×ˢ Icc t₀ (t₀ + q)))
    (hlab : ∀ i, ∀ l ∈ C i, |b l 4 + b l 0| ≤ ζ →
      slotKey b (N ^ (-v')) m t₀ l = κ ∧ ∀ τ ∈ Icc (0 : ℝ) 1,
        |b l 2 + (t₀ + q * τ) * b l 5| ≤ Xb ∧
        |b l 2 + (t₀ + q * τ) * b l 5 -
          a * quad2 (sheetKeyCoeff (Gi i) a (N ^ (-v')) m q t₀ κ) τ
            (sliceY b m t₀ l)| ≤ a * W₁)
    (hFB : ∀ i e, |sheetKeyCoeff (Gi i) a (N ^ (-v')) m q t₀ κ e| ≤ B)
    {coarseA H : ℝ} (haA : a ≤ coarseA) (hH : 0 ≤ H)
    (hMst : Mst ≤ 16 * H * coarseA / a)
    (J : Finset ι) (offset : ι → ℝ)
    (hoff : ∀ i ∈ J, |offset i| ≤ H * coarseA)
    (hfreeze : ∀ i ∈ J, ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t₀ + q * τ, domY (N ^ (-v')) m q κ τ y] (Gi i - G₀) - offset i| ≤ H * a) :
    (J.card : ℝ) ≤ A * ((16 * H * coarseA / a) / δ) ^ d ∧
      ((J.image offset).card : ℝ) ≤ A * ((16 * H * coarseA / a) / δ) ^ d := by
  classical
  have hball : ∀ i ∈ J, ∀ e,
      |sheetKeyCoeff (Gi i) a (N ^ (-v')) m q t₀ κ e -
        sheetKeyCoeff G₀ a (N ^ (-v')) m q t₀ κ e| ≤ 16 * H * coarseA / a := by
    intro i hi e
    have hnorm : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
        |MvPolynomial.eval ![t₀ + q * τ, domY (N ^ (-v')) m q κ τ y] (Gi i) -
          MvPolynomial.eval ![t₀ + q * τ, domY (N ^ (-v')) m q κ τ y] G₀| ≤ 2 * H * coarseA := by
      intro τ hτ y hy
      have hv := hfreeze i hi τ hτ y hy
      simp only [map_sub] at hv
      have hc : |MvPolynomial.eval ![t₀ + q * τ, domY (N ^ (-v')) m q κ τ y] (Gi i) -
          MvPolynomial.eval ![t₀ + q * τ, domY (N ^ (-v')) m q κ τ y] G₀| ≤ H * a + H * coarseA := by
        have h := abs_add_le
          (MvPolynomial.eval ![t₀ + q * τ, domY (N ^ (-v')) m q κ τ y] (Gi i) -
            MvPolynomial.eval ![t₀ + q * τ, domY (N ^ (-v')) m q κ τ y] G₀ - offset i)
          (offset i)
        rw [sub_add_cancel] at h
        exact h.trans (add_le_add hv (hoff i hi))
      exact hc.trans (by nlinarith [mul_le_mul_of_nonneg_left haA hH])
    have h := sheet_key_difference_coefficients (hGi i) hG₀ hn.ha κ hnorm e
    convert h using 1 <;> ring
  have hcount := slot_count hb hρμ hn hcap hT hTpos hπfin hnull C
    (fun i => sheetKeyCoeff (Gi i) a (N ^ (-v')) m q t₀ κ) hC hdisj hfl hn.hW₁M hlab hFB
    (sheetKeyCoeff G₀ a (N ^ (-v')) m q t₀ κ) (16 * H * coarseA / a) hMst J hball
  refine ⟨hcount, ?_⟩
  exact (by exact_mod_cast Finset.card_image_le : ((J.image offset).card : ℝ) ≤ J.card).trans hcount

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
