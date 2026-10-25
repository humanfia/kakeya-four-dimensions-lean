/- Retained from this obligation, o255, branch x0901 at commit 0f8ba410.
   Earlier source attributions in this file are preserved. -/
import Submission.Obl.k4_general_parent_narrow_contact_transfer.Refine

/-!
# Wide or narrow, at a moderate mesh

The dichotomy of `Dichotomy.lean`, with ordinary preparation always requested
at the moderate mesh exponent `m₀ = (L₀ + 1) a` and wide outputs refined to
the requested mesh by `LayerOutput.refine`.  The narrow alternative therefore
comes with the mesh `N^(-(L₀+1) a)`, a fixed multiple of the depth.  This is
what the narrow argument needs: its horizontal cells must be finer than the
projected intercept/velocity mesh, and true labels of that size exist below
`U` only for moderate meshes.
-/

namespace Submission.Obl.k4_general_parent_narrow_contact_transfer

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

namespace Model

variable {α : Type} [MeasurableSpace α]

theorem candidates_of_layers_moderate (cfg : Model α) (hv : Valid cfg)
    (h0 : Layers cfg false) (h1 : Layers cfg true → cfg.Candidates)
    (Λ : ℝ → ℝ) (hΛ : ∀ L, 2 < L → L + 2 ≤ cfg.S * Λ L)
    (core : ∀ L₀ : ℝ, 2 < L₀ →
      (∀ a : ℝ, 0 < a → 2 * a < cfg.U → ∀ D : Finset ℝ, (∀ s ∈ D, a ≤ s ∧ s ≤ 2 * a) →
        ∀ m : ℝ, L₀ * a < m → LayerOutput cfg false L₀ a D m) →
      ∀ a s : ℝ, 0 < a → Λ L₀ * a < cfg.U → a ≤ s → s ≤ 2 * a →
      ∀ (τ : ℕ → ℕ) (H : ℕ → ℝ) (ρ' : ℕ → Measure (α × ℝ)) (β : ℕ → ℝ → ℝ)
        (n' : ℕ → ℝ → ℕ) (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
        (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
        (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
        (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),
        NarrowWitness cfg L₀ a ((L₀ + 1) * a) s τ H ρ' β n' C tag u v G → cfg.Candidates) :
    cfg.Candidates := by
  by_contra hG
  obtain ⟨L₀, hL₀, hlay⟩ := (layers_iff cfg false).1 h0
  have hlay' : ∀ a : ℝ, 0 < a → 2 * a < cfg.U → ∀ D : Finset ℝ,
      (∀ s ∈ D, a ≤ s ∧ s ≤ 2 * a) → ∀ m : ℝ, L₀ * a < m →
      LayerOutput cfg false L₀ a D m := fun a ha h2 D hD m hm =>
    hlay a ha (by simpa using h2) D hD m hm
  have hN : ∀ k, 2 ≤ cfg.N k := hv.scale
  have hS1 := hv.palette_le_one
  have hSpos := hv.palette_pos
  have hΛS := hΛ L₀ hL₀
  have hΛ' : L₀ + 2 ≤ Λ L₀ := by
    by_contra hc
    push Not at hc
    have : cfg.S * Λ L₀ ≤ Λ L₀ := by
      have hΛpos : 0 ≤ Λ L₀ := by nlinarith
      nlinarith
    linarith
  apply hG
  apply h1
  refine (layers_iff cfg true).2 ⟨Λ L₀, by linarith, ?_⟩
  intro a ha haU D hD m hm
  simp only [ite_true] at haU
  have hm₀pos : 0 < (L₀ + 1) * a := by positivity
  have hm₀m : (L₀ + 1) * a ≤ m := by nlinarith
  have hSm : (L₀ + 1) * a < cfg.S * m := by
    have h1 : (L₀ + 2) * a ≤ cfg.S * Λ L₀ * a := mul_le_mul_of_nonneg_right hΛS ha.le
    have h2 : cfg.S * (Λ L₀ * a) < cfg.S * m := mul_lt_mul_of_pos_left hm hSpos
    nlinarith
  apply LayerOutput.refine cfg hv hm₀pos hm₀m hSm
  obtain ⟨τ, hτ, H, hH, hHsub, ρ', β, n', C, tag, u, v, G, hρ', hsl⟩ :=
    hlay' a ha (by nlinarith) D hD ((L₀ + 1) * a) (by nlinarith)
  by_cases hnar : ∃ s ∈ D, ∃ e : ℝ, 0 < e ∧
      ∃ᶠ k in Filter.atTop, cfg.N (τ k) ^ e * β k s < cfg.N (τ k) ^ (-cfg.ℓ * s)
  · exfalso
    obtain ⟨s, hs, e, he, hfreq⟩ := hnar
    exact hG (core L₀ hL₀ hlay' a s ha haU (hD s hs).1 (hD s hs).2
      τ H ρ' β n' C tag u v G ⟨hτ, hH, hHsub, hρ', fun k => hsl k s hs, e, he, hfreq⟩)
  · push Not at hnar
    have hNpos : ∀ k, 0 < cfg.N k := fun k => lt_of_lt_of_le two_pos (hN k)
    have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => le_trans one_le_two (hN k)
    set f : ℝ → ℕ → ℝ := fun s k => max 1 (cfg.N (τ k) ^ (-cfg.ℓ * s) / β k s) with hf
    have hf1 : ∀ s k, 1 ≤ f s k := fun s k => le_max_left _ _
    have hprod1 : ∀ k, 1 ≤ ∏ s ∈ D, f s k :=
      fun k => Finset.one_le_prod₀ fun s _ => hf1 s k
    have hprodge : ∀ k, ∀ s ∈ D, f s k ≤ ∏ s ∈ D, f s k := by
      intro k s hs
      rw [← Finset.mul_prod_erase D (fun s => f s k) hs]
      exact le_mul_of_one_le_right (le_trans zero_le_one (hf1 s k))
        (Finset.one_le_prod₀ fun s _ => hf1 s k)
    set H' : ℕ → ℝ := fun k => H k * ∏ s ∈ D, f s k with hH'
    have hHH' : ∀ k, H k ≤ H' k := fun k =>
      le_mul_of_one_le_right (le_trans zero_le_one (hH k).1) (hprod1 k)
    refine ⟨τ, hτ, H', fun k => ⟨(hH k).1.trans (hHH' k), (hH k).2.trans (hHH' k)⟩,
      ?_, ρ', β, n', C, tag, u, v, G, fun k => ⟨(hρ' k).1, ?_⟩, ?_⟩
    · have hsubH : Subpow (fun k => cfg.N (τ k)) H := hHsub
      have hsubf : ∀ s ∈ D, Subpow (fun k => cfg.N (τ k)) (f s) := by
        intro s hs e he
        filter_upwards [hnar s hs e he] with k hk
        have hβ : 0 < β k s := (hsl k s hs).1
        refine max_le (Real.one_le_rpow (hN1 _) he.le) ?_
        rw [div_le_iff₀ hβ]
        exact hk
      have := Subpow.mul (fun k => hNpos (τ k))
        (fun k => le_trans zero_le_one (hprod1 k)) hsubH
        (Subpow.finset_prod D (fun k => hN1 (τ k))
          (fun s k => le_trans zero_le_one (hf1 s k)) hsubf)
      exact this
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hρ' k).2
      exact inv_anti₀ (lt_of_lt_of_le one_pos (hH k).1) (hHH' k)
    · intro k s hs
      have hsk := hsl k s hs
      have hβ : 0 < β k s := hsk.1
      refine slice_widen cfg hsk (hNpos _) (hH k).1 (hHH' k) ?_
      have h1 : cfg.N (τ k) ^ (-cfg.ℓ * s) ≤ f s k * β k s := by
        rw [← div_le_iff₀ hβ]
        exact le_max_right _ _
      calc cfg.N (τ k) ^ (-cfg.ℓ * s) ≤ f s k * β k s := h1
        _ ≤ H' k * β k s := by
          apply mul_le_mul_of_nonneg_right _ hβ.le
          calc f s k ≤ ∏ s ∈ D, f s k := hprodge k s hs
            _ ≤ H k * ∏ s ∈ D, f s k :=
              le_mul_of_one_le_left (le_trans zero_le_one (hprod1 k)) (hH k).1

end Model

end

end Submission.Obl.k4_general_parent_narrow_contact_transfer
