-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormBridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormFamily
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormAfterZoom

/-!
# From the zoomed dense family to the body of `Grains σ`

The output of the zoom core is an o060-`Dense`/`Weak` family at `δ' = lam δ` (the zoomed pieces
`zx`, `zv`, `zY`). The separated cover refinement (o060) gives a subfamily that is `Dense` and
`Strong`, i.e. a `Family` that is `Separated`; its shadings lie in the zoomed union and inherit
the plane-map precision, so `grains_body_after_zoom` applies.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal

theorem family_of_dense {η δ : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : WangZahlLot.Obl.wz_separated_cover_refinement.Dense η δ n x v Y) :
    Family η δ n x v Y := h

theorem separated_of_strong {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : WangZahlLot.Obl.wz_separated_cover_refinement.Strong η δ n x v) :
    Separated η δ n x v := by
  intro r hr1 hr2
  obtain ⟨ρ, h1, h2, h3, k, hk, z, w, ⟨c1, c2, c3, c4, c5, c6⟩, hs⟩ := h r hr1 hr2
  exact ⟨ρ, h1, h2, h3, k, hk, z, w, c1, c2, c3, c4, c5, c6, hs⟩

theorem zoom_injective {c : Space} {lam : ℝ} (hlam : lam ≠ 0) {p q : Space}
    (h : zoom c lam p = zoom c lam q) : p = q := by
  rw [← zoom_inv_zoom (c := c) hlam p, h, zoom_inv_zoom hlam q]

/-- **The end of the normalization.** A zoomed dense/weak family (output of the zoom core) and
the separated cover refinement at `ε` give the body of `Grains σ` at `δ' = lam δ`. -/
theorem zoomed_grains_body {σ η δ lam δ' L C η₁ ε ηo d1 : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} {f : ℝ → ℝ} {V : Space → Space} {c : Space} {Q : Finset (Fin n)}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hδ : 0 < δ) (hlam : 1 ≤ lam) (hδ' : δ' = lam * δ)
    (hL : 0 ≤ L) (hLlam : 3 * L ≤ lam) (hC : 0 ≤ C)
    (hFam : Family η δ n x v Y)
    (hf : ∀ a b : ℝ, dist (f a) (f b) ≤ L * dist a b)
    (hslice : ∀ z : ℝ, z ∈ Icc (-1) 1 → Covering δ (1 - σ) C (projectedSlice f (⋃ i, Y i) z))
    (hVu : ∀ p, p ∈ (⋃ i, Y i) → ‖V p‖ = 1)
    (hVp : ∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ)
    (hVL : ∀ p, p ∈ (⋃ i, Y i) → ∀ q, q ∈ (⋃ i, Y i) → dist (V p) (V q) ≤ L * dist p q)
    (hloc : ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y i) →
      Covering ρ (1 - σ) C
        ((fun q : Space => inner ℝ (V p) q) '' ((⋃ i, Y i) ∩ ball p (Real.sqrt ρ))))
    (hD : WangZahlLot.Obl.wz_separated_cover_refinement.Dense η₁ δ' Q.card (zx c lam x v Q)
      (zv v Q) (zY c lam δ x v Y Q))
    (hW : WangZahlLot.Obl.wz_separated_cover_refinement.Weak η₁ δ' Q.card (zx c lam x v Q)
      (zv v Q))
    (hR : ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        WangZahlLot.Obl.wz_separated_cover_refinement.Dense η₁ δ n x v Y →
        WangZahlLot.Obl.wz_separated_cover_refinement.Weak η₁ δ n x v →
        ∃ (m : ℕ) (a : Fin m → Fin n), Function.Injective a ∧
          WangZahlLot.Obl.wz_separated_cover_refinement.Dense ε δ m (fun i => x (a i))
            (fun i => v (a i)) (fun i => Y (a i)) ∧
          WangZahlLot.Obl.wz_separated_cover_refinement.Strong ε δ m (fun i => x (a i))
            (fun i => v (a i)))
    (hd1 : δ' ≤ d1) (h100 : δ' ≤ 1 / 100)
    (hεo : ε ≤ ηo) (hfam : δ' ^ ηo ≤ δ' ^ ε / 2)
    (hCo : C ≤ δ' ^ (-ηo)) (hvolC : 32 * C ≤ δ' ^ (-ηo)) :
    ∃ (m : ℕ) (x' v' : Fin m → Space) (Y'' : Fin m → Set Space),
      Family ηo δ' m x' v' Y'' ∧ Separated ηo δ' m x' v' ∧ (∀ i, IsCompact (Y'' i)) ∧
      volume (⋃ i, Y'' i) ≤ ENNReal.ofReal (δ' ^ (σ - ηo)) ∧
      ∃ (g : ℝ → ℝ) (P : Space → Space), LipschitzWith 1 g ∧
        (∀ z : ℝ, z ∈ Icc (-1) 1 →
          Covering δ' (1 - σ) (δ' ^ (-ηo)) (projectedSlice g (⋃ i, Y'' i) z)) ∧
        LipschitzWith 1 P ∧ (∀ p, p ∈ (⋃ i, Y'' i) → ‖P p‖ = 1) ∧
        (∀ i p, p ∈ Y'' i → |inner ℝ (v' i) (P p)| ≤ δ') ∧
        (∀ ρ : ℝ, δ' ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y'' i) →
          Covering ρ (1 - σ) (δ' ^ (-ηo))
            ((fun q : Space => inner ℝ (P p) q) '' ((⋃ i, Y'' i) ∩ ball p (Real.sqrt ρ)))) := by
  subst hδ'
  have hlam0 : 0 < lam := by linarith
  have hlamne : lam ≠ 0 := hlam0.ne'
  have hδ'0 : 0 < lam * δ := by positivity
  have hlδ : lam * δ ≤ 1 := by linarith
  obtain ⟨m, a, -, hD', hS'⟩ := hR (lam * δ) hδ'0 hd1 h100 _ _ _ _ hD hW
  have hEb : (⋃ i, Y i) ⊆ ball 0 1 := by
    obtain ⟨-, -, hball, -, -, hYT, -⟩ := hFam
    exact iUnion_subset fun i => (hYT i).trans (hball i)
  have hY'E : ∀ j, (fun i => zY c lam δ x v Y Q (a i)) j ⊆ zoom c lam '' (⋃ i, Y i) := by
    intro j
    simp only [zY]
    exact image_mono (inter_subset_left.trans (subset_iUnion _ _))
  have hprec : ∀ j, ∀ q ∈ (⋃ i, Y i), zoom c lam q ∈ (fun i => zY c lam δ x v Y Q (a i)) j →
      |inner ℝ ((fun i => zv v Q (a i)) j) (V q)| ≤ lam * δ := by
    intro j q _ hq
    simp only [zY] at hq
    obtain ⟨p, ⟨hpY, -⟩, hpq⟩ := hq
    obtain rfl : p = q := zoom_injective hlamne hpq
    simp only [zv]
    calc |inner ℝ (v (WangZahlLot.Obl.wz_separated_cover_refinement.enumerate Q (a j))) (V p)|
        ≤ δ := hVp _ _ hpY
      _ ≤ lam * δ := by nlinarith
  obtain ⟨Y'', h1, h2, h3, h4, h5⟩ := grains_body_after_zoom hσ0 hσ1 hδ hlam hlδ hL hLlam hC hEb
    hf hslice hVu hVL hloc (family_of_dense hD') (separated_of_strong hS') hY'E hprec hεo hfam
    hCo hvolC
  exact ⟨m, _, _, Y'', h1, h2, h3, h4, h5⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
