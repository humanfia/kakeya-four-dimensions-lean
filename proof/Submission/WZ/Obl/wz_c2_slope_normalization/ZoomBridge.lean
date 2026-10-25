-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.ZoomBridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomMain

/-!
# The normalization in the flat frozen shape

The frozen statements write the separated covers with seven flat conjuncts and the example
shape with an arbitrary slope clause `Q η δ n Y f`.  `ExF Q σ` is that shape with the named
conditions; `normalizeF` is the normalization in this shape, ready to be matched against a
frozen statement by `subst` and unfolding.
-/

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

/-- The separated all-scale covers with the seven conjuncts of the frozen statement. -/
def StrongFlat (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∃ ρ : ℝ, r ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * r ∧
    ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → Space,
      (∀ j, ‖w j‖ = 1) ∧
      (∀ j j', j ≠ j' → volume (Tube ρ (z j) (w j) ∩ Tube ρ (z j') (w j')) ≤
        (1 / 2 : ENNReal) * volume (Tube ρ (z j) (w j))) ∧
      (∀ i, ∃! j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
      (∀ j, ∃ i, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
      (∀ j j', (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ) ≤
        δ ^ (-η) * (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j') (w j')} : ℝ)) ∧
      (∀ j, ∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal ((Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) ∧
          Tube δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η) *
          (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ)) * volume W) ∧
      (∀ i j j', Tube δ (x i) (v i) ⊆ Dilate ρ (z j) (w j) →
        Tube δ (x i) (v i) ⊆ Dilate ρ (z j') (w j') → j = j')

theorem strong_of_flat {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : StrongFlat η δ n x v) : Strong η δ n x v := by
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, h1, h2, h3, h4, h5, h6, h7⟩ := h r hδr hr1
  exact ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩

theorem flat_of_strong {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : Strong η δ n x v) : StrongFlat η δ n x v := by
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := h r hδr hr1
  exact ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, h1, h2, h3, h4, h5, h6, h7⟩

/-- The frozen example shape with an arbitrary slope clause. -/
def ExF (Q : ℝ → ℝ → (n : ℕ) → (Fin n → Set Space) → (ℝ → ℝ) → Prop) (σ : ℝ) : Prop :=
  ∀ η d₀ : ℝ, 0 < η → 0 < d₀ → ∃ δ : ℝ, 0 < δ ∧ δ ≤ d₀ ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Dense η δ n x v Y ∧ StrongFlat η δ n x v ∧ (∀ i, IsCompact (Y i)) ∧
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) ∧
      ∃ (f : ℝ → ℝ) (P : Space → Space), Q η δ n Y f ∧
        (∀ z : ℝ, z ∈ Icc (-1) 1 → Assouad δ (1 - σ) (δ ^ (-η)) (ProjectedSlice f (⋃ i, Y i) z)) ∧
        LipschitzWith 1 P ∧ (∀ p, p ∈ (⋃ i, Y i) → ‖P p‖ = 1) ∧
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (P p)| ≤ δ) ∧
        (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y i) →
          Assouad ρ (1 - σ) (δ ^ (-η))
            ((fun q : Space => inner ℝ (P p) q) '' ((⋃ i, Y i) ∩ ball p (Real.sqrt ρ))))

/-- The slope clause of the weak examples. -/
def QW (η δ : ℝ) (n : ℕ) (_Y : Fin n → Set Space) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ z : ℝ, |f z| ≤ δ ^ (-η) ∧ |deriv f z| ≤ δ ^ (-η) ∧
    |deriv (deriv f) z| ≤ δ ^ (-η)

/-- The slope clause of the frozen conclusion. -/
def QC (_η _δ : ℝ) (n : ℕ) (_Y : Fin n → Set Space) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Icc (-1) 1 → |f z| ≤ 1 ∧ |deriv f z| ≤ 1 ∧
    |deriv (deriv f) z| ≤ 1

theorem weak_of_exF {σ : ℝ} (h : ExF QW σ) : WeakSmoothExamples σ := by
  intro η d₀ hη hd₀
  obtain ⟨δ, hδ, hδd, hδ1, n, x, v, Y, hD, hS, hC, hV, f, P, hf, hg, hP, hn, ho, hl⟩ :=
    h η d₀ hη hd₀
  exact ⟨δ, hδ, hδd, hδ1, n, x, v, Y, ⟨hD, strong_of_flat hS, hC, hV⟩, f, P, hf,
    ⟨hg, hP, hn, ho, hl⟩⟩

theorem exF_of_smooth {σ : ℝ} (h : SmoothExamples σ) : ExF QC σ := by
  intro η d₀ hη hd₀
  obtain ⟨δ, hδ, hδd, hδ1, n, x, v, Y, ⟨hD, hS, hC, hV⟩, f, P, hf, ⟨hg, hP, hn, ho, hl⟩⟩ :=
    h η d₀ hη hd₀
  exact ⟨δ, hδ, hδd, hδ1, n, x, v, Y, hD, flat_of_strong hS, hC, hV, f, P, hf, hg, hP, hn,
    ho, hl⟩

/-- The normalization in the flat frozen shape. -/
theorem normalizeF {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (h : ExF QW σ) : ExF QC σ :=
  exF_of_smooth (normalize hσ0 hσ1 (weak_of_exF h))

end

end WangZahlLot.Obl.wz_c2_slope_normalization
