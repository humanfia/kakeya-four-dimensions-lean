import Submission.Obl.k4_general_parent_wide_layer_candidates.Model
import Submission.Obl.k4_general_parent_wide_layer_candidates.DomainMenus

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- One actual projected layer, retaining the original label identities and
the original velocity/intercept bins. -/
structure ProjectedLayer (α : Type) where
  β : ℝ
  count : ℕ
  C : Fin count → Set α
  tag : Fin count → Fin 2 → ℤ
  u : Fin count → ℝ
  v : Fin count → ℝ
  G : Fin count → MvPolynomial (Fin 2) ℝ

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

def referenceWeight (L : ProjectedLayer α) (p : Parent α) (k : ℕ) (s m : ℝ)
    (i : Fin L.count) : ℝ≥0∞ :=
  ENNReal.ofReal (p.N k ^ (-m) * (p.N k ^ (-s)) ^ p.d * L.β) *
    p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = L.tag i 0}

def unscaledWeight (L : ProjectedLayer α) (p : Parent α) (k : ℕ) (s m : ℝ)
    (i : Fin L.count) : ℝ≥0∞ :=
  ENNReal.ofReal (p.N k ^ (-m) * (p.N k ^ (-s)) ^ p.d) *
    p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = L.tag i 0}

def Covers (L : ProjectedLayer α) (σ : Measure (α × ℝ)) : Prop :=
  ∀ᵐ ω ∂σ, ∃ i, ω.1 ∈ L.C i

def Valid (L : ProjectedLayer α) (p : Parent α) (k : ℕ) (s m H : ℝ) : Prop :=
  0 < L.β ∧ p.N k ^ (-p.ℓ * s) / H ≤ L.β ∧ L.β ≤ H * p.N k ^ (-p.ℓ * s) ∧
  (∀ i, MeasurableSet (L.C i)) ∧
  (∀ i i', i ≠ i' → Disjoint (L.C i) (L.C i')) ∧
  (∀ i, |L.u i| + |L.v i| ≤ H ∧ (L.G i).totalDegree ≤ 2 ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, L.u i + t * L.v i + L.β * w] (L.G i)| ≤ H) ∧
    (∀ l ∈ L.C i,
      ⌊p.b k l 3 / (p.N k ^ (-m))⌋ = L.tag i 0 ∧
      ⌊p.b k l 0 / (p.N k ^ (-m))⌋ = L.tag i 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        |(p.x k l t) 2 - L.u i - t * L.v i| ≤ H * L.β ∧
        |MvPolynomial.eval (p.x k l t) (p.P k) -
          MvPolynomial.eval ![t, (p.x k l t) 2] (L.G i)| ≤ H * p.N k ^ (-s)) ∧
    ENNReal.ofReal (p.N k ^ (-m) * (p.N k ^ (-s)) ^ p.d * L.β / H) *
      p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = L.tag i 0} ≤
      p.ρ k (L.C i ×ˢ Icc (0 : ℝ) 1)) ∧
  (∑ i, L.referenceWeight p k s m i) ≤ ENNReal.ofReal H

/-- The actual full-time trajectory geometry supplies finite common-domain
menus whose total sliced reference is paid by the frozen layer budget. -/
theorem domain_menus (L : ProjectedLayer α) (p : Parent α) {k : ℕ} {s m H h g b : ℝ}
    (hL : L.Valid p k s m H) (hH : 1 ≤ H)
    (hh : 0 < h) (hh1 : h ≤ 1) (hb : 0 < b) (hbβ : b ≤ L.β) (hβg : L.β ≤ g) :
    ∃ D : Fin L.count → Finset (ℤ × ℤ × ℤ),
      (∀ i l, l ∈ L.C i → ∀ t ∈ Icc (0 : ℝ) 1,
        movingDomainCode h g b (p.b k l 1) (p.b k l 4) t ∈ D i) ∧
      (∑ i, ((D i).card : ℝ≥0∞) * (ENNReal.ofReal (h * b) * L.unscaledWeight p k s m i)) ≤
        ENNReal.ofReal (240 * H ^ 3) := by
  rcases hL with ⟨hβ, hβlo, hβhi, hC, hdisj, hlabels, hbudget⟩
  obtain ⟨D, hcover, hcost⟩ := exists_moving_domain_menus_with_budget
    hH hh hh1 hb (fun _ : Fin L.count => L.β) L.u L.v
    (fun _ => hbβ) (fun _ => hβg) (L.unscaledWeight p k s m)
  refine ⟨D, ?_, ?_⟩
  · intro i l hl t ht
    apply hcover i _ _ t ht
    intro t' ht'
    have hh := ((hlabels i).2.2.2.1 l hl).2.2 t' ht'
    simpa [Submission.Obl.k4_critical_intercept_concentration.Data.x] using hh.1
  · have href (i : Fin L.count) :
        ENNReal.ofReal L.β * L.unscaledWeight p k s m i = L.referenceWeight p k s m i := by
      dsimp [unscaledWeight, referenceWeight]
      rw [← mul_assoc, ← ENNReal.ofReal_mul hβ.le]
      rw [mul_comm L.β]
    simp_rw [href] at hcost
    calc
      _ ≤ ENNReal.ofReal (240 * H ^ 2) * ∑ i, L.referenceWeight p k s m i := hcost
      _ ≤ ENNReal.ofReal (240 * H ^ 2) * ENNReal.ofReal H := mul_le_mul_right hbudget _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 240 * H ^ 2)]
        congr 1
        ring

end ProjectedLayer

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Extract the literal projected layers on their common subsequence,
without changing any original law, label, or reference weight. -/
theorem WideLayers.projected_layers (hwide : p.WideLayers) :
    ∃ L : ℝ, 2 < L ∧ ∀ a : ℝ, 0 < a → L * a < p.U →
      ∀ D : Finset ℝ, (∀ s ∈ D, a ≤ s ∧ s ≤ 2 * a) → ∀ m : ℝ, L * a < m →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ H : ℕ → ℝ,
        (∀ k, 1 ≤ H k ∧ p.K (τ k) ≤ H k) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N (τ k) ^ ε) ∧
      ∃ (σ : ℕ → Measure (α × ℝ)) (layers : ℕ → ℝ → ProjectedLayer α),
        (∀ k, σ k ≤ p.ρ (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ σ k univ) ∧
        ∀ k s, s ∈ D → (layers k s).Valid p (τ k) s m (H k) ∧ (layers k s).Covers (σ k) := by
  obtain ⟨L, hL, hpre⟩ := hwide
  refine ⟨L, hL, ?_⟩
  intro a ha haU D hD m hm
  obtain ⟨τ, hτ, H, hHK, hHsub, σ, β, n, C, tag, u, v, G, hσ, hlayers⟩ :=
    hpre a ha haU D hD m hm
  let layers (k : ℕ) (s : ℝ) : ProjectedLayer α :=
    ⟨β k s, n k s, C k s, tag k s, u k s, v k s, G k s⟩
  refine ⟨τ, hτ, H, hHK, hHsub, σ, layers, hσ, ?_⟩
  intro k s hs
  obtain ⟨hβ, hβlo, hβhi, hC, hdisj, hlabels, hbudget, hcover⟩ := hlayers k s hs
  exact ⟨⟨hβ, hβlo, hβhi, hC, hdisj, hlabels, hbudget⟩, hcover⟩

end Parent
end
end Submission.Obl.k4_general_parent_wide_layer_candidates
