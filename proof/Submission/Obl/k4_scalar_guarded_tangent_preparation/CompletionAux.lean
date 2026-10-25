import Submission.Obl.k4_scalar_guarded_tangent_preparation.Pruning

/-!
# Auxiliary facts for the full-prior layer completion

Exponent comparisons for rounded depths and profiles, the retained weighted mass of the
pruned laws, and their support on the kept witnesses.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_scalar_linear_critical_extremizers
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- If `N ^ |x - y| ≤ B`, then `N ^ (λ x) ≤ B N ^ (λ y)` for `0 ≤ λ ≤ 1`. -/
theorem rpow_le_mul_of_abs_le {N B x y lam : ℝ} (hN : 1 ≤ N) (hB : N ^ |x - y| ≤ B)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    N ^ (lam * x) ≤ B * N ^ (lam * y) := by
  have hNpos : 0 < N := by linarith
  have h1 : lam * x ≤ lam * y + |x - y| := by
    have : lam * (x - y) ≤ |x - y| := by
      calc lam * (x - y) ≤ lam * |x - y| := mul_le_mul_of_nonneg_left (le_abs_self _) hl0
        _ ≤ 1 * |x - y| := mul_le_mul_of_nonneg_right hl1 (abs_nonneg _)
        _ = |x - y| := one_mul _
    linarith
  calc N ^ (lam * x) ≤ N ^ (lam * y + |x - y|) := Real.rpow_le_rpow_of_exponent_le hN h1
    _ = N ^ (lam * y) * N ^ |x - y| := Real.rpow_add hNpos _ _
    _ ≤ N ^ (lam * y) * B := by gcongr
    _ = B * N ^ (lam * y) := mul_comm _ _

theorem abs_sub_comm' (x y : ℝ) : |x - y| = |y - x| := abs_sub_comm x y

/-- The two directions of the comparison with `λ = d`, negated exponents. -/
theorem rpow_neg_le_mul_of_abs_le {N B x y lam : ℝ} (hN : 1 ≤ N) (hB : N ^ |x - y| ≤ B)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    N ^ (-lam * x) ≤ B * N ^ (-lam * y) := by
  have hB' : N ^ |(-x) - (-y)| ≤ B := by
    rw [show (-x) - (-y) = -(x - y) by ring, abs_neg]; exact hB
  have := rpow_le_mul_of_abs_le hN hB' hl0 hl1
  simpa [mul_neg, neg_mul] using this

/-- The scaling identity `N₀ ^ (-(sc * x)) = (N₀ ^ sc) ^ (-x)`. -/
theorem rpow_scale {N₀ sc x : ℝ} (hN₀ : 0 < N₀) :
    N₀ ^ (-(sc * x)) = (N₀ ^ sc) ^ (-x) := by
  rw [← Real.rpow_mul hN₀.le]; ring_nf

namespace PruneInput

variable {I : PruneInput}

/-- The pruned laws retain the weighted mass `c` when the original laws had `2 c` and the
total cost is at most `c`. -/
theorem pruned_mass (hmeas : ∀ ℓ i, MeasurableSet ((I.layers ℓ).assignment i))
    (ω : Fin I.W → ℝ) (hω : ∀ g, 0 ≤ ω g) (hω1 : ∑ g, ω g = 1)
    (hν : ∀ g, IsProbabilityMeasure (I.ν g)) (hK₁ : 0 < I.K₁)
    (hdisj : ∀ ℓ i i', i ≠ i' → (I.layers ℓ).world i = (I.layers ℓ).world i' →
      (I.layers ℓ).block i = (I.layers ℓ).block i' →
      Disjoint ((I.layers ℓ).assignment i) ((I.layers ℓ).assignment i'))
    {c : ℝ} (hc : 0 ≤ c) (hcount : (I.count : ℝ) / I.K₁ ≤ c)
    (hmass : ENNReal.ofReal (2 * c) ≤ ∑ g, ENNReal.ofReal (ω g) * I.ρ g Set.univ) :
    ENNReal.ofReal c ≤ ∑ g, ENNReal.ofReal (ω g) * pruned hmeas g Set.univ := by
  have hcost := weighted_cost_le ω hω hω1 hν hK₁ hmeas hdisj
  have hsplit : ∑ g, ENNReal.ofReal (ω g) * I.ρ g Set.univ ≤
      ∑ g, ENNReal.ofReal (ω g) * pruned hmeas g Set.univ +
        ∑ g, ENNReal.ofReal (ω g) * ∑ x ∈ I.packetsOf g, I.cost x := by
    rw [← Finset.sum_add_distrib]
    gcongr with g
    rw [← mul_add]
    gcongr
    exact (mask_spec hmeas g).2.1
  have h2 : ENNReal.ofReal (2 * c) = ENNReal.ofReal c + ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_add hc hc]; ring_nf
  have hle : ENNReal.ofReal c + ENNReal.ofReal c ≤
      ∑ g, ENNReal.ofReal (ω g) * pruned hmeas g Set.univ + ENNReal.ofReal c := by
    rw [← h2]
    refine hmass.trans (hsplit.trans ?_)
    gcongr
    exact hcost.trans (ENNReal.ofReal_le_ofReal hcount)
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hle

/-- The pruned law of a world lives on the kept witnesses of each layer. -/
theorem pruned_support (hmeas : ∀ ℓ i, MeasurableSet ((I.layers ℓ).assignment i))
    (σ : Fin I.W → Measure Incidence) (hρσ : ∀ g, I.ρ g ≤ σ g)
    (ℓ : Fin I.count) (g : Fin I.W)
    (hCrect : ∀ i, (I.layers ℓ).witness i ⊆
      (I.layers ℓ).assignment i ×ˢ Split.I (I.layers ℓ).T ((I.layers ℓ).block i))
    (hσ : σ g {z | ∃ i, (I.layers ℓ).world i = g ∧ z ∈ (I.layers ℓ).witness i}ᶜ = 0) :
    pruned hmeas g {z | ∃ i, (I.layers ℓ).world i = g ∧ keep hmeas ℓ i ∧
      z ∈ (I.layers ℓ).witness i}ᶜ = 0 := by
  classical
  set s := Finset.univ.filter (fun i => (I.layers ℓ).world i = g) with hs
  have hcover : pruned hmeas g (⋃ i ∈ s, (I.layers ℓ).witness i)ᶜ = 0 := by
    apply le_antisymm _ bot_le
    calc pruned hmeas g (⋃ i ∈ s, (I.layers ℓ).witness i)ᶜ
        ≤ σ g (⋃ i ∈ s, (I.layers ℓ).witness i)ᶜ := ((pruned_le hmeas g).trans (hρσ g)) _
      _ = σ g {z | ∃ i, (I.layers ℓ).world i = g ∧ z ∈ (I.layers ℓ).witness i}ᶜ := by
          congr 2
          ext z
          simp [hs]
      _ = 0 := hσ
      _ ≤ 0 := le_rfl
  have hmain := support_after_zero_packet_pruning (pruned hmeas g)
    (fun i => (I.layers ℓ).witness i)
    (fun i => (I.layers ℓ).assignment i ×ˢ Split.I (I.layers ℓ).T ((I.layers ℓ).block i))
    s (fun i _ => hCrect i) hcover
  refine le_antisymm (le_trans (measure_mono ?_) hmain.le) bot_le
  intro z hz hz'
  apply hz
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs] at hi
  refine ⟨i, hi.1, ?_, hzi⟩
  unfold keep
  rw [hi.1]
  exact hi.2

end PruneInput

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
