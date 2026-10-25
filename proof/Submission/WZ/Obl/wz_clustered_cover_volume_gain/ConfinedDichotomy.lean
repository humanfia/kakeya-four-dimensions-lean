-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.ConfinedDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseDichotomy
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NarrowRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd unit)

/-- The geometric dichotomy and the analytic packet estimate combined:
dense grains either force a large ambient density or have a retained shading
with controlled medium multiplicity. -/
theorem confined_grain_density_or_refinement {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n L A : ℕ) (ι : Fin n → Fin L),
    1 ≤ A → Function.Injective ι → (n : ℝ) ≤ δ ^ (-100 : ℝ) →
    ∀ θ ρ a c s m D R lam : ℝ,
    0 < θ → θ ≤ 1 → 0 < ρ → ρ ≤ θ → 0 < a → a ≤ ρ * c →
    0 < c → c ≤ 1 → 0 < s → s ≤ 1 → a ≤ s * ρ * c → s * ρ * c ≤ A * a →
    1 ≤ m → 0 < D → 1536 * δ ^ η ≤ D / 8 → δ ≤ a / 20000 →
    256 * δ ^ 2 ≤ a * ρ / (800000000 * θ ^ 2 * s * c) →
    0 < R → (s = 1 ∨ R ≤ (s / 2) * ρ * c) → 0 ≤ lam →
    ∀ (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (Y : Fin n → Set V) (Z U : Set V),
    (∀ i, ‖dualLinear θ (boxAxis (e (ι i)) 0)‖ ≤ 25 * θ) →
    (∀ i, ‖dualLinear θ (boxAxis (e (ι i)) 1)‖ ≤ 25 * θ) →
    (∀ i, ‖coarseLinear θ (boxAxis (e (ι i)) 2)‖ ≤ 43) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ P a (ρ * c) c (z (ι i)) (e (ι i))) →
    (∀ i, Y i ⊆ Z) → Z ⊆ U → U ⊆ ball 0 1 →
    (∀ i, O D * volume (P a (ρ * c) c (z (ι i)) (e (ι i))) ≤ volume (Y i)) →
    (∀ p ∈ Z, volume (U ∩ ball p R) ≤ O (lam * R ^ 3)) →
    (∀ j W, Convex ℝ W →
      O (q L {j' | P (a / ρ) c c (z j') (e j') ⊆
        P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O m * μ W) →
    confinementDensity a ρ c D s ≤ 46080 * lam ∨
    ∃ W : Fin n → Set V, (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i) ∧
      (1 / 16 : ℝ≥0∞) * ∑ i, volume (Y i) ≤ ∑ i, volume (W i) ∧
      ∀ p, bodyCount W p ≤ C * δ ^ (-ε) * (D / 8)⁻¹ *
        ((((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) * m) ^ (1 + σ / 2) *
        (a * ρ / (800000000 * θ ^ 2 * s * c)) ^ (-(ω + σ) / 2) := by
  intro ε hε
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ :=
    narrow_grain_refinement hσ hσhalf hω hE ε hε
  refine ⟨C, η, d₀, hC, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδsmall n L A ι hA hι hncard θ ρ a c s m D R lam hθ hθ1 hρ hρθ ha hac hc hc1
    hs hs1 has hAs hm hD hDη hδa hscale hR hRs hlam z e Y Z U hDn hDb haxis hYm hYU hYZ hZU
    hUball hdense hupper hlocal
  have hsub :
      confinementDensity a ρ c D s ≤ 46080 * lam ∨
      ∃ Y' : Fin n → Set V,
        (∀ i, MeasurableSet (Y' i) ∧ Y' i ⊆ Y i ∧ (1 / 4 : ℝ≥0∞) * volume (Y i) ≤ volume (Y' i)) ∧
        ∀ i j p, p ∈ Y' i → p ∈ Y' j → s = 1 ∨
          pd (unit (dualLinear θ (boxAxis (e (ι i)) 0)))
            (unit (dualLinear θ (boxAxis (e (ι j)) 0))) ≤ s := by
    by_cases hsone : s = 1
    · right
      refine ⟨Y, fun i => ⟨hYm i, Set.Subset.rfl, ?_⟩, fun _ _ _ _ _ => Or.inl hsone⟩
      exact (mul_le_mul' (by norm_num : (1 / 4 : ℝ≥0∞) ≤ 1) le_rfl).trans_eq (one_mul _)
    · rcases coarse_grains_transverse_or_narrow hθ hθ1 hρ hρθ ha hac hc hs hs1 has
        hR (hRs.resolve_left hsone) hD hlam (z ∘ ι) (e ∘ ι) Y Z U haxis hYm hYU hYZ hZU hUball hdense hupper with hd | hh
      · exact Or.inl hd
      · obtain ⟨Y', hY', hnarrow⟩ := hh
        exact Or.inr ⟨Y', hY', fun i j p hi hj => Or.inr (hnarrow i j p hi hj)⟩
  rcases hsub with hd | hsub
  · exact Or.inl hd
  obtain ⟨Y', hY', hnarrow⟩ := hsub
  have hmass : (1 / 4 : ℝ≥0∞) * ∑ i, volume (Y i) ≤ ∑ i, volume (Y' i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hY' i).2.2)
  let w := a * (ρ * c) * c
  have hw : 0 < w := by dsimp [w]; positivity
  have hden : O (D * n * w) ≤ ∑ i, volume (Y i) := by
    have he := sum_uniform_volume_weight (Finset.univ : Finset (Fin n)) hD.le hw.le
    simp only [Finset.card_univ, Fintype.card_fin] at he
    change ENNReal.ofReal (D * n * w) ≤ _
    rw [← he]
    apply Finset.sum_le_sum
    intro i _
    simpa only [w, frozen_prism_volume ha.le (mul_pos hρ hc).le hc.le,
      ← ENNReal.ofReal_mul hD.le] using hdense i
  have hbudget : O (D / 8 * n * w) ≤ (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y' i) := by
    calc
      _ = (1 / 8 : ℝ≥0∞) * O (D * n * w) := by
        have h8 : (1 / 8 : ℝ≥0∞) = O (1 / 8 : ℝ) := by norm_num [O, ENNReal.ofReal_div_of_pos]
        rw [h8, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
        congr 1
        ring
      _ ≤ (1 / 8 : ℝ≥0∞) * ∑ i, volume (Y i) := mul_le_mul' le_rfl hden
      _ = (1 / 2 : ℝ≥0∞) * ((1 / 4 : ℝ≥0∞) * ∑ i, volume (Y i)) := by
        rw [← mul_assoc]
        congr 1
        rw [one_div, one_div, one_div, ← ENNReal.mul_inv] <;> norm_num
      _ ≤ _ := mul_le_mul' le_rfl hmass
  have hasθ : a ≤ θ * s * c := has.trans (by nlinarith [mul_le_mul_of_nonneg_right hρθ (mul_pos hs hc).le])
  obtain ⟨W, hW, hretain, hcount⟩ := H δ hδ hδsmall n L A ι hA hι hncard θ ρ a c s m (D / 8)
    hθ hθ1 hρ hρθ ha hac hc hc1 hs hs1 hasθ hAs hm (by positivity) hDη hδa hscale z e Y'
    hDn hDb haxis (fun i => (hY' i).1) (fun i => (hY' i).2.1.trans (hYU i)) hbudget hnarrow hlocal
  right
  refine ⟨W, fun i => ⟨(hW i).1, (hW i).2.trans (hY' i).2.1⟩, ?_, hcount⟩
  calc
    _ = (1 / 4 : ℝ≥0∞) * ((1 / 4 : ℝ≥0∞) * ∑ i, volume (Y i)) := by
      rw [← mul_assoc]
      congr 1
      rw [one_div, one_div, ← ENNReal.mul_inv] <;> norm_num
    _ ≤ (1 / 4 : ℝ≥0∞) * ∑ i, volume (Y' i) := mul_le_mul' le_rfl hmass
    _ ≤ _ := hretain

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
