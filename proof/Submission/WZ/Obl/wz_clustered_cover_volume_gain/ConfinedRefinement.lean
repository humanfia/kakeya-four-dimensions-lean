-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.ConfinedRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketCount
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AffineRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)

/-- The analytic medium-scale refinement for one actual confined packet,
using only the local convex count from the original grain family. -/
theorem confined_frozen_packet_refinement {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n L A : ℕ) (ι : Fin n → Fin L),
    0 < n → 1 ≤ A → Function.Injective ι → (n : ℝ) ≤ δ ^ (-100 : ℝ) →
    ∀ θ ρ a c s m D : ℝ,
    0 < θ → θ ≤ 1 → 0 < ρ → ρ ≤ θ → 0 < a → a ≤ ρ * c →
    0 < c → c ≤ 1 → 0 < s → s ≤ 1 → a ≤ θ * s * c → s * ρ * c ≤ A * a →
    1 ≤ m → 0 < D → 1536 * δ ^ η ≤ D → δ ≤ a / 20000 →
    256 * δ ^ 2 ≤ a * ρ / (800000000 * θ ^ 2 * s * c) →
    ∀ (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
      (Y : Fin n → Set V),
    ‖dualLinear θ (boxAxis e₀ 0)‖ ≤ 25 * θ →
    ‖dualLinear θ (boxAxis e₀ 1)‖ ≤ 25 * θ →
    (∀ i, ‖coarseLinear θ (boxAxis (e (ι i)) 2)‖ ≤ 43) →
    (∀ i, ‖unit (dualLinear θ (boxAxis (e (ι i)) 0)) -
      unit (dualLinear θ (boxAxis e₀ 0))‖ ≤ s / 100) →
    (∀ i, ‖coarseLinear θ (z (ι i) - z₀)‖ ≤ c / 100) →
    (∀ i, |inner ℝ (unit (dualLinear θ (boxAxis e₀ 0)))
      (coarseLinear θ (z (ι i) - z₀))| ≤ s * c / 100) →
    (∀ i, 1 / 2 ≤ |inner ℝ (boxAxis e₀ 2) (boxAxis (e (ι i)) 2)|) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ P a (ρ * c) c (z (ι i)) (e (ι i))) →
    O (D * n * (a * (ρ * c) * c)) ≤ ∑ i, volume (Y i) →
    (∀ j W, Convex ℝ W →
      O (q L {j' | P (a / ρ) c c (z j') (e j') ⊆
        P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O m * μ W) →
    ∃ Z : Fin n → Set V, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) ∧
      ∀ p, bodyCount Z p ≤ C * δ ^ (-ε) * D⁻¹ *
        ((((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) * m) ^ (1 + σ / 2) *
        (a * ρ / (800000000 * θ ^ 2 * s * c)) ^ (-(ω + σ) / 2) := by
  intro ε hε
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ :=
    affine_body_refinement_of_volume hσ hσhalf hω hE ε hε
  refine ⟨C, η, d₀, hC, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδsmall n L A ι hn hA hι hncard θ ρ a c s m D hθ hθ1 hρ hρθ ha hac hc hc1
    hs hs1 has hAs hm hD hDη hδa hscale z e z₀ e₀ Y hDn hDb haxis hangle hcenter hshort
    hlong hYm hYU hden hlocal
  have hangle' (i : Fin n) : ‖unit (dualLinear θ (boxAxis (e (ι i)) 0)) -
      unit (dualLinear θ (boxAxis e₀ 0))‖ ≤ s := (hangle i).trans (by linarith)
  obtain ⟨f, hvol, hball, hint, hdiam⟩ := frozen_packet_normalization hθ hθ1 hρ hρθ ha hac hc hc1
    hs hs1 has (z ∘ ι) (e ∘ ι) z₀ e₀ hDn hDb haxis hangle' hcenter hshort hlong
  let w := a * (ρ * c) * c
  let J := 1 / (800000000 * θ ^ 2 * s * c ^ 3)
  let M : ℝ := (((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) * m
  have hw : 0 < w := by dsimp [w]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hJw : J * w = a * ρ / (800000000 * θ ^ 2 * s * c) :=
    normalized_packet_weight hθ.ne' hs.ne' hc.ne'
  have hM : 1 ≤ M := by
    have hKN : 1 ≤ (128 * A ^ 2 + 1) ^ 6 := by
      have hh : 0 < (128 * A ^ 2 + 1) ^ 6 := by positivity
      omega
    have hK : (1 : ℝ) ≤ (((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) := by exact_mod_cast hKN
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left hm (le_trans (by norm_num) hK)]
  have hρc : ρ * c ≤ c := by
    have hh := mul_le_mul_of_nonneg_right (hρθ.trans hθ1) hc.le
    simpa only [one_mul] using hh
  have hK := packet_convex_count hn hA ι hι hθ hθ1 ha hρ hc hs hac hAs z e z₀ e₀
    hDn hangle hcenter hshort hlocal
  obtain ⟨Z, hZY, hmass, hmult⟩ := H δ hδ hδsmall n
    (fun i => P a (ρ * c) c (z (ι i)) (e (ι i))) Y (fun i => f (z (ι i))) w M J D f
    hn hncard (by rwa [hJw]) hw hM hJ hD hDη hvol
    (fun i => frozen_prism_compact ha.le hac hρc (z (ι i)) (e (ι i)))
    (fun i => frozen_prism_convex _ _ _ _ _) hball
    (fun i => (ball_subset_ball hδa).trans (hint i)) hdiam
    (fun i => by
      rw [frozen_prism_volume ha.le (mul_pos hρ hc).le hc.le]
      exact ⟨le_rfl, ENNReal.ofReal_le_ofReal (by dsimp [w] at hw ⊢; linarith)⟩)
    hYm hYU hden hK
  exact ⟨Z, hZY, hmass, fun p => by simpa only [hJw] using hmult p⟩

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
