-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.NarrowRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ConfinedRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenPackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensePacketAssembly
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SubfamilyRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd unit)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (enumerate enumerate_mem sum_enumerate)

local instance narrowRefinementDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The full medium-scale refinement for a narrow family: construct packets,
discard sparse ones, refine each dense packet, and use bounded packet overlap. -/
theorem narrow_grain_refinement {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n L A : ℕ) (ι : Fin n → Fin L),
    1 ≤ A → Function.Injective ι → (n : ℝ) ≤ δ ^ (-100 : ℝ) →
    ∀ θ ρ a c s m D : ℝ,
    0 < θ → θ ≤ 1 → 0 < ρ → ρ ≤ θ → 0 < a → a ≤ ρ * c →
    0 < c → c ≤ 1 → 0 < s → s ≤ 1 → a ≤ θ * s * c → s * ρ * c ≤ A * a →
    1 ≤ m → 0 < D → 1536 * δ ^ η ≤ D → δ ≤ a / 20000 →
    256 * δ ^ 2 ≤ a * ρ / (800000000 * θ ^ 2 * s * c) →
    ∀ (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (Y : Fin n → Set V),
    (∀ i, ‖dualLinear θ (boxAxis (e (ι i)) 0)‖ ≤ 25 * θ) →
    (∀ i, ‖dualLinear θ (boxAxis (e (ι i)) 1)‖ ≤ 25 * θ) →
    (∀ i, ‖coarseLinear θ (boxAxis (e (ι i)) 2)‖ ≤ 43) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ P a (ρ * c) c (z (ι i)) (e (ι i))) →
    O (D * n * (a * (ρ * c) * c)) ≤ (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i) →
    (∀ i j p, p ∈ Y i → p ∈ Y j → s = 1 ∨
      pd (unit (dualLinear θ (boxAxis (e (ι i)) 0)))
        (unit (dualLinear θ (boxAxis (e (ι j)) 0))) ≤ s) →
    (∀ j W, Convex ℝ W →
      O (q L {j' | P (a / ρ) c c (z j') (e j') ⊆
        P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O m * μ W) →
    ∃ Z : Fin n → Set V, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 4 : ℝ≥0∞) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) ∧
      ∀ p, bodyCount Z p ≤ C * δ ^ (-ε) * D⁻¹ *
        ((((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) * m) ^ (1 + σ / 2) *
        (a * ρ / (800000000 * θ ^ 2 * s * c)) ^ (-(ω + σ) / 2) := by
  intro ε hε
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ :=
    confined_frozen_packet_refinement hσ hσhalf hω hE ε hε
  have hP : (0 : ℝ) < geometricPacketOverlap := by norm_num [geometricPacketOverlap]
  refine ⟨geometricPacketOverlap * C, η, d₀, mul_pos hP hC, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδsmall n L A ι hA hι hncard θ ρ a c s m D hθ hθ1 hρ hρθ ha hac hc hc1
    hs hs1 has hAs hm hD hDη hδa hscale z e Y hDn hDb haxis hYm hYU hbudget hnarrow hlocal
  let w := a * (ρ * c) * c
  have hw : 0 < w := by dsimp [w]; positivity
  have hm0 : 0 < m := by linarith
  let B : ℝ := C * δ ^ (-ε) * D⁻¹ *
    ((((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) * m) ^ (1 + σ / 2) *
      (a * ρ / (800000000 * θ ^ 2 * s * c)) ^ (-(ω + σ) / 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hρc : ρ * c ≤ c := by
    have hh := mul_le_mul_of_nonneg_right (hρθ.trans hθ1) hc.le
    simpa only [one_mul] using hh
  have hfin : (∑ i, volume (Y i)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ne_top_of_le_ne_top
      (frozen_prism_compact ha.le hac hρc (z (ι i)) (e (ι i))).isBounded.measure_lt_top.ne
      (measure_mono (hYU i))
  obtain ⟨K, f, ref, href, hclose, hactive⟩ := frozen_narrow_packets hθ hθ1 hρ hρθ ha hac hc
    hs hs1 has (z ∘ ι) (e ∘ ι) Y haxis hYU hnarrow
  let cost : Fin n → ℝ≥0∞ := fun _ => O (D * w)
  have hcost : (∑ i, cost i) ≤ (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i) := by
    have hh := sum_uniform_volume_weight (Finset.univ : Finset (Fin n)) hD.le hw.le
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    change (∑ i, ENNReal.ofReal (D * w)) ≤ _
    rw [hh]
    exact hbudget
  have hpacket (k : Fin K) (Y' : Fin n → Set V)
      (hY' : ∀ i, MeasurableSet (Y' i) ∧ Y' i ⊆ Y i)
      (hden : (∑ i ∈ Finset.univ.filter (fun i => f i = k), cost i) ≤
        ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y' i)) :
      ∃ W : Fin n → Set V,
        (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y' i ∧ (f i ≠ k → W i = ∅)) ∧
        (1 / 2 : ℝ≥0∞) * (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y' i)) ≤
          ∑ i, volume (W i) ∧ ∀ p, bodyCount W p ≤ B := by
    let I := Finset.univ.filter fun i => f i = k
    let j := enumerate I
    have hj (t : Fin I.card) : f (j t) = k := (Finset.mem_filter.mp (enumerate_mem I t)).2
    have hI : 0 < I.card := Finset.card_pos.mpr ⟨ref k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, href k⟩⟩
    have hcard : (I.card : ℝ) ≤ δ ^ (-100 : ℝ) :=
      (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using Finset.card_le_univ I)).trans hncard
    have hgeom (t : Fin I.card) := hclose (j t) (ref k) ((hj t).trans (href k).symm)
    have hden' : O (D * I.card * w) ≤ ∑ t, volume (Y' (j t)) := by
      rw [sum_enumerate I (fun i => volume (Y' i))]
      have hh := sum_uniform_volume_weight I hD.le hw.le
      change (∑ i ∈ I, ENNReal.ofReal (D * w)) = _ at hh
      change ENNReal.ofReal (D * I.card * w) ≤ _
      rw [← hh]
      exact hden
    obtain ⟨W, hW, hmass, hcount⟩ := H δ hδ hδsmall I.card L A (ι ∘ j)
      hI hA (hι.comp j.injective) hcard θ ρ a c s m D hθ hθ1 hρ hρθ ha hac hc hc1
      hs hs1 has hAs hm hD hDη hδa hscale z e (z (ι (ref k))) (e (ι (ref k)))
      (fun t => Y' (j t)) (hDn (ref k)) (hDb (ref k))
      (fun t => haxis (j t)) (fun t => (hgeom t).1) (fun t => (hgeom t).2.2.1)
      (fun t => (hgeom t).2.2.2) (fun t => (hgeom t).2.1)
      (fun t => (hY' (j t)).1) (fun t => (hY' (j t)).2.trans (hYU (j t))) hden' hlocal
    obtain ⟨W', hW', hmass', hcount'⟩ := extend_subfamily_refinement I Y' W hW hmass hcount
    refine ⟨W', fun i => ⟨(hW' i).1, (hW' i).2.1, ?_⟩, hmass', hcount'⟩
    intro hi
    exact (hW' i).2.2 (by simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using hi)
  obtain ⟨Z, hZ, hmass, hcount⟩ := refine_dense_packets f Y hYm hfin cost hcost hB hactive hpacket
  refine ⟨Z, hZ, hmass, fun p => (hcount p).trans_eq ?_⟩
  dsimp [B]
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
