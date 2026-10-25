-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.FrozenPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GeometricPackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd unit)

/-- A narrow family of the exact frozen grains admits the packet geometry
used by `confined_frozen_packet_refinement`. -/
theorem frozen_narrow_packets {n : ℕ} {θ ρ a c s : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ) (hρθ : ρ ≤ θ)
    (ha : 0 < a) (hac : a ≤ ρ * c) (hc : 0 < c)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ θ * s * c)
    (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V) (Y : Fin n → Set V)
    (haxis : ∀ i, ‖coarseLinear θ (boxAxis (e i) 2)‖ ≤ 43)
    (hYU : ∀ i, Y i ⊆ P a (ρ * c) c (z i) (e i))
    (hnarrow : ∀ i j p, p ∈ Y i → p ∈ Y j → s = 1 ∨
      pd (unit (dualLinear θ (boxAxis (e i) 0))) (unit (dualLinear θ (boxAxis (e j) 0))) ≤ s) :
    ∃ L : ℕ, ∃ f : Fin n → Fin L, ∃ ref : Fin L → Fin n,
      (∀ k, f (ref k) = k) ∧
      (∀ i j, f i = f j →
        ‖unit (dualLinear θ (boxAxis (e i) 0)) - unit (dualLinear θ (boxAxis (e j) 0))‖ ≤ s / 100 ∧
        1 / 2 ≤ |inner ℝ (boxAxis (e j) 2) (boxAxis (e i) 2)| ∧
        ‖coarseLinear θ (z i - z j)‖ ≤ c / 100 ∧
        |inner ℝ (unit (dualLinear θ (boxAxis (e j) 0))) (coarseLinear θ (z i - z j))| ≤ s * c / 100) ∧
      (∀ p, bodyCount (assignedFiber f Y) p ≤ geometricPacketOverlap) := by
  have hρcθ : ρ * c ≤ θ * c := mul_le_mul_of_nonneg_right hρθ hc.le
  have hex (i : Fin n) : ∃ u : OrthonormalBasis (Fin 3) ℝ V,
      u 0 = unit (dualLinear θ (boxAxis (e i) 0)) := by
    obtain ⟨u, hu, _, _⟩ := coarse_prism_enclosure hθ hθ1 (by positivity : 0 ≤ a)
      hac hρcθ hc.le (by norm_num : (0 : ℝ) ≤ 43) (frozenBasis (e i)) (z i) (haxis i)
    exact ⟨u, hu⟩
  choose u hu using hex
  have hsource (i : Fin n) (p : V) (hp : p ∈ Y i) :
      ‖coarseLinear θ p - coarseLinear θ (z i)‖ ≤ 25 * c ∧
      |inner ℝ (u i 0) (coarseLinear θ p - coarseLinear θ (z i))| ≤ s * c := by
    rw [← map_sub, hu i]
    have hh := frozen_prism_coarse_bounds hθ hθ1 ha.le hac hρcθ hc (z i) (e i) (haxis i) p (hYU i hp)
    exact ⟨hh.1, hh.2.trans ((div_le_iff₀ hθ).mpr (by nlinarith))⟩
  have hnarrow' (i j : Fin n) (p : V) (hi : p ∈ Y i) (hj : p ∈ Y j) :
      s = 1 ∨ pd (u i 0) (u j 0) ≤ s := by
    rw [hu i, hu j]
    exact hnarrow i j p hi hj
  obtain ⟨L, f, ref, href, hclose, hcount⟩ := narrow_geometric_packets hs hs1 hc u
    (fun i => coarseLinear θ (z i)) (fun i => boxAxis (e i) 2) Y (coarseLinear θ)
    (fun i => boxAxis_norm (e i) 2) hsource hnarrow'
  refine ⟨L, f, ref, href, ?_, hcount⟩
  intro i j hij
  obtain ⟨hn, hl, hz, ht⟩ := hclose i j hij
  rw [hu i, hu j] at hn
  rw [← map_sub] at hz
  rw [hu j, ← map_sub] at ht
  refine ⟨hn, ?_, hz, ht⟩
  apply inner_ge_half_of_close (boxAxis_norm (e j) 2) (boxAxis_norm (e i) 2)
  rw [norm_sub_rev]
  exact hl.trans (by norm_num)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
