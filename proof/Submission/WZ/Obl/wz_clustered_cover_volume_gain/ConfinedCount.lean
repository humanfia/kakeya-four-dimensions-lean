-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.ConfinedCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.LocalCount

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set
open WangZahlLot.Obl.wz_flat_factored_improvement

/-- The local convex count in the frozen grains configuration becomes a global
convex count after confinement. The loss is polynomial in the confinement error,
independent of the grain aspect ratio and of the selected family's cardinality. -/
theorem confined_grain_convex_count {n L A : ℕ} (hn : 0 < n) (hA : 1 ≤ A)
    (s : Fin n → Fin L) (hs : Function.Injective s) {a ρ c m : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hc : 0 < c) (haspect : a ≤ ρ * c)
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (u : Fin n → V)
    (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
    (hu : ∀ i, u i = boxAxis (e (s i)) 0 ∨ u i = -boxAxis (e (s i)) 0)
    (hcenter : ∀ i, ‖z (s i) - z₀‖ ≤ A * c)
    (hshort : ∀ i, |e₀ (z (s i) - z₀) 0| ≤ A * (a / ρ))
    (hnormal : ∀ i, ‖u i - boxAxis e₀ 0‖ ≤ A * ((a / ρ) / c))
    (hlocal : ∀ j W, Convex ℝ W →
      O (q L {j' | P (a / ρ) c c (z j') (e j') ⊆
        P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O m * μ W) :
    BodyConvexCount (fun i => P a (ρ * c) c (z (s i)) (e (s i)))
      (a * (ρ * c) * c) (((128 * A ^ 2 + 1) ^ 6 : ℕ) * m) := by
  have hle : a / ρ ≤ c := (div_le_iff₀ hρ).mpr (by simpa only [mul_comm] using haspect)
  obtain ⟨K, hK, ref, hcover⟩ := confined_prism_anchor_cover hn hA (div_pos ha hρ) hc hle
    (z ∘ s) (e ∘ s) u z₀ e₀ hu hcenter hshort hnormal
  have hcover' : ∀ i, ∃ k,
      P (a / ρ) c c (z (s i)) (e (s i)) ⊆
        P (2 * a / ρ) (2 * c) (2 * c) (z (s (ref k))) (e (s (ref k))) := by
    simpa only [Function.comp_apply, show 2 * (a / ρ) = 2 * a / ρ by ring] using hcover
  have hh := grain_convex_count_of_anchors s hs (s ∘ ref) (by positivity) z e hcover' hlocal
  rwa [hK] at hh

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
