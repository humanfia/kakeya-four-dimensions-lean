-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.FromFurstenberg.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.SingleScaleFinal
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.RichStripSet

/-!
# o141 from the Furstenberg bush estimate alone

The rich-strip count is proved (`frostman_rich_strip_count`), the single-scale
estimate follows from it and the Furstenberg bush estimate
(`P2_of_furstenberg_richstrip`), and o141 from the single-scale estimate
(`o141_of_P2`).
-/

namespace WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

/-- The rich-strip count in the internal form. -/
theorem richStrip_internal :
    ∃ AB : ℝ, 0 < AB ∧ ∀ r C : ℝ, 0 < r → r ≤ 1 → 1 ≤ C → RichStripAt r C AB := by
  obtain ⟨A, hA, h⟩ := frostman_rich_strip_count
  exact ⟨A, hA, fun r C hr hr1 hC l hl Y J hY hYne hY4 hFr hJ hJmem hJsep =>
    h r C l hr hr1 hC hl Y J hY hYne hY4 hFr hJ hJmem hJsep⟩

/-- o141 from the Furstenberg bush estimate (internal form). -/
theorem o141_of_furstenberg
    (hA : ∀ ε : ℝ, 0 < ε → ∃ ε₀ ηA rA : ℝ, 0 < ε₀ ∧ 0 < ηA ∧ 0 < rA ∧
      ∀ r σ : ℝ, 0 < r → r ≤ rA → 1 / 4 ≤ σ → σ ≤ 1 - ε → FurstenbergAt r σ ε₀ ηA) :
    ∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ TT, TT = (fun (δ σ K c : ℝ) (G G' : Set (EuclideanSpace ℝ (Fin 2))) => ∃ T : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), T ⊆ G ×ˢ G' ∧ (1 - c) * G.ncard * G'.ncard ≤ (T.ncard : ℝ) ∧ ∀ b ∈ G, ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 → ∀ r : ℝ, δ ≤ r → ({b' | (b, b') ∈ T ∧ |inner ℝ (b' - b) e| < r}.ncard : ℝ) ≤ K * r ^ σ * G'.ncard) → ∀ ε : ℝ, 0 < ε → ∃ τ M δ₀ : ℝ, 0 < τ ∧ 1 ≤ M ∧ 0 < δ₀ ∧ ∀ δ σ c K C : ℝ, 0 < δ → δ ≤ δ₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → 0 < c → c < 1 / 10 → 1 ≤ K → 1 ≤ C → ∀ G G' : Set (EuclideanSpace ℝ (Fin 2)), Fr δ C G → Fr δ C G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') → TT δ σ K c G G' → TT δ σ K c G' G → TT δ (σ + τ) ((C * K / c) ^ M) (4 * c) G G' ∧ TT δ (σ + τ) ((C * K / c) ^ M) (4 * c) G' G :=
  o141_of_P2 (P2_of_furstenberg_richstrip hA richStrip_internal)

end WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs
