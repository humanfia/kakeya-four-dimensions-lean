-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FirstPacketFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FirstPacketFilling.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FirstPacketFilling.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.DenseLabels
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FillingOnFinset

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open scoped ENNReal Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent (uniformMap)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit pd)

/-- Simultaneous first filling after discarding sparse angular labels. Every
selected label has the same normalized carrier radius and density. The total
selected original-index count is bounded below, with no separate saturation
assumption on the individual labels. -/
theorem first_packet_fillings {ι : Type*} {n : ℕ} (Λ : Finset ι)
    (S : ι → Finset (Fin n)) {r a b θ β C lam D k w d₀ L : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1 / 100) (hra : r ≤ a) (hab : a ≤ b)
    (hb : b ≤ 4) (hθ1 : θ ≤ 1) (hsmallslab : r + 5 * (a / 2) ≤ 1 / 100)
    (hflat : 100 * (r + 5 * (a / 2)) ≤ 3 * b)
    (hθ : 32 * (r + 5 * (a / 2)) ≤ θ) (hθb : θ ≤ 3 * b)
    (hlam : 0 < lam) (hC : 0 < C) (hD : 0 < D) (hw : 0 < w)
    (hk : 0 < k) (hksmall : k ≤ 1 / 1000000000)
    (hsmall : C * (θ / (3 * b)) ^ β ≤ lam / 8)
    (hnum : D * (10 ^ 13 * ((3 * b) / θ) * (1 + Real.log (1 / r))) ≤
      (lam / 16000) ^ 2 * (48 * lam))
    (x v : Fin n → V) (Y : ι → Fin n → Set V)
    (z : ι → V) (e : ι → V ≃ₗᵢ[ℝ] V) (f : ι → V ≃ᵃ[ℝ] V)
    (hvlo : ∀ i, (1 / 4 : ℝ) ≤ ‖v i‖) (hvhi : ∀ i, ‖v i‖ ≤ 1)
    (hends : ∀ ℓ ∈ Λ, ∀ i ∈ S ℓ,
      x i ∈ P a b 4 (z ℓ) (e ℓ) ∧ x i + v i ∈ P a b 4 (z ℓ) (e ℓ))
    (hYm : ∀ ℓ ∈ Λ, ∀ i, MeasurableSet (Y ℓ i))
    (hYT : ∀ ℓ ∈ Λ, ∀ i, Y ℓ i ⊆ T r (x i) (v i))
    (hzero : ∀ ℓ ∈ Λ, ∀ i, i ∉ S ℓ → Y ℓ i = ∅)
    (hupper : ∀ ℓ ∈ Λ, (∑ i, μ (Y ℓ i)) ≤ O (w * (S ℓ).card))
    (hmass : O (d₀ * w * n) ≤ ∑ ℓ ∈ Λ, ∑ i, μ (Y ℓ i))
    (hcount : (∑ ℓ ∈ Λ, ((S ℓ).card : ℝ)) ≤ L * n)
    (hbudget : 1536 * lam * r ^ 2 * L ≤ d₀ * w)
    (hbroad : ∀ ℓ ∈ Λ, ∀ (p u : V) (t : ℝ), ‖u‖ = 1 → r ≤ t → t ≤ 3 * b →
      q n {i | p ∈ Y ℓ i ∧ pd (unit (v i)) u ≤ t} ≤
        C * (t / (3 * b)) ^ β * q n {i | p ∈ Y ℓ i})
    (hf : ∀ ℓ ∈ Λ, ∀ q i,
      (f ℓ).linear q i = (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i * e ℓ q i)
    (hfvol : ∀ ℓ ∈ Λ, ∀ Q : Set V, μ (f ℓ '' Q) = O (1 / (4 * a * b)) * μ Q)
    (hfball : ∀ ℓ ∈ Λ, f ℓ '' P a b 4 (z ℓ) (e ℓ) ⊆ ball (0 : V) 1) :
    let F := fun ℓ => (f ℓ).trans (uniformMap hk).toAffineEquiv
    let B := 256 * k * r / a
    ∃ (good : Finset ι) (G : ι → Finset (Fin n)) (u : ι → Fin n → Fin 3 → V),
      good ⊆ Λ ∧ (∀ ℓ, G ℓ ⊆ S ℓ ∧ (ℓ ∉ good → G ℓ = ∅)) ∧
      (lam * d₀ / 16) * n ≤ ∑ ℓ ∈ good, ((G ℓ).card : ℝ) ∧
      (1 / 2 : ℝ≥0∞) * (∑ ℓ ∈ Λ, ∑ i, μ (Y ℓ i)) ≤
        ∑ ℓ ∈ good, ∑ i, μ (Y ℓ i) ∧
      ∀ ℓ ∈ good, (G ℓ).Nonempty ∧
        (lam / 8) * (S ℓ).card ≤ ((G ℓ).card : ℝ) ∧ B ≤ 1 / 1000000 ∧
        ∀ i ∈ G ℓ, O (48 * lam * r ^ 2) ≤ μ (Y ℓ i) ∧
          Orthonormal ℝ (u ℓ i) ∧ ‖F ℓ (x i + (1 / 2 : ℝ) • v i)‖ < 1 / 100 ∧
          F ℓ '' T r (x i) (v i) ⊆ WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
            B B (F ℓ (x i + (1 / 2 : ℝ) • v i)) (u ℓ i) ∧
          O ((D * k / 16000) * B ^ 2) ≤ μ
            (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
              B B (F ℓ (x i + (1 / 2 : ℝ) • v i)) (u ℓ i) ∩ F ℓ '' (⋃ j, Y ℓ j)) := by
  classical
  dsimp only
  let τ := 768 * lam * r ^ 2 / w
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hτw : τ * w = 768 * lam * r ^ 2 := by dsimp [τ]; field_simp
  have hbgt : 2 * τ * L ≤ d₀ := by
    apply (mul_le_mul_iff_left₀ hw).mp
    calc
      (2 * τ * L) * w = 1536 * lam * r ^ 2 * L := by
        calc
          _ = 2 * (τ * w) * L := by ring
          _ = _ := by rw [hτw]; ring
      _ ≤ _ := hbudget
  obtain ⟨good, hg, hden, hretain, hcard⟩ := dense_label_measures_retain_count Λ
    (fun ℓ => (S ℓ).card) (fun ℓ => ∑ i, μ (Y ℓ i)) hτ hw (Nat.cast_nonneg n)
    hupper hmass hcount hbgt
  let F := fun ℓ => (f ℓ).trans (uniformMap hk).toAffineEquiv
  let B := 256 * k * r / a
  let Data := fun ℓ (G : Finset (Fin n)) (u : Fin n → Fin 3 → V) =>
    G ⊆ S ℓ ∧ G.Nonempty ∧ (lam / 8) * (S ℓ).card ≤ (G.card : ℝ) ∧ B ≤ 1 / 1000000 ∧
      ∀ i ∈ G, O (48 * lam * r ^ 2) ≤ μ (Y ℓ i) ∧ Orthonormal ℝ (u i) ∧
        ‖F ℓ (x i + (1 / 2 : ℝ) • v i)‖ < 1 / 100 ∧
        F ℓ '' T r (x i) (v i) ⊆ WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          B B (F ℓ (x i + (1 / 2 : ℝ) • v i)) (u i) ∧
        O ((D * k / 16000) * B ^ 2) ≤ μ
          (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
            B B (F ℓ (x i + (1 / 2 : ℝ) • v i)) (u i) ∩ F ℓ '' (⋃ j, Y ℓ j))
  have H (ℓ : ι) : ∃ (G : Finset (Fin n)) (u : Fin n → Fin 3 → V),
      (ℓ ∈ good → Data ℓ G u) ∧ (ℓ ∉ good → G = ∅) := by
    by_cases hℓ : ℓ ∈ good
    · have hℓΛ := hg hℓ
      have hd : O (768 * lam * r ^ 2 * (S ℓ).card) ≤ ∑ i, μ (Y ℓ i) := by
        simpa only [hτw] using (hden ℓ hℓ).2
      obtain ⟨G, u, hh⟩ := flat_prism_dense_net_input_on_finset (S ℓ)
        (Finset.card_pos.mp (hden ℓ hℓ).1) hr hr1 hra hab hb hθ1 hsmallslab hflat hθ hθb
        hlam hC hD hk hksmall hsmall hnum x v (Y ℓ) (z ℓ) (e ℓ)
        (fun i _ => hvlo i) (fun i _ => hvhi i) (hends ℓ hℓΛ) (hYm ℓ hℓΛ)
        (hYT ℓ hℓΛ) (hzero ℓ hℓΛ) hd (hbroad ℓ hℓΛ) (f ℓ)
        (hf ℓ hℓΛ) (hfvol ℓ hℓΛ) (hfball ℓ hℓΛ)
      exact ⟨G, u, fun _ => hh, fun h => (h hℓ).elim⟩
    · exact ⟨∅, fun _ _ => 0, fun h => (hℓ h).elim, fun _ => rfl⟩
  choose G u hdata hzeroG using H
  have hselected : (lam / 8) * (∑ ℓ ∈ good, ((S ℓ).card : ℝ)) ≤
      ∑ ℓ ∈ good, ((G ℓ).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun ℓ hℓ => (hdata ℓ hℓ).2.2.1
  refine ⟨good, G, u, hg, ?_, ?_, hretain, ?_⟩
  · intro ℓ
    refine ⟨?_, hzeroG ℓ⟩
    by_cases hℓ : ℓ ∈ good
    · exact (hdata ℓ hℓ).1
    · rw [hzeroG ℓ hℓ]
      exact Finset.empty_subset _
  · calc
      _ = (lam / 8) * ((d₀ / 2) * n) := by ring
      _ ≤ (lam / 8) * (∑ ℓ ∈ good, ((S ℓ).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      _ ≤ _ := hselected
  · intro ℓ hℓ
    exact (hdata ℓ hℓ).2

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
