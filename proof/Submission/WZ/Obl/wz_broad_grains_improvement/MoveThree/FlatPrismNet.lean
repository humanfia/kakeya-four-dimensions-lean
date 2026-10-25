-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FlatPrismNet.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FlatPrismNet.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FlatPrismNet.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FlatPrismFrames
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FilledNetData

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open scoped ENNReal Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis inner_boxAxis)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent (uniformMap)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit pd)

/-- Broad flat short tubes produce a positive proportion of dense square prisms
after the fixed flat normalization. Whole short tubes, not only their shadings,
are contained in the selected prisms. -/
theorem flat_prism_dense_net_input {n : ℕ} (hn : 0 < n) {δ a b θ β h lam ε k : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hδa : δ ≤ a) (hab : a ≤ b)
    (hb : 3 * b ≤ 1) (hr : δ + 5 * (a / 2) ≤ 1 / 100)
    (hflat : 100 * (δ + 5 * (a / 2)) ≤ 3 * b)
    (hθ : 32 * (δ + 5 * (a / 2)) ≤ θ) (hθb : θ ≤ 3 * b)
    (hlam : 0 < lam) (hk : 0 < k) (hksmall : k ≤ 1 / 100000000)
    (hsmall : δ ^ (-h) * (θ / (3 * b)) ^ β ≤ lam / 8)
    (hnum : δ ^ ε * (10 ^ 13 * ((3 * b) / θ) * (1 + Real.log (1 / δ))) ≤
      (lam / 16000) ^ 2 * (48 * lam))
    (x v : Fin n → V) (Y : Fin n → Set V) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hvlo : ∀ i, (1 / 4 : ℝ) ≤ ‖v i‖) (hvhi : ∀ i, ‖v i‖ ≤ 1)
    (hends : ∀ i, x i ∈ P a b 4 z e ∧ x i + v i ∈ P a b 4 z e)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hmass : O (768 * lam * δ ^ 2 * n) ≤ ∑ i, μ (Y i))
    (hbroad : ∀ (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ 3 * b →
      q n {i | p ∈ Y i ∧ pd (unit (v i)) u ≤ r} ≤
        δ ^ (-h) * (r / (3 * b)) ^ β * q n {i | p ∈ Y i})
    (f : V ≃ᵃ[ℝ] V)
    (hf : ∀ q i, f.linear q i = (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i * e q i)
    (hfvol : ∀ Q : Set V, μ (f '' Q) = O (1 / (4 * a * b)) * μ Q)
    (hfball : f '' P a b 4 z e ⊆ ball (0 : V) 1) :
    let F := f.trans (uniformMap hk).toAffineEquiv
    let B := 64 * k * δ / a
    ∃ (G : Finset (Fin n)) (u : Fin n → Fin 3 → V),
      G.Nonempty ∧ (lam / 8) * n ≤ (G.card : ℝ) ∧ B ≤ 1 / 1000000 ∧
      ∀ i ∈ G, O (48 * lam * δ ^ 2) ≤ μ (Y i) ∧ Orthonormal ℝ (u i) ∧ ‖F (x i + (1 / 2 : ℝ) • v i)‖ < 1 / 100 ∧
        F '' T δ (x i) (v i) ⊆ WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          B B (F (x i + (1 / 2 : ℝ) • v i)) (u i) ∧
        O ((δ ^ ε * k / 1000) * B ^ 2) ≤ μ
          (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
            B B (F (x i + (1 / 2 : ℝ) • v i)) (u i) ∩ F '' (⋃ j, Y j)) := by
  classical
  let F := f.trans (uniformMap hk).toAffineEquiv
  let B := 64 * k * δ / a
  have ha : 0 < a := hδ.trans_le hδa
  obtain ⟨G, hcard, hstem, hfill⟩ := flat_prism_filling_frames_and_mass hδ hδ1 ha hab hb hr hflat hθ hθb
    hlam hsmall hnum x v Y z e hvlo hvhi hends hYm hYT hmass hbroad
  have hG : G.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < G.card :=
      (mul_pos (div_pos hlam (by norm_num)) (Nat.cast_pos.mpr hn)).trans_le hcard
    exact_mod_cast hp
  have H (i : Fin n) (hi : i ∈ G) : B ≤ 1 / 1000000 ∧
      ∃ u : Fin 3 → V, Orthonormal ℝ u ∧ ‖F (x i + (1 / 2 : ℝ) • v i)‖ < 1 / 100 ∧
        F '' T δ (x i) (v i) ⊆ WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          B B (F (x i + (1 / 2 : ℝ) • v i)) u ∧
        O ((δ ^ ε * k / 1000) * B ^ 2) ≤ μ
          (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
            B B (F (x i + (1 / 2 : ℝ) • v i)) u ∩ F '' (⋃ j, Y j)) := by
    obtain ⟨g, hg₂, hg₀, hT, hden⟩ := hfill i hi
    have hvne : v i ≠ 0 := by intro hh; have hh' := hvlo i; rw [hh, norm_zero] at hh'; norm_num at hh'
    have hmid : x i + (1 / 2 : ℝ) • v i ∈ P a b 4 z e := by
      have hh := WangZahlLot.Obl.wz_move_three_thick_grains_gain.convex_P a b 4 z e
        (hends i).1 (hends i).2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      convert hh using 1 <;> module
    have hcoord (j : Fin 3) (d : ℝ) (hx : |e (x i - z) j| ≤ d / 2)
        (hy : |e (x i + v i - z) j| ≤ d / 2) : |e (unit (v i)) j| ≤ 4 * d := by
      have hh := chord_unit_inner_bound (hvlo i)
        (u := boxAxis e j) (t := inner ℝ (boxAxis e j) z) (r := d / 2)
        (by rw [← inner_sub_right, inner_boxAxis]; exact hx)
        (by rw [← inner_sub_right, inner_boxAxis]; exact hy)
      rw [inner_boxAxis] at hh
      linarith
    obtain ⟨hB, hc, u, hu, hcover, hdense⟩ := filled_prism_net_data hδ hδa hab
      (by linarith : b ≤ 1 / 3) (by linarith : 5 * (a / 2) ≤ δ + 5 * (a / 2))
      (by linarith : δ + 5 * (a / 2) ≤ 4 * a) hk hksmall
      (by positivity : 0 ≤ δ ^ ε) (x i + (1 / 2 : ℝ) • v i) (unit (v i))
      (norm_unit hvne) e g f hf hfvol
      (by have hh := mem_ball_zero_iff.mp (hfball ⟨_, hmid, rfl⟩); linarith)
      (hcoord 0 a (hends i).1.1 (hends i).2.1)
      (hcoord 1 b (hends i).1.2.1 (hends i).2.2.1) hg₂ hg₀ (⋃ j, Y j) hden
    exact ⟨hB, u, hu, hc, (image_mono hT).trans hcover, hdense⟩
  obtain ⟨i₀, hi₀⟩ := hG
  have choices : ∀ i, ∃ u : Fin 3 → V, i ∈ G →
      Orthonormal ℝ u ∧ ‖F (x i + (1 / 2 : ℝ) • v i)‖ < 1 / 100 ∧
        F '' T δ (x i) (v i) ⊆ WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          B B (F (x i + (1 / 2 : ℝ) • v i)) u ∧
        O ((δ ^ ε * k / 1000) * B ^ 2) ≤ μ
          (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
            B B (F (x i + (1 / 2 : ℝ) • v i)) u ∩ F '' (⋃ j, Y j)) := by
    intro i
    by_cases hi : i ∈ G
    · obtain ⟨u, hu⟩ := (H i hi).2
      exact ⟨u, fun _ => hu⟩
    · exact ⟨fun _ => 0, fun hh => (hi hh).elim⟩
  choose u hu using choices
  exact ⟨G, u, ⟨i₀, hi₀⟩, hcard, (H i₀ hi₀).1, fun i hi => ⟨hstem i hi, hu i hi⟩⟩

/-- Broad flat short tubes produce a positive proportion of dense square prisms
after the fixed flat normalization. Whole short tubes, not only their shadings,
are contained in the selected prisms. -/
theorem flat_prism_dense_net_input_of_coefficients {n : ℕ} (hn : 0 < n) {δ a b θ β C lam D k : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hδa : δ ≤ a) (hab : a ≤ b)
    (hb : b ≤ 4) (hθ1 : θ ≤ 1) (hr : δ + 5 * (a / 2) ≤ 1 / 100)
    (hflat : 100 * (δ + 5 * (a / 2)) ≤ 3 * b)
    (hθ : 32 * (δ + 5 * (a / 2)) ≤ θ) (hθb : θ ≤ 3 * b)
    (hlam : 0 < lam) (hC : 0 < C) (hD : 0 < D) (hk : 0 < k) (hksmall : k ≤ 1 / 1000000000)
    (hsmall : C * (θ / (3 * b)) ^ β ≤ lam / 8)
    (hnum : D * (10 ^ 13 * ((3 * b) / θ) * (1 + Real.log (1 / δ))) ≤
      (lam / 16000) ^ 2 * (48 * lam))
    (x v : Fin n → V) (Y : Fin n → Set V) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hvlo : ∀ i, (1 / 4 : ℝ) ≤ ‖v i‖) (hvhi : ∀ i, ‖v i‖ ≤ 1)
    (hends : ∀ i, x i ∈ P a b 4 z e ∧ x i + v i ∈ P a b 4 z e)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hmass : O (768 * lam * δ ^ 2 * n) ≤ ∑ i, μ (Y i))
    (hbroad : ∀ (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ 3 * b →
      q n {i | p ∈ Y i ∧ pd (unit (v i)) u ≤ r} ≤
        C * (r / (3 * b)) ^ β * q n {i | p ∈ Y i})
    (f : V ≃ᵃ[ℝ] V)
    (hf : ∀ q i, f.linear q i = (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i * e q i)
    (hfvol : ∀ Q : Set V, μ (f '' Q) = O (1 / (4 * a * b)) * μ Q)
    (hfball : f '' P a b 4 z e ⊆ ball (0 : V) 1) :
    let F := f.trans (uniformMap hk).toAffineEquiv
    let B := 256 * k * δ / a
    ∃ (G : Finset (Fin n)) (u : Fin n → Fin 3 → V),
      G.Nonempty ∧ (lam / 8) * n ≤ (G.card : ℝ) ∧ B ≤ 1 / 1000000 ∧
      ∀ i ∈ G, O (48 * lam * δ ^ 2) ≤ μ (Y i) ∧ Orthonormal ℝ (u i) ∧ ‖F (x i + (1 / 2 : ℝ) • v i)‖ < 1 / 100 ∧
        F '' T δ (x i) (v i) ⊆ WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          B B (F (x i + (1 / 2 : ℝ) • v i)) (u i) ∧
        O ((D * k / 16000) * B ^ 2) ≤ μ
          (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
            B B (F (x i + (1 / 2 : ℝ) • v i)) (u i) ∩ F '' (⋃ j, Y j)) := by
  classical
  let F := f.trans (uniformMap hk).toAffineEquiv
  let B := 256 * k * δ / a
  have ha : 0 < a := hδ.trans_le hδa
  obtain ⟨G, hcard, hstem, hfill⟩ := flat_prism_filling_frames_of_coefficients hδ hδ1 ha hab hθ1 hr hflat hθ hθb
    hlam hC hD hsmall hnum x v Y z e hvlo hvhi hends hYm hYT hmass hbroad
  have hG : G.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < G.card :=
      (mul_pos (div_pos hlam (by norm_num)) (Nat.cast_pos.mpr hn)).trans_le hcard
    exact_mod_cast hp
  have H (i : Fin n) (hi : i ∈ G) : B ≤ 1 / 1000000 ∧
      ∃ u : Fin 3 → V, Orthonormal ℝ u ∧ ‖F (x i + (1 / 2 : ℝ) • v i)‖ < 1 / 100 ∧
        F '' T δ (x i) (v i) ⊆ WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          B B (F (x i + (1 / 2 : ℝ) • v i)) u ∧
        O ((D * k / 16000) * B ^ 2) ≤ μ
          (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
            B B (F (x i + (1 / 2 : ℝ) • v i)) u ∩ F '' (⋃ j, Y j)) := by
    obtain ⟨g, hg₂, hg₀, hT, hden⟩ := hfill i hi
    have hvne : v i ≠ 0 := by intro hh; have hh' := hvlo i; rw [hh, norm_zero] at hh'; norm_num at hh'
    have hmid : x i + (1 / 2 : ℝ) • v i ∈ P a b 4 z e := by
      have hh := WangZahlLot.Obl.wz_move_three_thick_grains_gain.convex_P a b 4 z e
        (hends i).1 (hends i).2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      convert hh using 1 <;> module
    have hcoord (j : Fin 3) (d : ℝ) (hx : |e (x i - z) j| ≤ d / 2)
        (hy : |e (x i + v i - z) j| ≤ d / 2) : |e (unit (v i)) j| ≤ 4 * d := by
      have hh := chord_unit_inner_bound (hvlo i)
        (u := boxAxis e j) (t := inner ℝ (boxAxis e j) z) (r := d / 2)
        (by rw [← inner_sub_right, inner_boxAxis]; exact hx)
        (by rw [← inner_sub_right, inner_boxAxis]; exact hy)
      rw [inner_boxAxis] at hh
      linarith
    obtain ⟨hB, hc, u, hu, hcover, hdense⟩ := filled_prism_net_data_wide hδ hδa hab hb (by linarith : 5 * (a / 2) ≤ δ + 5 * (a / 2))
      (by linarith : δ + 5 * (a / 2) ≤ 4 * a) hk hksmall
      (by positivity : 0 ≤ D) (x i + (1 / 2 : ℝ) • v i) (unit (v i))
      (norm_unit hvne) e g f hf hfvol
      (by have hh := mem_ball_zero_iff.mp (hfball ⟨_, hmid, rfl⟩); linarith)
      (hcoord 0 a (hends i).1.1 (hends i).2.1)
      (hcoord 1 b (hends i).1.2.1 (hends i).2.2.1) hg₂ hg₀ (⋃ j, Y j) hden
    exact ⟨hB, u, hu, hc, (image_mono hT).trans hcover, hdense⟩
  obtain ⟨i₀, hi₀⟩ := hG
  have choices : ∀ i, ∃ u : Fin 3 → V, i ∈ G →
      Orthonormal ℝ u ∧ ‖F (x i + (1 / 2 : ℝ) • v i)‖ < 1 / 100 ∧
        F '' T δ (x i) (v i) ⊆ WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          B B (F (x i + (1 / 2 : ℝ) • v i)) u ∧
        O ((D * k / 16000) * B ^ 2) ≤ μ
          (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
            B B (F (x i + (1 / 2 : ℝ) • v i)) u ∩ F '' (⋃ j, Y j)) := by
    intro i
    by_cases hi : i ∈ G
    · obtain ⟨u, hu⟩ := (H i hi).2
      exact ⟨u, fun _ => hu⟩
    · exact ⟨fun _ => 0, fun hh => (hi hh).elim⟩
  choose u hu using choices
  exact ⟨G, u, ⟨i₀, hi₀⟩, hcard, (H i₀ hi₀).1, fun i hi => ⟨hstem i hi, hu i hi⟩⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
