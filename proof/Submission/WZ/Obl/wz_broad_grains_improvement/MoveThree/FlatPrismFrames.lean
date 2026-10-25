-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FlatPrismFrames.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FlatPrismFrames.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FlatPrismFrames.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FlatFramedStage
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FlatGeometry
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FlatScales

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open scoped ENNReal Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit norm_smul_unit pd pd_triangle pd_symm)

/-- Flat-prism filling with the center and adapted frame exposed for further
affine normalization. -/
theorem flat_prism_filling_frames_of_small_slab {n : ℕ} {δ a b θ β h lam ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (ha : 0 < a) (hab : a ≤ b)
    (hθ1 : θ ≤ 1) (hr : δ + 5 * (a / 2) ≤ 1 / 100)
    (hflat : 100 * (δ + 5 * (a / 2)) ≤ 3 * b)
    (hθ : 32 * (δ + 5 * (a / 2)) ≤ θ) (hθb : θ ≤ 3 * b)
    (hlam : 0 < lam)
    (hsmall : δ ^ (-h) * (θ / (3 * b)) ^ β ≤ lam / 8)
    (hnum : δ ^ ε * (10 ^ 13 * ((3 * b) / θ) * (1 + Real.log (1 / δ))) ≤
      (lam / 16000) ^ 2 * (48 * lam))
    (x v : Fin n → V) (Y : Fin n → Set V) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hvlo : ∀ i, (1 / 4 : ℝ) ≤ ‖v i‖) (hvhi : ∀ i, ‖v i‖ ≤ 1)
    (hends : ∀ i, x i ∈ P a b 4 z e ∧ x i + v i ∈ P a b 4 z e)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hmass : O (768 * lam * δ ^ 2 * n) ≤ ∑ i, volume (Y i))
    (hbroad : ∀ (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ 3 * b →
      q n {i | p ∈ Y i ∧ pd (unit (v i)) u ≤ r} ≤
        δ ^ (-h) * (r / (3 * b)) ^ β * q n {i | p ∈ Y i}) :
    ∃ G : Finset (Fin n), (lam / 8) * n ≤ (G.card : ℝ) ∧
      (∀ i ∈ G, O (48 * lam * δ ^ 2) ≤ volume (Y i)) ∧
      ∀ i ∈ G, ∃ (e' : V ≃ₗᵢ[ℝ] V),
        (∀ p, e' p 2 = inner ℝ (unit (v i)) p) ∧
        (∀ w, |e' w 0| ≤ 2 * (|inner ℝ (boxAxis e 0) w| +
          |inner ℝ (boxAxis e 0) (unit (v i))| * ‖w‖)) ∧
        T δ (x i) (v i) ⊆ P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e' ∧
        O (δ ^ ε) * volume (P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e') ≤
          volume (P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e' ∩ ⋃ j, Y j) := by
  let r := δ + 5 * (a / 2)
  let L := δ / (16 * r)
  let B := 2 * (3 * b) * δ / r
  have hδr : δ ≤ r := by dsimp [r]; linarith
  have hρ : 0 < 3 * b := by linarith
  obtain ⟨hB, hL3, hL, hBδ, hrL, hρL⟩ := flat_filling_scales_of_small_slab hδ hδr hr hflat
  have hB' : 2 * (3 * b) * δ / r = 6 * b * δ / r := by ring
  let w := fun i => unit (v i)
  let y := fun i => x i + (1 / 2 : ℝ) • v i - (1 / 2 : ℝ) • w i
  have hv0 (i) : v i ≠ 0 := by
    intro h
    have hh := hvlo i
    rw [h, norm_zero] at hh
    norm_num at hh
  have hw (i) : ‖w i‖ = 1 := norm_unit (hv0 i)
  have hT (i) : T δ (x i) (v i) ⊆ T δ (y i) (w i) := by
    have hh := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.image_tube_extend
      (AffineEquiv.refl ℝ V).toContinuousAffineEquiv (x i) (v i) (w i) (δ := δ)
      (by norm_num : (0 : ℝ) < 1) (norm_nonneg (v i)) (hvhi i)
      (norm_smul_unit (hv0 i)).symm (fun p q => by simp)
    simpa only [AffineEquiv.coe_toContinuousAffineEquiv, AffineEquiv.coe_refl,
      Set.image_id, one_mul, id_eq, T, WangZahlLot.Obl.wz_affine_robust_cluster_estimate.tube] using hh
  have hangle (i j : Fin n) : pd (w j) (w i) ≤ 8 * (3 * b) := by
    have hi := chord_in_prism_angle ha.le hab e (hvlo i) (hends i).1 (hends i).2
    have hj := chord_in_prism_angle ha.le hab e (hvlo j) (hends j).1 (hends j).2
    have hh := pd_triangle (w j) (boxAxis e 2) (w i)
    rw [pd_symm (boxAxis e 2) (w i)] at hh
    change pd (w i) (boxAxis e 2) ≤ 12 * b at hi
    change pd (w j) (boxAxis e 2) ≤ 12 * b at hj
    linarith
  have hslab (i : Fin n) : T δ (y i) (w i) ⊆
      {p | |inner ℝ (boxAxis e 0) p - inner ℝ (boxAxis e 0) z| ≤ r} :=
    chord_in_prism_slab e (hvlo i) (hends i).1 (hends i).2
  have hθδ : δ ≤ θ := by change 32 * r ≤ θ at hθ; linarith
  obtain ⟨G, _, hcard, hstem, hfill⟩ := flat_filling_with_frames_and_mass hδ hδ1 hρ hθδ hθb hθ1
    hlam hB hL3 hL hBδ hρL hsmall hnum y w Y Y hw hYm
    (fun i => (hYT i).trans (hT i)) hYm (fun _ => Set.Subset.rfl)
    Finset.univ (fun _ => (0 : Fin 1)) (by simpa using hmass)
    (by intro k p u s hu hsδ hsb; simpa only [q, Finset.mem_univ, true_and, Fin.eq_zero, and_true, pd, w]
          using hbroad p u s hu hsδ hsb)
    (by intro i _ j _ _ _; exact hangle i j)
    (fun _ => boxAxis e 0)
    (by intro i _; exact ⟨inner ℝ (boxAxis e 0) z, r, boxAxis_norm e 0,
          hslab i, hθ, hrL, fun j _ _ _ => hslab j⟩)
  refine ⟨G, hcard, hstem, ?_⟩
  intro i hi
  obtain ⟨e', hg₂, hg₀, hsub, hdense⟩ := hfill i hi
  have heq : y i + (1 / 2 : ℝ) • w i = x i + (1 / 2 : ℝ) • v i := by dsimp [y]; abel
  rw [hB', heq] at hsub hdense
  exact ⟨e', hg₂, hg₀, (hT i).trans hsub, hdense⟩

/-- A coefficient form of filling: the broadness and density errors can
be measured at the original scale, independently of the short-tube radius. -/
theorem flat_prism_filling_frames_of_coefficients {n : ℕ} {δ a b θ β C lam D : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (ha : 0 < a) (hab : a ≤ b)
    (hθ1 : θ ≤ 1) (hr : δ + 5 * (a / 2) ≤ 1 / 100)
    (hflat : 100 * (δ + 5 * (a / 2)) ≤ 3 * b)
    (hθ : 32 * (δ + 5 * (a / 2)) ≤ θ) (hθb : θ ≤ 3 * b)
    (hlam : 0 < lam) (hC : 0 < C) (hD : 0 < D)
    (hsmall : C * (θ / (3 * b)) ^ β ≤ lam / 8)
    (hnum : D * (10 ^ 13 * ((3 * b) / θ) * (1 + Real.log (1 / δ))) ≤
      (lam / 16000) ^ 2 * (48 * lam))
    (x v : Fin n → V) (Y : Fin n → Set V) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hvlo : ∀ i, (1 / 4 : ℝ) ≤ ‖v i‖) (hvhi : ∀ i, ‖v i‖ ≤ 1)
    (hends : ∀ i, x i ∈ P a b 4 z e ∧ x i + v i ∈ P a b 4 z e)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hmass : O (768 * lam * δ ^ 2 * n) ≤ ∑ i, volume (Y i))
    (hbroad : ∀ (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ 3 * b →
      q n {i | p ∈ Y i ∧ pd (unit (v i)) u ≤ r} ≤
        C * (r / (3 * b)) ^ β * q n {i | p ∈ Y i}) :
    ∃ G : Finset (Fin n), (lam / 8) * n ≤ (G.card : ℝ) ∧
      (∀ i ∈ G, O (48 * lam * δ ^ 2) ≤ volume (Y i)) ∧
      ∀ i ∈ G, ∃ (e' : V ≃ₗᵢ[ℝ] V),
        (∀ p, e' p 2 = inner ℝ (unit (v i)) p) ∧
        (∀ w, |e' w 0| ≤ 2 * (|inner ℝ (boxAxis e 0) w| +
          |inner ℝ (boxAxis e 0) (unit (v i))| * ‖w‖)) ∧
        T δ (x i) (v i) ⊆ P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e' ∧
        O (D) * volume (P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e') ≤
          volume (P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e' ∩ ⋃ j, Y j)  := by
  have hδne : δ ≠ 1 := ne_of_lt (hδ1.trans_lt (by norm_num))
  have hCp : δ ^ (-(-Real.logb δ C)) = C := by
    simpa only [neg_neg] using Real.rpow_logb hδ hδne hC
  have hDp : δ ^ Real.logb δ D = D := Real.rpow_logb hδ hδne hD
  have H := flat_prism_filling_frames_of_small_slab
    (h := -Real.logb δ C) (ε := Real.logb δ D)
    hδ hδ1 ha hab hθ1 hr hflat hθ hθb hlam
    (by simpa only [hCp] using hsmall) (by simpa only [hDp] using hnum)
    x v Y z e hvlo hvhi hends hYm hYT hmass
    (by simpa only [hCp] using hbroad)
  simpa only [hDp] using H

/-- Flat-prism filling with the center and adapted frame exposed for further
affine normalization. -/
theorem flat_prism_filling_frames_and_mass {n : ℕ} {δ a b θ β h lam ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (ha : 0 < a) (hab : a ≤ b)
    (hb : 3 * b ≤ 1) (hr : δ + 5 * (a / 2) ≤ 1 / 100)
    (hflat : 100 * (δ + 5 * (a / 2)) ≤ 3 * b)
    (hθ : 32 * (δ + 5 * (a / 2)) ≤ θ) (hθb : θ ≤ 3 * b)
    (hlam : 0 < lam)
    (hsmall : δ ^ (-h) * (θ / (3 * b)) ^ β ≤ lam / 8)
    (hnum : δ ^ ε * (10 ^ 13 * ((3 * b) / θ) * (1 + Real.log (1 / δ))) ≤
      (lam / 16000) ^ 2 * (48 * lam))
    (x v : Fin n → V) (Y : Fin n → Set V) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hvlo : ∀ i, (1 / 4 : ℝ) ≤ ‖v i‖) (hvhi : ∀ i, ‖v i‖ ≤ 1)
    (hends : ∀ i, x i ∈ P a b 4 z e ∧ x i + v i ∈ P a b 4 z e)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hmass : O (768 * lam * δ ^ 2 * n) ≤ ∑ i, volume (Y i))
    (hbroad : ∀ (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ 3 * b →
      q n {i | p ∈ Y i ∧ pd (unit (v i)) u ≤ r} ≤
        δ ^ (-h) * (r / (3 * b)) ^ β * q n {i | p ∈ Y i}) :
    ∃ G : Finset (Fin n), (lam / 8) * n ≤ (G.card : ℝ) ∧
      (∀ i ∈ G, O (48 * lam * δ ^ 2) ≤ volume (Y i)) ∧
      ∀ i ∈ G, ∃ (e' : V ≃ₗᵢ[ℝ] V),
        (∀ p, e' p 2 = inner ℝ (unit (v i)) p) ∧
        (∀ w, |e' w 0| ≤ 2 * (|inner ℝ (boxAxis e 0) w| +
          |inner ℝ (boxAxis e 0) (unit (v i))| * ‖w‖)) ∧
        T δ (x i) (v i) ⊆ P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e' ∧
        O (δ ^ ε) * volume (P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e') ≤
          volume (P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e' ∩ ⋃ j, Y j)  := by
  exact flat_prism_filling_frames_of_small_slab hδ hδ1 ha hab (hθb.trans hb)
    hr hflat hθ hθb hlam hsmall hnum x v Y z e hvlo hvhi hends hYm hYT hmass hbroad

/-- The frame-only interface is retained for existing callers. -/
theorem flat_prism_filling_frames {n : ℕ} {δ a b θ β h lam ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (ha : 0 < a) (hab : a ≤ b)
    (hb : 3 * b ≤ 1) (hr : δ + 5 * (a / 2) ≤ 1 / 100)
    (hflat : 100 * (δ + 5 * (a / 2)) ≤ 3 * b)
    (hθ : 32 * (δ + 5 * (a / 2)) ≤ θ) (hθb : θ ≤ 3 * b)
    (hlam : 0 < lam)
    (hsmall : δ ^ (-h) * (θ / (3 * b)) ^ β ≤ lam / 8)
    (hnum : δ ^ ε * (10 ^ 13 * ((3 * b) / θ) * (1 + Real.log (1 / δ))) ≤
      (lam / 16000) ^ 2 * (48 * lam))
    (x v : Fin n → V) (Y : Fin n → Set V) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hvlo : ∀ i, (1 / 4 : ℝ) ≤ ‖v i‖) (hvhi : ∀ i, ‖v i‖ ≤ 1)
    (hends : ∀ i, x i ∈ P a b 4 z e ∧ x i + v i ∈ P a b 4 z e)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hmass : O (768 * lam * δ ^ 2 * n) ≤ ∑ i, volume (Y i))
    (hbroad : ∀ (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ 3 * b →
      q n {i | p ∈ Y i ∧ pd (unit (v i)) u ≤ r} ≤
        δ ^ (-h) * (r / (3 * b)) ^ β * q n {i | p ∈ Y i}) :
    ∃ G : Finset (Fin n), (lam / 8) * n ≤ (G.card : ℝ) ∧
      ∀ i ∈ G, ∃ (e' : V ≃ₗᵢ[ℝ] V),
        (∀ p, e' p 2 = inner ℝ (unit (v i)) p) ∧
        (∀ w, |e' w 0| ≤ 2 * (|inner ℝ (boxAxis e 0) w| +
          |inner ℝ (boxAxis e 0) (unit (v i))| * ‖w‖)) ∧
        T δ (x i) (v i) ⊆ P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e' ∧
        O (δ ^ ε) * volume (P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e') ≤
          volume (P (10 * δ) (6 * b * δ / (δ + 5 * (a / 2))) 2 (x i + (1 / 2 : ℝ) • v i) e' ∩ ⋃ j, Y j) := by
  obtain ⟨G, hcard, _, H⟩ := flat_prism_filling_frames_and_mass
    hδ hδ1 ha hab hb hr hflat hθ hθb hlam hsmall hnum
    x v Y z e hvlo hvhi hends hYm hYT hmass hbroad
  exact ⟨G, hcard, H⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
