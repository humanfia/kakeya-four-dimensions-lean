-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PrismWidthClasses.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PrismWidthClasses.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/PrismWidthClasses.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.CrossingSlab
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SmallPowers
import Submission.WZ.Obl.wz_move_three_thick_grains_gain.Box

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Crosses)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale (dyExp dyUp)

/-- Enlarging just the two transverse sides preserves exact long-end
crossing at the same center, frame, and length. -/
theorem crosses_transverse_mono {δ a b a' b' c : ℝ} {x v z : V}
    {e : V ≃ₗᵢ[ℝ] V} (hc : 0 < c) (ha : a ≤ a') (hb : b ≤ b')
    (h : Crosses δ a b c x v z e) : Crosses δ a' b' c x v z e := by
  have hsub : P a b c z e ⊆ P a' b' c z e := by
    intro p hp
    exact ⟨hp.1.trans (by linarith), hp.2.1.trans (by linarith), hp.2.2⟩
  constructor
  · intro p hp
    have hclosed : IsClosed (P a' b' c z e) :=
      WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_isClosed a' b' c z e
    have hpP : p ∈ P a' b' c z e := hclosed.closure_eq ▸ hp.2.1
    have hp2 : |e (p - z) 2| ≤ c / 2 := hpP.2.2
    by_contra hne
    have hlt : |e (p - z) 2| < c / 2 := lt_of_le_of_ne hp2 hne
    exact hp.2.2 (interior_mono hsub (h.slab_subset hc ⟨hp.1, hlt⟩))
  · intro t ht
    obtain ⟨p, hp, he⟩ := h.2 t ht
    exact ⟨p, ⟨hp.1, hsub hp.2⟩, he⟩

/-- Doubling at most the two transverse dimensions costs at most four in
prism volume, with the long length fixed. -/
theorem prism_transverse_volume_le_four {a b a' b' c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc : 0 ≤ c)
    (haa' : a' ≤ 2 * a) (hbb' : b' ≤ 2 * b) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    μ (P a' b' c z e) ≤ (4 : ENNReal) * μ (P a b c z e) := by
  have hv : μ (P a b c z e) = O (a * b * c) :=
    WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P ha hb hc z e
  have hv' : μ (P a' b' c z e) = O (a' * b' * c) :=
    WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P ha' hb' hc z e
  rw [hv, hv']
  change ENNReal.ofReal (a' * b' * c) ≤ 4 * ENNReal.ofReal (a * b * c)
  rw [← show ENNReal.ofReal (4 : ℝ) = 4 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul haa' hbb' hb' (by positivity)) hc
  nlinarith

/-- A heavy pair of dyadic width classes has common enlarged dimensions.
The dimensions remain at most the original long length. -/
theorem select_prism_width_class {κ : Type*} [Fintype κ] {δ c : ℝ}
    (hδ : 0 < δ) (hc1 : c ≤ 1) (a b : κ → ℝ) (weight : κ → ENNReal)
    (hdim : ∀ k, δ ≤ a k ∧ a k ≤ b k ∧ b k ≤ c)
    (hpos : 0 < ∑ k, weight k) :
    ∃ (a' b' : ℝ) (Q : Finset κ), Q.Nonempty ∧
      δ ≤ a' ∧ a' ≤ b' ∧ b' ≤ c ∧
      (∀ k ∈ Q, a k ≤ a' ∧ a' ≤ 2 * a k ∧ b k ≤ b' ∧ b' ≤ 2 * b k) ∧
      (∑ k, weight k) ≤ (((dyExp 1 δ + 1) ^ 2 : ℕ) : ENNReal) * ∑ k ∈ Q, weight k := by
  classical
  let D := dyExp 1 δ + 1
  let lab : κ → Fin D × Fin D := fun k =>
    (⟨dyExp 1 (a k), Nat.lt_succ_of_le
      (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyExp_le (by norm_num) hδ (hdim k).1)⟩,
     ⟨dyExp 1 (b k), Nat.lt_succ_of_le
      (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyExp_le (by norm_num) hδ
        ((hdim k).1.trans (hdim k).2.1))⟩)
  let Q : Fin D × Fin D → Finset κ := fun p => Finset.univ.filter (fun k => lab k = p)
  let mass := fun p => ∑ k ∈ Q p, weight k
  have hsum : (∑ p, mass p) = ∑ k, weight k :=
    Finset.sum_fiberwise Finset.univ lab weight
  have hD : 0 < D := Nat.succ_pos _
  letI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ mass Finset.univ_nonempty
  have hmass : (∑ k, weight k) ≤ ((D ^ 2 : ℕ) : ENNReal) * mass p := by
    calc
      _ = ∑ q, mass q := hsum.symm
      _ ≤ ∑ _q : Fin D × Fin D, mass p := Finset.sum_le_sum fun q hq => hp q hq
      _ = _ := by simp [nsmul_eq_mul, pow_two]
  have hQne : (Q p).Nonempty := by
    by_contra hne
    have he : Q p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hz : mass p = 0 := by simp only [mass, he, Finset.sum_empty]
    rw [hz, mul_zero] at hmass
    exact (not_lt_of_ge hmass) hpos
  let a' := min c (1 / (2 : ℝ) ^ (p.1 : ℕ))
  let b' := min c (1 / (2 : ℝ) ^ (p.2 : ℕ))
  have hround (k : κ) (hk : k ∈ Q p) :
      a k ≤ a' ∧ a' ≤ 2 * a k ∧ b k ≤ b' ∧ b' ≤ 2 * b k := by
    have hl : lab k = p := (Finset.mem_filter.mp hk).2
    have ha : 0 < a k := hδ.trans_le (hdim k).1
    have hb : 0 < b k := ha.trans_le (hdim k).2.1
    have ha1 : a k ≤ 1 := (hdim k).2.1.trans ((hdim k).2.2.trans hc1)
    have hb1 : b k ≤ 1 := (hdim k).2.2.trans hc1
    have heA : a' = min c (dyUp 1 (a k)) := by
      dsimp only [a']
      rw [← hl]
      rfl
    have heB : b' = min c (dyUp 1 (b k)) := by
      dsimp only [b']
      rw [← hl]
      rfl
    rw [heA, heB]
    exact ⟨le_min ((hdim k).2.1.trans (hdim k).2.2)
        (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.le_dyUp ha ha1),
      (min_le_right _ _).trans
        (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyUp_lt ha (by norm_num)).le,
      le_min (hdim k).2.2 (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.le_dyUp hb hb1),
      (min_le_right _ _).trans
        (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyUp_lt hb (by norm_num)).le⟩
  obtain ⟨k, hk⟩ := hQne
  refine ⟨a', b', Q p, ⟨k, hk⟩, (hdim k).1.trans (hround k hk).1, ?_,
    min_le_left _ _, hround, hmass⟩
  have hl : lab k = p := (Finset.mem_filter.mp hk).2
  dsimp only [a', b']
  rw [← hl]
  change min c (dyUp 1 (a k)) ≤ min c (dyUp 1 (b k))
  apply min_le_min_left
  exact WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyUp_le_dyUp (by norm_num)
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyExp_le (by norm_num)
      (hδ.trans_le (hdim k).1) (hdim k).2.1)

/-- Two independent dyadic width choices cost only an arbitrarily small
power of the fine radius, uniformly before the radius is chosen. -/
theorem prism_width_class_budget {s : ℝ} (hs : 0 < s) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ d₀ →
      (((dyExp 1 δ + 1) ^ 2 : ℕ) : ℝ) ≤ δ ^ (-s) := by
  obtain ⟨d₀, hd₀, hcount⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.dyadic_size_power_bound
      (M := 1) (k := 1) (ν := s / 2) (by norm_num) (by norm_num) (by positivity)
  refine ⟨d₀, hd₀, ?_⟩
  intro δ hδ hδ1 hδ0
  have h := hcount δ hδ hδ1 hδ0
  simp only [Real.rpow_one] at h
  have he : (δ ^ (-(s / 2))) ^ 2 = δ ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    ring
  push_cast
  have hp : 0 ≤ δ ^ (-(s / 2)) := Real.rpow_nonneg hδ.le _
  have hn : 0 ≤ (dyExp 1 δ : ℝ) := Nat.cast_nonneg _
  nlinarith

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
