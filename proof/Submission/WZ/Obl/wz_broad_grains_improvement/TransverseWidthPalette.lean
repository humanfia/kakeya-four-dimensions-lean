-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.TransverseWidthPalette.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.CrossingSlab
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SmallPowers
import Submission.WZ.Obl.wz_move_three_thick_grains_gain.Box

/- Adapted from this workspace: o169/x0670, branch x0641, commit5642ec0,
PrismWidthClasses.lean. Its unaccepted module cannot be imported here. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement

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

/-- A fixed finite palette of transverse dimensions at a prescribed length. -/
def transverseWidthPalette (δ c : ℝ)
    (k : Fin ((dyExp 1 δ+1)*(dyExp 1 δ+1))) : ℝ × ℝ :=
  let ij : Fin (dyExp 1 δ+1) × Fin (dyExp 1 δ+1) := finProdFinEquiv.symm k
  (min c (1/(2:ℝ)^(ij.1:ℕ)), min c (1/(2:ℝ)^(ij.2:ℕ)))

/-- Every admissible pair rounds upward into the same finite palette,
by at most two in each direction and without increasing the long length. -/
theorem transverse_width_palette_round {δ a b c : ℝ}
    (hδ : 0 < δ) (hc1 : c ≤ 1) (hδa : δ ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    ∃ k : Fin ((dyExp 1 δ+1)*(dyExp 1 δ+1)),
      δ ≤ (transverseWidthPalette δ c k).1 ∧
      (transverseWidthPalette δ c k).1 ≤ (transverseWidthPalette δ c k).2 ∧
      (transverseWidthPalette δ c k).2 ≤ c ∧
      a ≤ (transverseWidthPalette δ c k).1 ∧ (transverseWidthPalette δ c k).1 ≤ 2*a ∧
      b ≤ (transverseWidthPalette δ c k).2 ∧ (transverseWidthPalette δ c k).2 ≤ 2*b := by
  let ka : Fin (dyExp 1 δ+1) := ⟨dyExp 1 a,Nat.lt_succ_of_le
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyExp_le (by norm_num) hδ hδa)⟩
  let kb : Fin (dyExp 1 δ+1) := ⟨dyExp 1 b,Nat.lt_succ_of_le
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyExp_le (by norm_num) hδ (hδa.trans hab))⟩
  have he : transverseWidthPalette δ c (finProdFinEquiv (ka,kb)) =
      (min c (dyUp 1 a),min c (dyUp 1 b)) := by
    simp [transverseWidthPalette,ka,kb,dyUp]
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have ha' : a ≤ min c (dyUp 1 a) := le_min (hab.trans hbc)
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.le_dyUp ha ((hab.trans hbc).trans hc1))
  have hb' : b ≤ min c (dyUp 1 b) := le_min hbc
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.le_dyUp hb (hbc.trans hc1))
  refine ⟨finProdFinEquiv (ka,kb),?_⟩
  rw [he]
  refine ⟨hδa.trans ha',?_,min_le_left _ _,ha',?_,hb',?_⟩
  · exact min_le_min_left c
      (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyUp_le_dyUp (by norm_num)
        (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyExp_le (by norm_num) ha hab))
  · exact (min_le_right _ _).trans
      (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyUp_lt ha (by norm_num)).le
  · exact (min_le_right _ _).trans
      (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyUp_lt hb (by norm_num)).le

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

end WangZahlLot.Obl.wz_broad_grains_improvement
