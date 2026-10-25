-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.ThickGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodPowers
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularShading
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DenseGrains
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenBridge
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainCardinality
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry

/-!
# Thick grains give the volume gain (WZ Lemma 8.2 and Lemma 8.3, Step 1)

If the grains of a frozen two-scale grains decomposition have thickness
`a ≥ 2 δ^(1-b)`, then the union of the original shadings is dense in balls of
radius `δ^(1-b)/2` around a fixed share of the fine incidence mass.  The
neighbourhood estimate of o095 (`neighborhood_power_gain`, a frozen form of
WZ Corollary 5.19) then gives the volume gain with exponent `α = b ω / 2`.

The argument: keep the grains of density at least `δ^h/2` (half of the grain
mass), regularize each kept grain at radius `s = δ^(1-b)/2`, and transfer the
retained grain mass back to the fine shadings using the uniform multiplicity
of the frozen grains.  At every retained fine point the regular grain has
density `δ^h/32000` in its own box near that point, and a box whose sides are
at least `4 s` contains a ball of radius `s/8` inside every `s`-ball centred in it.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory Set Metric
open scoped ENNReal

/-- The frozen box is the box of o094. -/
theorem P_eq_Box (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    P a b c z e = WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Box a b c z e := rfl

/-- Moving a coordinate a quarter step towards the centre leaves room `s/4`. -/
lemma shift_abs_le {x W s : ℝ} (hs : 0 < s) (hW : 2 * s ≤ W) (hx : |x| ≤ W) :
    |x + (if 0 ≤ x then -(s / 4) else s / 4)| ≤ W - s / 4 := by
  have hx' := abs_le.mp hx
  split_ifs with h
  · rw [abs_le]
    constructor <;> linarith
  · rw [not_le] at h
    rw [abs_le]
    constructor <;> linarith

/-- Every `s`-ball centred in a box with all sides at least `4 s` meets the box in
volume at least `s^3/512`. -/
theorem box_ball_volume {a b c s : ℝ} {z p : V} {e : V ≃ₗᵢ[ℝ] V} (hs : 0 < s)
    (ha : 4 * s ≤ a) (hb : 4 * s ≤ b) (hc : 4 * s ≤ c) (hp : p ∈ P a b c z e) :
    O (s ^ 3 / 512) ≤ μ (P a b c z e ∩ ball p s) := by
  let u : V := e (p - z)
  let t : V := WithLp.toLp 2 (fun i => if 0 ≤ u i then -(s / 4) else s / 4)
  have ht : ∀ i, t i = if 0 ≤ u i then -(s / 4) else s / 4 := fun i => rfl
  have htabs : ∀ i, |t i| ≤ s / 4 := by
    intro i
    rw [ht]
    split_ifs
    · rw [abs_neg, abs_of_pos (by positivity)]
    · rw [abs_of_pos (by positivity)]
  have htnorm : ‖t‖ ≤ 2 * (s / 4) :=
    WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le (by positivity) htabs
  let p' : V := p + e.symm t
  have hp0 : |u 0| ≤ a / 2 := hp.1
  have hp1 : |u 1| ≤ b / 2 := hp.2.1
  have hp2 : |u 2| ≤ c / 2 := hp.2.2
  have hsub : ball p' (s / 8) ⊆ P a b c z e ∩ ball p s := by
    intro q hq
    have hq' : ‖q - p'‖ < s / 8 := by rwa [mem_ball, dist_eq_norm] at hq
    have hdecomp : e (q - z) = e (q - p') + (u + t) := by
      have hqz : q - z = (q - p') + ((p - z) + e.symm t) := by
        simp only [p']
        abel
      rw [hqz, map_add, map_add, LinearIsometryEquiv.apply_symm_apply]
    have hcoord : ∀ i, |e (q - z) i| ≤ ‖q - p'‖ + |u i + t i| := by
      intro i
      rw [hdecomp]
      calc |(e (q - p') + (u + t)) i| = |e (q - p') i + (u i + t i)| := by
            simp only [PiLp.add_apply]
        _ ≤ |e (q - p') i| + |u i + t i| := abs_add_le _ _
        _ ≤ ‖e (q - p')‖ + |u i + t i| := by
          gcongr
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (e (q - p')) i
        _ = ‖q - p'‖ + |u i + t i| := by rw [LinearIsometryEquiv.norm_map]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · have h1 := hcoord 0
      have h2 : |u 0 + t 0| ≤ a / 2 - s / 4 := by
        rw [ht]; exact shift_abs_le hs (by linarith) hp0
      change |e (q - z) 0| ≤ a / 2
      linarith
    · have h1 := hcoord 1
      have h2 : |u 1 + t 1| ≤ b / 2 - s / 4 := by
        rw [ht]; exact shift_abs_le hs (by linarith) hp1
      change |e (q - z) 1| ≤ b / 2
      linarith
    · have h1 := hcoord 2
      have h2 : |u 2 + t 2| ≤ c / 2 - s / 4 := by
        rw [ht]; exact shift_abs_le hs (by linarith) hp2
      change |e (q - z) 2| ≤ c / 2
      linarith
    · rw [mem_ball, dist_eq_norm]
      have hpp : q - p = (q - p') + e.symm t := by
        simp only [p']
        abel
      rw [hpp]
      calc ‖(q - p') + e.symm t‖ ≤ ‖q - p'‖ + ‖e.symm t‖ := norm_add_le _ _
        _ = ‖q - p'‖ + ‖t‖ := by rw [LinearIsometryEquiv.norm_map]
        _ < s := by linarith
  calc O (s ^ 3 / 512) = ENNReal.ofReal ((s / 8) ^ 3) := by congr 1; ring
    _ ≤ volume (ball p' (s / 8)) :=
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.ball_volume_lower p' (by positivity)
    _ ≤ μ (P a b c z e ∩ ball p s) := measure_mono hsub

/-- An explicit cutoff making a positive power of `δ` small. -/
lemma small_rpow {p K : ℝ} (hp : 0 < p) (hK : 0 < K) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → δ ^ p ≤ K := by
  refine ⟨K ^ (1 / p), Real.rpow_pos_of_pos hK _, fun δ hδ hδd => ?_⟩
  calc δ ^ p ≤ (K ^ (1 / p)) ^ p := Real.rpow_le_rpow hδ.le hδd hp.le
    _ = K := by rw [← Real.rpow_mul hK.le, one_div_mul_cancel hp.ne', Real.rpow_one]

/-- A constant sum of real masses. -/
lemma sum_const_ofReal (L : ℕ) (x : ℝ) : (∑ _j : Fin L, O x) = O (L * x) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [O]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

lemma ofReal_half : O (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
  norm_num [O, ENNReal.ofReal_div_of_pos]

set_option maxHeartbeats 1000000 in
/-- **WZ Lemma 8.2 / Lemma 8.3, Step 1, frozen form.** Thick grains give the gain.

For every `b ∈ (0,1]` there are `κ, h₀, d₀ > 0` such that at every scale
`δ ≤ d₀` and every error `h ≤ h₀`: an admissible family (original indices) with
a frozen cover `C` (any below-slab clause `β`) and frozen grains `H` (any length
bound `b'` and local coefficient `g`) of thickness `a ≥ 2 δ^(1-b)` has the volume
gain with exponent `α = b ω / 2`. -/
theorem thick_grains_gain {σ ω : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω)
    (hω1 : ω ≤ 1) (hE : E σ ω) (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ κ h₀ d₀ : ℝ, 0 < κ ∧ 0 < h₀ ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
    ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ h₀ →
    ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
    ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ) (y w : Fin N → V)
      (f : Fin n → Fin N) (β : Prop), C δ h n x v Y S Z ρ N y w f β →
    ∀ a c b' g : ℝ, H δ h n x v S Z ρ N y w f a c b' g → 2 * δ ^ (1 - b) ≤ a →
    O (κ * δ ^ (ω - b * ω / 2) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) := by
  classical
  obtain ⟨κ, ηL, dL, hκ, hηL, hdL, hdL1, Hgain⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.neighborhood_power_gain hσ.le hσ2 hω hE
      (b * ω / 8) (by positivity)
  set h₀ : ℝ := min (b * ω / 88) (ηL / 3) with hh₀
  have hh₀pos : 0 < h₀ := lt_min (by positivity) (by positivity)
  have hh₀b : h₀ ≤ b * ω / 88 := min_le_left _ _
  have hh₀η : h₀ ≤ ηL / 3 := min_le_right _ _
  have hbω : b * ω ≤ 1 := by
    calc b * ω ≤ 1 * 1 := mul_le_mul hb1 hω1 hω.le zero_le_one
      _ = 1 := by ring
  obtain ⟨d1, hd1, H1⟩ := small_rpow (p := b) hb (K := 1 / 6) (by norm_num)
  obtain ⟨d2, hd2, H2⟩ := small_rpow (p := h₀) hh₀pos (K := 1 / 8) (by norm_num)
  obtain ⟨d3, hd3, H3⟩ := small_rpow (p := 17 * h₀) (by positivity) (K := 1 / 16384000)
    (by norm_num)
  obtain ⟨d4, hd4, H4⟩ := small_rpow (p := ηL) hηL (K := 1 / 128) (by norm_num)
  set d₀ : ℝ := min (1 / 100) (min dL (min d1 (min d2 (min d3 d4)))) with hd₀
  have hd₀pos : 0 < d₀ :=
    lt_min (by norm_num) (lt_min hdL (lt_min hd1 (lt_min hd2 (lt_min hd3 hd4))))
  refine ⟨κ, h₀, d₀, hκ, hh₀pos, hd₀pos, min_le_left _ _, ?_⟩
  intro δ h hδ hδd hh hhh n x v Y hA S Z ρ N y w f β hC a c b' g hH hthick
  -- scale facts
  have hδ100 : δ ≤ 1 / 100 := hδd.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hδdL : δ ≤ dL := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd1 : δ ≤ d1 := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδd2 : δ ≤ d2 := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hδd3 : δ ≤ d3 := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδd4 : δ ≤ d4 := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hδb : δ ^ b ≤ 1 / 6 := H1 δ hδ hδd1
  have hδh₀ : δ ^ h₀ ≤ 1 / 8 := H2 δ hδ hδd2
  have hδ17 : δ ^ (17 * h₀) ≤ 1 / 16384000 := H3 δ hδ hδd3
  have hδη : δ ^ ηL ≤ 1 / 128 := H4 δ hδ hδd4
  -- unpack the cover and the grains
  obtain ⟨hZ, hmassZ, -⟩ := hC
  obtain ⟨L, z, e, G, γ, m, hda, hab, hbc, hc1, hgeom, hdisj, hunion, hmassG, hmult,
    -, -, -⟩ := hH
  have ha : 0 < a := hδ.trans_le hda
  have hρc : 0 < ρ * c := ha.trans_le hab
  have hcpos : 0 < c := hρc.trans_le hbc
  set s : ℝ := δ ^ (1 - b) / 2 with hs_def
  have hs : 0 < s := by positivity
  have hs4a : 4 * s ≤ a := by rw [hs_def]; linarith
  -- the fibre structure in the language of o095
  have hsupport : ∀ i, i ∉ S → Z i = ∅ := fun i hi => (hZ i).2.2 hi
  have heq : ∀ k, WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber γ G k =
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber f Z k := by
    intro k
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_eq_supported f hsupport k]
    exact hunion k
  obtain ⟨m', hm'0, hlevel⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.fine_level_of_UF hsupport ⟨m, hmult⟩
  -- the grain boxes
  let U : Fin L → Set V := fun j => P a (ρ * c) c (z j) (e j)
  have hUvol : ∀ j, volume (U j) = O (a * (ρ * c) * c) := fun j =>
    WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha.le hρc.le hcpos.le (z j) (e j)
  have hUconv : ∀ j, Convex ℝ (U j) := fun j =>
    WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_convex _ _ _ _ _
  have hUclosed : ∀ j, IsClosed (U j) := fun j =>
    WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_isClosed _ _ _ _ _
  have hUcpt : ∀ j, IsCompact (U j) := fun j =>
    WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_compact hab hbc hcpos.le _ _
  have hGm : ∀ j, MeasurableSet (G j) := fun j => (hgeom j).1
  have hGU : ∀ j, G j ⊆ U j := fun j => (hgeom j).2.1
  have hGfin : (∑ j, volume (G j)) ≠ ⊤ := by
    apply ne_of_lt
    apply ENNReal.sum_lt_top.mpr
    intro j _
    apply lt_of_le_of_lt (measure_mono (hGU j))
    rw [hUvol j]
    exact ENNReal.ofReal_lt_top
  -- keep the grains of density at least `δ^h/2`
  have hbudget : (∑ j, O (δ ^ h / 2) * volume (U j)) ≤
      (1 / 2 : ℝ≥0∞) * ∑ j, volume (G j) := by
    calc (∑ j, O (δ ^ h / 2) * volume (U j))
        = ∑ _j : Fin L, O (δ ^ h / 2 * (a * (ρ * c) * c)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hUvol j, ← ENNReal.ofReal_mul (by positivity)]
      _ = O (L * (δ ^ h / 2 * (a * (ρ * c) * c))) := sum_const_ofReal L _
      _ = O (1 / 2) * O (δ ^ h * L * a * (ρ * c) * c) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
      _ ≤ (1 / 2 : ℝ≥0∞) * ∑ j, volume (G j) := by
          rw [ofReal_half]
          exact mul_le_mul' le_rfl hmassG
  obtain ⟨W', hW', hW'mass, hW'dense⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.dense_individual_refinement G U hGm hGfin
      hbudget
  -- regularize every kept grain at radius `s`
  have hreg : ∀ j, ∃ R : Set V, MeasurableSet R ∧ R ⊆ W' j ∧
      (1 / 2 : ℝ≥0∞) * volume (W' j) ≤ volume R ∧
      ∀ p ∈ R, O (δ ^ h / 2 / (16000 * ((1 : ℕ) : ℝ))) * volume (U j ∩ ball p s) ≤
        volume (R ∩ ball p s) := by
    intro j
    by_cases hj : W' j = ∅
    · refine ⟨∅, MeasurableSet.empty, empty_subset _, ?_, fun p hp => absurd hp (by simp)⟩
      rw [hj]
      simp
    · obtain ⟨R, hRm, hRW, hRmass, hRreg⟩ :=
        WangZahlLot.Obl.wz_clustered_cover_volume_gain.convex_regular_subshading_finite
          (hUconv j) (hUclosed j).measurableSet (hUcpt j).totallyBounded
          (by rw [hUvol j]; exact ENNReal.ofReal_ne_top) (hW' j).1 ((hW' j).2.trans (hGU j))
          (lam := δ ^ h / 2) (by positivity) (hW'dense j hj) (k := 1) one_pos (fun _ => s)
          (fun _ => hs)
      exact ⟨R, hRm, hRW, hRmass, fun p hp => hRreg p hp 0⟩
  choose R hRm hRW hRmass hRreg using hreg
  have hRG : ∀ j, R j ⊆ G j := fun j => (hRW j).trans (hW' j).2
  have hRsum : O (1 / 4) * ∑ j, volume (G j) ≤ ∑ j, volume (R j) := by
    calc O (1 / 4) * ∑ j, volume (G j)
        = (1 / 2 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * ∑ j, volume (G j)) := by
          rw [← mul_assoc, ← ofReal_half, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
      _ ≤ (1 / 2 : ℝ≥0∞) * ∑ j, volume (W' j) := mul_le_mul' le_rfl hW'mass
      _ = ∑ j, (1 / 2 : ℝ≥0∞) * volume (W' j) := Finset.mul_sum _ _ _
      _ ≤ ∑ j, volume (R j) := Finset.sum_le_sum fun j _ => hRmass j
  -- transfer the retained grain mass to the fine shadings
  obtain ⟨W, hW, hWmass, hWfib⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.grain_refinement_transfer f γ Z G R
      hm'0 (by norm_num : (0 : ℝ) ≤ 1 / 4) (fun i => (hZ i).1) hGm hRm hRG hdisj heq hlevel
      hRsum
  -- every grain lies in the original union
  have hGY : ∀ j, G j ⊆ ⋃ i, Y i := by
    intro j p hp
    have hp' : p ∈ WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber f Z (γ j) := by
      rw [← heq]
      exact ⟨j, rfl, hp⟩
    obtain ⟨i, -, hi⟩ := hp'
    exact mem_iUnion.mpr ⟨i, (hZ i).2.1 hi⟩
  -- the neighbourhood estimate
  have hA' := hA
  have hcount := WangZahlLot.Obl.wz_clustered_cover_volume_gain.admissible_count_eight hδ hA
  have hnbound := WangZahlLot.Obl.wz_clustered_cover_volume_gain.power_count_bound hδ hcount
  have hhle1 : h ≤ 1 := hhh.trans (hh₀b.trans (by linarith))
  have hnmax : (n : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) := by
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.square_rpow hδ]
    apply hnbound.trans
    have hinv : (8 : ℝ) ≤ δ ^ (-(198 - h)) := by
      have h1 : δ ^ (-(1 : ℝ)) ≤ δ ^ (-(198 - h)) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      have h2 : (100 : ℝ) ≤ δ ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg_one]
        rw [le_inv_comm₀ (by norm_num) hδ]
        linarith
      linarith
    calc 8 * δ ^ (-(h + 2)) ≤ δ ^ (-(198 - h)) * δ ^ (-(h + 2)) :=
          mul_le_mul_of_nonneg_right hinv (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (2 * (-100 : ℝ)) := by
          rw [← Real.rpow_add hδ]
          congr 1
          ring
  have hδsq : δ ^ (2 : ℕ) ≤ dL := by
    calc δ ^ (2 : ℕ) = δ * δ := by ring
      _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hδ1 hδ.le
      _ ≤ dL := by linarith
  have hδsplit : δ = δ ^ b * δ ^ (1 - b) := by
    rw [← Real.rpow_add hδ]
    simp
  have hδs6 : δ ≤ δ ^ (1 - b) / 6 := by
    have hpos : 0 ≤ δ ^ (1 - b) := Real.rpow_nonneg hδ.le _
    calc δ = δ ^ b * δ ^ (1 - b) := hδsplit
      _ ≤ 1 / 6 * δ ^ (1 - b) := mul_le_mul_of_nonneg_right hδb hpos
      _ = δ ^ (1 - b) / 6 := by ring
  have hδs48 : δ ^ (2 : ℕ) ≤ (δ ^ (1 - b) / 6) / 8 := by
    calc δ ^ (2 : ℕ) = δ * δ := by ring
      _ ≤ (1 / 8) * (δ ^ (1 - b) / 6) := mul_le_mul (by linarith) hδs6 hδ.le (by norm_num)
      _ = (δ ^ (1 - b) / 6) / 8 := by ring
  have h128 : 128 * (δ ^ (2 : ℕ)) ^ ηL ≤ δ ^ (3 * h₀) := by
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.square_rpow hδ]
    have hsplit : δ ^ (2 * ηL) = δ ^ ηL * δ ^ ηL := by
      rw [← Real.rpow_add hδ]
      ring_nf
    rw [hsplit]
    have hle : δ ^ ηL ≤ δ ^ (3 * h₀) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have hpos : 0 ≤ δ ^ ηL := Real.rpow_nonneg hδ.le _
    calc 128 * (δ ^ ηL * δ ^ ηL) = (128 * δ ^ ηL) * δ ^ ηL := by ring
      _ ≤ 1 * δ ^ ηL := mul_le_mul_of_nonneg_right (by linarith) hpos
      _ ≤ δ ^ (3 * h₀) := by linarith
  have hbudgetν : 7 * (3 * h₀) + 2 * (b * ω / 8) + h ≤ b * ω / 2 := by linarith
  -- retained fine mass
  have hYmass : O (δ ^ h * n * δ ^ 2) ≤ ∑ i, volume (Y i) := hA.2.2.2.1
  have hZsum : (∑ i ∈ S, volume (Z i)) ≤ ∑ i, volume (Z i) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hmassW : O (δ ^ (3 * h₀) * n * δ ^ 2) ≤ ∑ i, volume (W i) := by
    have hpow : δ ^ (3 * h₀) ≤ 1 / 4 / 2 * (δ ^ h * δ ^ h) := by
      have h1 : δ ^ (3 * h₀) = δ ^ h₀ * δ ^ (2 * h₀) := by
        rw [← Real.rpow_add hδ]
        ring_nf
      have h2 : δ ^ (2 * h₀) ≤ δ ^ h * δ ^ h := by
        rw [← Real.rpow_add hδ]
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      rw [h1]
      have hpos : 0 ≤ δ ^ (2 * h₀) := Real.rpow_nonneg hδ.le _
      calc δ ^ h₀ * δ ^ (2 * h₀) ≤ 1 / 8 * δ ^ (2 * h₀) :=
            mul_le_mul_of_nonneg_right hδh₀ hpos
        _ ≤ 1 / 8 * (δ ^ h * δ ^ h) := by linarith
        _ = 1 / 4 / 2 * (δ ^ h * δ ^ h) := by ring
    calc O (δ ^ (3 * h₀) * n * δ ^ 2)
        ≤ O (1 / 4 / 2) * (O (δ ^ h) * O (δ ^ h * n * δ ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hn0 : (0 : ℝ) ≤ n * δ ^ 2 := by positivity
          calc δ ^ (3 * h₀) * n * δ ^ 2 = δ ^ (3 * h₀) * (n * δ ^ 2) := by ring
            _ ≤ (1 / 4 / 2 * (δ ^ h * δ ^ h)) * (n * δ ^ 2) :=
                mul_le_mul_of_nonneg_right hpow hn0
            _ = 1 / 4 / 2 * (δ ^ h * (δ ^ h * n * δ ^ 2)) := by ring
      _ ≤ O (1 / 4 / 2) * (O (δ ^ h) * ∑ i, volume (Y i)) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hYmass)
      _ ≤ O (1 / 4 / 2) * ∑ i, volume (Z i) :=
          mul_le_mul' le_rfl (hmassZ.trans hZsum)
      _ ≤ ∑ i, volume (W i) := hWmass
  -- density of the original union around retained fine points
  have hdensW : ∀ i p, p ∈ W i → O (δ ^ (6 * (3 * h₀)) * (δ ^ (1 - b) / 2) ^ 3) ≤
      volume ((⋃ i, Y i) ∩ ball p (δ ^ (1 - b) / 2)) := by
    intro i p hp
    have hpfib : p ∈ WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber γ R (f i) := by
      rw [← hWfib]
      exact ⟨i, rfl, hp⟩
    obtain ⟨j, -, hpj⟩ := hpfib
    have hpU : p ∈ U j := hGU j (hRG j hpj)
    have hbox := box_ball_volume (a := a) (b := ρ * c) (c := c) (z := z j) (e := e j) hs hs4a
      (hs4a.trans hab) ((hs4a.trans hab).trans hbc) hpU
    have hdens : O (δ ^ h / 2 / (16000 * ((1 : ℕ) : ℝ))) * O (s ^ 3 / 512) ≤
        volume ((⋃ i, Y i) ∩ ball p s) := by
      calc O (δ ^ h / 2 / (16000 * ((1 : ℕ) : ℝ))) * O (s ^ 3 / 512)
          ≤ O (δ ^ h / 2 / (16000 * ((1 : ℕ) : ℝ))) * volume (U j ∩ ball p s) :=
            mul_le_mul' le_rfl hbox
        _ ≤ volume (R j ∩ ball p s) := hRreg j p hpj
        _ ≤ volume ((⋃ i, Y i) ∩ ball p s) :=
            measure_mono (inter_subset_inter_left _ ((hRG j).trans (hGY j)))
    refine le_trans ?_ hdens
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hpow : δ ^ (6 * (3 * h₀)) ≤ δ ^ h / 16384000 := by
      have h1 : δ ^ (6 * (3 * h₀)) = δ ^ (17 * h₀) * δ ^ h₀ := by
        rw [← Real.rpow_add hδ]
        ring_nf
      have h2 : δ ^ h₀ ≤ δ ^ h := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhh
      rw [h1]
      have hpos : 0 ≤ δ ^ h₀ := Real.rpow_nonneg hδ.le _
      calc δ ^ (17 * h₀) * δ ^ h₀ ≤ 1 / 16384000 * δ ^ h :=
            mul_le_mul hδ17 h2 hpos (by norm_num)
        _ = δ ^ h / 16384000 := by ring
    have hs3 : (0 : ℝ) ≤ s ^ 3 := by positivity
    rw [← hs_def]
    calc δ ^ (6 * (3 * h₀)) * s ^ 3 ≤ δ ^ h / 16384000 * s ^ 3 :=
          mul_le_mul_of_nonneg_right hpow hs3
      _ = δ ^ h / 2 / (16000 * ((1 : ℕ) : ℝ)) * (s ^ 3 / 512) := by
          push_cast
          ring
  exact Hgain δ h b (3 * h₀) hδ hδ1 hh hb.le hb1 hδsq hδs6 hδs48 h128 hbudgetν n x v Y W
    hnmax hA (fun i => ⟨(hW i).1, (hW i).2.trans (hZ i).2.1⟩) hmassW hdensW

end WangZahlLot.Obl.wz_broad_grains_improvement
