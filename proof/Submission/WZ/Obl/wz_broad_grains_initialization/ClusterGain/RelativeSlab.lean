-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain.RelativeSlab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.ClusterGain.Basic
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.KatzSeparation

/-!
# Cluster gain: relative slab count of a cluster

A cluster of fine unit tubes lying in a carrier of radius `ρ` and length `L ≤ 8` satisfies the
normalized slab count on the doubled carrier with constant
`max 2560 (20480 * l * n * ρ / m)`, where `l` is the global Frostman constant of the whole
family of `n` tubes and `m` is the size of the cluster. Thick slabs (`r ≥ ρ`) use the trivial
count, thin slabs the global bound together with `carrier_slab_volume`.
-/

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

namespace WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain

/-- Volume of a doubled carrier. -/
theorem dilated_carrier_volume_le {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (y w : Space)
    (hw : ‖w‖ = 1) :
    volume (Carrier (2 * L) (2 * ρ) y w) ≤ ENNReal.ofReal (16 * ρ ^ 2 * (2 * L + 4 * ρ)) := by
  obtain ⟨e, hew⟩ := exists_rotation_last hw
  have hy : (y + (1 / 2 : ℝ) • w) - (1 / 2 : ℝ) • w = y := by abel
  have hsub := carrier_subset_box (c := 2 * L) (ρ := 2 * ρ) (by positivity)
    (y + (1 / 2 : ℝ) • w) e hew
  rw [hy] at hsub
  calc volume (Carrier (2 * L) (2 * ρ) y w)
      ≤ volume (Factor.box (2 * (2 * ρ)) (2 * (2 * ρ)) (2 * L + 2 * (2 * ρ))
          (y + (1 / 2 : ℝ) • w) e) := measure_mono hsub
    _ = ENNReal.ofReal (2 * (2 * ρ) * (2 * (2 * ρ)) * (2 * L + 2 * (2 * ρ))) :=
        Factor.box_volume (by positivity) (by positivity) (by positivity) _ _
    _ = ENNReal.ofReal (16 * ρ ^ 2 * (2 * L + 4 * ρ)) := by congr 1; ring

/-- The relative slab count of a reindexed cluster lying in one carrier. -/
theorem cluster_slab_count {δ ρ L lg : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hL : 0 < L) (hL8 : L ≤ 8) (hlg : 0 ≤ lg)
    {n m : ℕ} (hm : 0 < m) {x v : Fin n → Space} (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Space) 1)
    (hF : ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (({i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          ball (0 : Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r}}.ncard : ℝ)) ≤
        ENNReal.ofReal (lg * n) * volume (ball (0 : Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r}))
    (g : Fin m → Fin n) (hg : Function.Injective g) {y w : Space} (hw : ‖w‖ = 1)
    (hcar : ∀ j, thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j))) ⊆ Carrier L ρ y w) :
    ReferenceSlabCount (Carrier (2 * L) (2 * ρ) y w)
      (max 2560 (20480 * lg * n * ρ / m)) (fun j => Tube δ (x (g j)) (v (g j))) := by
  intro u t r hu hr
  set D := Carrier (2 * L) (2 * ρ) y w with hDdef
  set Qs := {p : Space | |inner ℝ u p - t| ≤ r} with hQs
  set lc := max 2560 (20480 * lg * n * ρ / m) with hlc
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlc1 : 2560 ≤ lc := le_max_left _ _
  have hlc2 : 20480 * lg * n * ρ ≤ lc * m := by
    have := le_max_right 2560 (20480 * lg * n * ρ / m)
    rw [← hlc] at this
    calc 20480 * lg * n * ρ = 20480 * lg * n * ρ / m * m := by field_simp
      _ ≤ lc * m := by gcongr
  have hD : volume D ≤ ENNReal.ofReal (320 * ρ ^ 2) := by
    refine (dilated_carrier_volume_le hL.le hρ.le y w hw).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 2 * L + 4 * ρ ≤ 20 := by linarith
    nlinarith [sq_nonneg ρ]
  set S := {j | Tube δ (x (g j)) (v (g j)) ⊆ D ∩ Qs} with hSdef
  change ENNReal.ofReal (S.ncard : ℝ) * volume D ≤ ENNReal.ofReal (lc * m) * volume (D ∩ Qs)
  rcases S.eq_empty_or_nonempty with hE | ⟨j₀, hj₀⟩
  · rw [hE, Set.ncard_empty, Nat.cast_zero, ENNReal.ofReal_zero, zero_mul]
    exact bot_le
  have hj₀' : Tube δ (x (g j₀)) (v (g j₀)) ⊆ D ∩ Qs := hj₀
  have hlow := carrier_slab_volume hδ hρ hr hL (hv (g j₀)) hu (hcar j₀)
    (hj₀'.trans inter_subset_right)
  have hSm : (S.ncard : ℝ) ≤ m := by
    have := Set.ncard_le_ncard (Set.subset_univ S) (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact_mod_cast this
  have hN0 : (0 : ℝ) ≤ S.ncard := Nat.cast_nonneg _
  have hstep : ENNReal.ofReal (S.ncard : ℝ) * volume D ≤
      ENNReal.ofReal ((S.ncard : ℝ) * (320 * ρ ^ 2)) := by
    rw [ENNReal.ofReal_mul hN0]
    exact mul_le_mul_right hD _
  refine hstep.trans ?_
  rcases le_total ρ r with hρr | hrρ
  · rw [min_eq_left hρr] at hlow
    calc ENNReal.ofReal ((S.ncard : ℝ) * (320 * ρ ^ 2))
        ≤ ENNReal.ofReal ((lc * m) * (ρ * ρ / 8)) := by
          apply ENNReal.ofReal_le_ofReal
          calc (S.ncard : ℝ) * (320 * ρ ^ 2) ≤ m * (320 * ρ ^ 2) := by gcongr
            _ = (2560 * m) * (ρ * ρ / 8) := by ring
            _ ≤ (lc * m) * (ρ * ρ / 8) := by gcongr
      _ = ENNReal.ofReal (lc * m) * ENNReal.ofReal (ρ * ρ / 8) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (lc * m) * volume (D ∩ Qs) := mul_le_mul_right hlow _
  · rw [min_eq_right hrρ] at hlow
    -- the global count bounds the cluster count on thin slabs
    have hinj : (S.ncard : ℝ) ≤
        ({i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          ball (0 : Space) 1 ∩ Qs}.ncard : ℝ) := by
      have := Set.ncard_le_ncard_of_injOn g (s := S)
        (t := {i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Space) 1 ∩ Qs})
        (fun j hj => subset_inter (hball (g j)) ((show Tube δ (x (g j)) (v (g j)) ⊆ D ∩ Qs from hj).trans
          inter_subset_right)) hg.injOn (Set.toFinite _)
      exact_mod_cast this
    have hslab : volume (ball (0 : Space) 1 ∩ Qs) ≤ ENNReal.ofReal (8 * r) := by
      have := Factor.slab_inter_ball_volume hu t r (0 : Space) hr.le zero_le_one
      rw [inter_comm]
      refine this.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
    have hglob : (({i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          ball (0 : Space) 1 ∩ Qs}.ncard : ℝ)) ≤ lg * n * (8 * r) := by
      have h1 := (hF u t r hu hr).trans (mul_le_mul_right hslab _)
      rw [← ENNReal.ofReal_mul (by positivity)] at h1
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    calc ENNReal.ofReal ((S.ncard : ℝ) * (320 * ρ ^ 2))
        ≤ ENNReal.ofReal ((lc * m) * (r * ρ / 8)) := by
          apply ENNReal.ofReal_le_ofReal
          calc (S.ncard : ℝ) * (320 * ρ ^ 2) ≤ (lg * n * (8 * r)) * (320 * ρ ^ 2) := by
                gcongr; exact hinj.trans hglob
            _ = (20480 * lg * n * ρ) * (r * ρ / 8) := by ring
            _ ≤ (lc * m) * (r * ρ / 8) := by gcongr
      _ = ENNReal.ofReal (lc * m) * ENNReal.ofReal (r * ρ / 8) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (lc * m) * volume (D ∩ Qs) := mul_le_mul_right hlow _

/-- A carrier lies in a slab of half-width `ρ` normal to any unit vector orthogonal to its axis. -/
theorem carrier_subset_slab {L ρ : ℝ} {y w ν : Space} (hν : ‖ν‖ = 1)
    (hνw : inner ℝ ν w = 0) :
    Carrier L ρ y w ⊆ {p | |inner ℝ ν p - inner ℝ ν y| ≤ ρ} := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, -, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  show |inner ℝ ν p - inner ℝ ν y| ≤ ρ
  have hq : inner ℝ ν (y + ((1 - L) / 2) • w + s • (L • w)) = inner ℝ ν y := by
    simp only [inner_add_right, inner_smul_right, hνw]; ring
  have heq : inner ℝ ν p - inner ℝ ν y =
      inner ℝ ν (p - (y + ((1 - L) / 2) • w + s • (L • w))) := by
    rw [inner_sub_right, hq]
  rw [heq]
  calc |inner ℝ ν (p - (y + ((1 - L) / 2) • w + s • (L • w)))|
      ≤ ‖ν‖ * ‖p - (y + ((1 - L) / 2) • w + s • (L • w))‖ := abs_real_inner_le_norm _ _
    _ ≤ ρ := by rw [hν, one_mul, ← dist_eq_norm]; exact hpq.le

/-- The Frostman slab bound limits the number of fine tubes in one carrier. -/
theorem cluster_card_le {δ ρ L lg : ℝ} (hρ : 0 < ρ) (hlg : 0 ≤ lg) {n : ℕ}
    {x v : Fin n → Space}
    (hball : ∀ i, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Space) 1)
    (hF : ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (({i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          ball (0 : Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r}}.ncard : ℝ)) ≤
        ENNReal.ofReal (lg * n) * volume (ball (0 : Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r}))
    {S : Finset (Fin n)} {y w : Space} (hw : ‖w‖ = 1)
    (hcar : ∀ i ∈ S, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Carrier L ρ y w) :
    (S.card : ℝ) ≤ lg * n * (8 * ρ) := by
  obtain ⟨ν, hν, hνw⟩ := Factor.exists_orth_unit hw
  set Qs := {p : Space | |inner ℝ ν p - inner ℝ ν y| ≤ ρ} with hQs
  have hsub : (S : Set (Fin n)) ⊆
      {i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Space) 1 ∩ Qs} :=
    fun i hi => subset_inter (hball i) ((hcar i hi).trans (carrier_subset_slab hν hνw))
  have hcard : (S.card : ℝ) ≤
      ({i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Space) 1 ∩ Qs}.ncard : ℝ) := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  have hslab : volume (ball (0 : Space) 1 ∩ Qs) ≤ ENNReal.ofReal (8 * ρ) := by
    have := Factor.slab_inter_ball_volume hν (inner ℝ ν y) ρ (0 : Space) hρ.le zero_le_one
    rw [inter_comm]
    refine this.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  have h1 := (hF ν (inner ℝ ν y) ρ hν hρ).trans (mul_le_mul_right hslab _)
  rw [← ENNReal.ofReal_mul (by positivity)] at h1
  exact hcard.trans ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1)

end WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain
