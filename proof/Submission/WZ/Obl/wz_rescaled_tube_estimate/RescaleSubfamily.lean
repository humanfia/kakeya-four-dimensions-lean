-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_tube_estimate.RescaleSubfamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_tube_estimate.RescaleDegree
import Submission.WZ.Obl.wz_rescaled_tube_estimate.WeightedSelection
import Submission.WZ.Obl.wz_rescaled_tube_estimate.SlabTransport
import Submission.WZ.Obl.wz_rescaled_tube_estimate.LocalScale
import Submission.WZ.Obl.wz_rescaled_tube_estimate.RecoverEstimate

/-!
# The rescaled essentially distinct subfamily of a fibre

A fibre of `δ`-tubes inside `Tube ρ y w` (essentially distinct, `δ^η`-dense, with convex count
`m` and the below-slab count `l` in the two-fold dilate) is mapped by the anisotropic rescaling to
tubes of radius `δ' = ρ⁻¹ δ / 100` in the unit ball. A subfamily of these, carrying a fixed share
`1/D` of the shading mass, is essentially distinct, and it inherits the convex count `100 m`,
the Frostman slab count `10⁶ l n / k` and density `δ^η / (100 D)`.
-/

namespace WangZahlLot.Obl.wz_rescaled_tube_estimate

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_affine_robust_cluster_estimate

noncomputable section

/-- A tube lies in its two-fold dilate. -/
theorem tube_subset_dilate {ρ : ℝ} (hρ : 0 ≤ ρ) (y w : Space) :
    Tube ρ y w ⊆ Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w) := by
  have hseg : segment ℝ y (y + w) ⊆
      segment ℝ (y - (1 / 2 : ℝ) • w) (y - (1 / 2 : ℝ) • w + 2 • w) := by
    intro p hp
    rw [segment_eq_image'] at hp ⊢
    obtain ⟨s, hs, rfl⟩ := hp
    refine ⟨s / 2 + 1 / 4, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    simp only [add_sub_cancel_left]
    rw [two_smul]
    module
  exact (thickening_mono (by linarith) _).trans (thickening_subset_of_subset _ hseg)

/-- A tube of positive radius is never essentially distinct from itself. -/
theorem tube_self_conflict {δ : ℝ} (hδ : 0 < δ) (x v : Space) (hv : ‖v‖ = 1) :
    ¬ volume (Tube δ x v ∩ Tube δ x v) ≤ (1 / 2 : ENNReal) * volume (Tube δ x v) := by
  rw [inter_self]
  have hpos : volume (Tube δ x v) ≠ 0 :=
    ((ENNReal.ofReal_pos.mpr (sq_pos_of_pos hδ)).trans_le
      (wz_direction_density_transfer.tube_volume_lower hδ x v hv)).ne'
  have htop := tube_volume_ne_top δ x v
  have h := ENNReal.half_lt_self hpos htop
  rw [ENNReal.div_eq_inv_mul, ← one_div] at h
  exact not_le.mpr h

/-- Restricting to an injectively indexed subfamily preserves the convex count. -/
theorem Katz.comp_injective {δ m : ℝ} {n k : ℕ} {x v : Fin n → Space} (h : Katz δ m x v)
    {ii : Fin k → Fin n} (hii : Function.Injective ii) :
    Katz δ m (fun a => x (ii a)) (fun a => v (ii a)) := by
  intro W hW
  apply le_trans _ (h W hW)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
  apply Nat.cast_le.mpr
  exact Set.ncard_le_ncard_of_injOn ii (fun a ha => ha) hii.injOn (Set.toFinite _)

/-- Restricting to an injectively indexed subfamily multiplies the Frostman constant by `n/k`. -/
theorem Frostman.comp_injective {δ l : ℝ} {n k : ℕ} {x v : Fin n → Space}
    (h : Frostman δ l x v) (hk : 0 < k) {ii : Fin k → Fin n} (hii : Function.Injective ii) :
    Frostman δ (l * n / k) (fun a => x (ii a)) (fun a => v (ii a)) := by
  intro u t r hu hr
  apply le_trans _ ((h u t r hu hr).trans_eq _)
  · apply ENNReal.ofReal_le_ofReal
    apply Nat.cast_le.mpr
    exact Set.ncard_le_ncard_of_injOn ii (fun a ha => ha) hii.injOn (Set.toFinite _)
  · congr 2
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp

/-- Sums over an enumeration of a finset. -/
theorem sum_comp_equivFin {β : Type*} [AddCommMonoid β] {n : ℕ} (S : Finset (Fin n))
    (f : Fin n → β) :
    ∑ a : Fin S.card, f ((S.equivFin.symm a : S) : Fin n) = ∑ i ∈ S, f i := by
  rw [Equiv.sum_comp S.equivFin.symm (fun s : S => f s)]
  exact Finset.sum_coe_sort S f

/-- The rescaled essentially distinct subfamily of a fibre. -/
theorem rescaled_subfamily :
    ∃ D : ℕ, 0 < D ∧ ∀ {δ ρ η m l : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
      {y w : Space}, 0 < δ → δ ≤ ρ → ρ ≤ 1 → 0 < n → ‖w‖ = 1 →
      (∀ i, ‖v i‖ = 1 ∧ Tube δ (x i) (v i) ⊆ Tube ρ y w ∧ MeasurableSet (Y i) ∧
        Y i ⊆ Tube δ (x i) (v i)) →
      (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
      Dense δ η Y → Katz δ m x v →
      ReferenceSlabCount (Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w)) l
        (fun i => Tube δ (x i) (v i)) →
      ∃ (k : ℕ) (x' v' : Fin k → Space) (Y' : Fin k → Set Space),
        (k : ℝ) ≤ n ∧ δ ^ η * n ≤ 384 * D * k ∧
        Admissible ((1 / 100) * ρ⁻¹ * δ) x' v' Y' ∧
        ENNReal.ofReal ((1 / (100 * D)) * δ ^ η * k * ((1 / 100) * ρ⁻¹ * δ) ^ 2) ≤
          ∑ a, volume (Y' a) ∧
        Katz ((1 / 100) * ρ⁻¹ * δ) (m / (1 / 100)) x' v' ∧
        Frostman ((1 / 100) * ρ⁻¹ * δ) (l / (1 / 100) ^ 3 * n / k) x' v' ∧
        volume (⋃ a, Y' a) ≤
          ENNReal.ofReal ((1 / 100) ^ 3 * (ρ⁻¹) ^ 2) * volume (⋃ i, Y i) := by
  classical
  obtain ⟨M, hM⟩ := rescaled_conflict_degree_bound
  refine ⟨M + 1, Nat.succ_pos M, ?_⟩
  intro δ ρ η m l n x v Y y w hδ hδρ hρ1 hn hw hfib hdist hdense hK hB
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hδ1 : δ ≤ 1 := hδρ.trans hρ1
  set κ : ℝ := 1 / 100 with hκ_def
  have hκ : 0 < κ := by norm_num
  have hκ5 : κ * 5 ≤ 1 := by norm_num
  have hκ6 : κ * 6 ≤ 1 := by norm_num
  obtain ⟨e, hew⟩ := exists_rotation hw
  set F := rescaleMap e y w hκ hρ with hF_def
  set δ' := κ * ρ⁻¹ * δ with hδ'_def
  have hδ'pos : 0 < δ' := by positivity
  have hδ'le : δ' ≤ 1 / 100 := by
    have h1 : ρ⁻¹ * δ ≤ 1 := by
      rw [inv_mul_le_iff₀ hρ, mul_one]; exact hδρ
    calc δ' = κ * (ρ⁻¹ * δ) := by rw [hδ'_def]; ring
      _ ≤ κ * 1 := by gcongr
      _ = 1 / 100 := by norm_num [hκ_def]
  set J : ℝ := κ ^ 3 * (ρ⁻¹) ^ 2 with hJ_def
  have hJ : 0 < J := by positivity
  have hvolF : ∀ W : Set Space, volume (F '' W) = ENNReal.ofReal J * volume W :=
    rescaleMap_volume e y w hκ hρ
  have hv : ∀ i, ‖v i‖ = 1 := fun i => (hfib i).1
  have hsub : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ y w := fun i => (hfib i).2.1
  have hvw : ∀ i, pd (v i) w < 4 * ρ := fun i => pd_lt_of_tube_subset hδ (hv i) hw (hsub i)
  let xr : Fin n → Space := fun i => rescaledBase e y w hκ hρ (x i) (v i)
  let vr : Fin n → Space := fun i => rescaledDir e ρ (v i)
  have hcover : ∀ i, F '' Tube δ (x i) (v i) ⊆ Tube δ' (xr i) (vr i) :=
    fun i => rescale_image_tube_subset e hew hκ hκ5 hρ hρ1 (hv i) (hvw i)
  have hball : ∀ i, Tube δ' (xr i) (vr i) ⊆ Metric.ball 0 1 :=
    fun i => rescaled_tube_subset_ball e hew hκ hκ6 hρ hρ1 hδ hδ'le (hv i) (hsub i)
  have hvr : ∀ i, ‖vr i‖ = 1 := fun i => norm_rescaledDir e hρ hρ1 (hv i)
  -- extraction of an essentially distinct rescaled subfamily
  let R : Fin n → Fin n → Prop := RescaledConflict e y w hκ hρ δ x v
  have hrefl : ∀ i, R i i := fun i => Or.inl (tube_self_conflict hδ'pos _ _ (hvr i))
  have hsymm : ∀ {i j}, R i j → R j i := fun h => h.symm
  have hdeg : ∀ i, (Finset.univ.filter (R i)).card ≤ M + 1 := fun i =>
    (hM e hew hw hκ hρ hκ5 hρ1 hδ x v hv hsub hdist i _
      (fun j hj => (Finset.mem_filter.mp hj).2)).trans (Nat.le_succ M)
  obtain ⟨S, -, hsep, hmass⟩ := weighted_separated_subfamily R hrefl hsymm (M + 1) hdeg
    (fun i => volume (Y i)) Finset.univ
  set D : ℕ := M + 1 with hD_def
  set k := S.card with hk_def
  let φ : Fin k ≃ S := S.equivFin.symm
  let ii : Fin k → Fin n := fun a => (φ a : Fin n)
  have hii_mem : ∀ a, ii a ∈ S := fun a => (φ a).2
  have hii_inj : Function.Injective ii := fun a b h => φ.injective (Subtype.ext h)
  -- mass and count
  have hYle : ∀ i, volume (Y i) ≤ ENNReal.ofReal (384 * δ ^ 2) := fun i =>
    (measure_mono (hfib i).2.2.2).trans (tube_volume_upper hδ hδ1 (x i) (v i) (hv i))
  have hSmass : ∑ i ∈ S, volume (Y i) ≤ ENNReal.ofReal (k * (384 * δ ^ 2)) := by
    calc
      ∑ i ∈ S, volume (Y i) ≤ ∑ _i ∈ S, ENNReal.ofReal (384 * δ ^ 2) :=
        Finset.sum_le_sum fun i _ => hYle i
      _ = ENNReal.ofReal (k * (384 * δ ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
  have hdense' : ENNReal.ofReal (δ ^ η * n * δ ^ 2) ≤
      (D : ENNReal) * ∑ i ∈ S, volume (Y i) := hdense.trans hmass
  have hcount : δ ^ η * n ≤ 384 * D * k := by
    have h1 : ENNReal.ofReal (δ ^ η * n * δ ^ 2) ≤ ENNReal.ofReal (D * (k * (384 * δ ^ 2))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      exact hdense'.trans (mul_le_mul_right hSmass _)
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    have hδ2 : 0 < δ ^ 2 := by positivity
    nlinarith
  have hkpos : 0 < k := by
    have h1 : 0 < δ ^ η * n := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have h2 : (0 : ℝ) < 384 * D * k := h1.trans_le hcount
    have h3 : (0 : ℝ) < k := by
      by_contra hk0
      push Not at hk0
      have : (384 * D * k : ℝ) ≤ 0 := by
        have : (0 : ℝ) ≤ 384 * D := by positivity
        nlinarith
      linarith
    exact_mod_cast h3
  have hkn : (k : ℝ) ≤ n := by
    have : k ≤ n := by
      calc k = S.card := rfl
        _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ S
        _ = n := Finset.card_fin n
    exact_mod_cast this
  refine ⟨k, fun a => xr (ii a), fun a => vr (ii a), fun a => F '' Y (ii a), hkn, hcount,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- admissibility
    refine ⟨hkpos, fun a => ⟨hvr (ii a), hball (ii a), ?_, ?_⟩, ?_⟩
    · exact F.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hfib (ii a)).2.2.1
    · exact (image_mono (hfib (ii a)).2.2.2).trans (hcover (ii a))
    · intro a b hab
      have hnr := hsep (ii a) (hii_mem a) (ii b) (hii_mem b) (hii_inj.ne hab)
      by_contra hbad
      exact hnr (Or.inl hbad)
  · -- density
    have hsum : ∑ a, volume (F '' Y (ii a)) = ENNReal.ofReal J * ∑ i ∈ S, volume (Y i) := by
      rw [sum_comp_equivFin S (fun i => volume (F '' Y i)), Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hvolF (Y i)
    rw [hsum]
    have hD0 : (D : ENNReal) ≠ 0 := by exact_mod_cast (Nat.succ_pos M).ne'
    have hDtop : (D : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top D
    apply (ENNReal.mul_le_mul_iff_right hD0 hDtop).mp
    calc
      (D : ENNReal) * ENNReal.ofReal ((1 / (100 * D)) * δ ^ η * k * δ' ^ 2) =
          ENNReal.ofReal J * ENNReal.ofReal (δ ^ η * k * δ ^ 2) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul hJ.le]
        congr 1
        rw [hδ'_def, hJ_def, hκ_def]
        have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_pos M).ne'
        field_simp
      _ ≤ ENNReal.ofReal J * ENNReal.ofReal (δ ^ η * n * δ ^ 2) := by
        gcongr
      _ ≤ ENNReal.ofReal J * ((D : ENNReal) * ∑ i ∈ S, volume (Y i)) :=
        mul_le_mul_right hdense' _
      _ = (D : ENNReal) * (ENNReal.ofReal J * ∑ i ∈ S, volume (Y i)) := by ring
  · -- convex count
    have htr := convex_count_transport F hκ hvolF x v xr vr hcover hK
    exact Katz.comp_injective (fun W hW => htr W hW) hii_inj
  · -- Frostman slab count
    set Dl : Set Space := Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w) with hDl
    have hTD : ∀ i, Tube δ (x i) (v i) ⊆ Dl := fun i =>
      (hsub i).trans (tube_subset_dilate hρ.le y w)
    have hcount' := reference_slab_count_transport F hJ hvolF rfl hTD hcover hB
    have hDball : F '' Dl ⊆ Metric.ball 0 1 := by
      rintro _ ⟨p, hp, rfl⟩
      rw [mem_ball_zero_iff]
      have := rescaleMap_dilate_norm_lt e hew hκ hρ hρ1 hp
      linarith
    have hDvol : ENNReal.ofReal (κ ^ 3) ≤ volume (F '' Dl) := by
      rw [hvolF]
      calc
        ENNReal.ofReal (κ ^ 3) = ENNReal.ofReal J * ENNReal.ofReal (ρ ^ 2) := by
          rw [← ENNReal.ofReal_mul hJ.le, hJ_def]
          congr 1
          field_simp
        _ ≤ ENNReal.ofReal J * volume Dl := by
          gcongr
          exact (wz_direction_density_transfer.tube_volume_lower hρ y w hw).trans
            (measure_mono (tube_subset_dilate hρ.le y w))
    have hfr := frostman_of_transported_reference (by positivity) hDball hDvol hcount'
    exact Frostman.comp_injective hfr hkpos hii_inj
  · -- union volume
    calc
      volume (⋃ a, F '' Y (ii a)) ≤ volume (F '' ⋃ i, Y i) := by
        apply measure_mono
        rw [image_iUnion]
        exact iUnion_subset fun a => subset_iUnion (fun i => F '' Y i) (ii a)
      _ = ENNReal.ofReal J * volume (⋃ i, Y i) := hvolF _

end

end WangZahlLot.Obl.wz_rescaled_tube_estimate
