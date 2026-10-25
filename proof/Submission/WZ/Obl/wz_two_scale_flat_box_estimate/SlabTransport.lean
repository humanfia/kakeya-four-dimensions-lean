-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.SlabTransport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Interfaces
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.AffineSlabs

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (SlabBound slab count_subfamily)

/-- Local slab counting survives taking a subfamily and enlarging its members.
The containing body may also be enlarged without changing its volume. -/
lemma local_slab_enlargement {n m : ℕ} {T : Fin n → Set Space} {V : Fin m → Set Space}
    {D D' : Set Space} {L F : ℝ} {P : Fin n → Prop} {Q : Fin m → Prop}
    (hL : 0 ≤ L) (h : SlabBound D L P T)
    (j : Fin m → Fin n) (hj : Function.Injective j)
    (hQP : ∀ i, Q i → P (j i)) (hTV : ∀ i, T (j i) ⊆ V i)
    (hTD : ∀ i, P i → T i ⊆ D) (hDD : D ⊆ D') (hvol : volume D' = volume D)
    (hF : (Set.ncard {i | P i} : ℝ) ≤ F) :
    ∀ u s r, ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i | Q i ∧ V i ⊆ slab u s r} : ℝ) * volume D' ≤
        ENNReal.ofReal (L * F) * volume (D' ∩ slab u s r) := by
  intro u s r hu hr
  have hc : Set.ncard {i | Q i ∧ V i ⊆ slab u s r} ≤
      Set.ncard {i | P i ∧ T i ⊆ D ∩ slab u s r} := by
    refine (Set.ncard_mono (b := {i | P (j i) ∧ T (j i) ⊆ D ∩ slab u s r}) ?_).trans
      (count_subfamily j hj (fun i => P i ∧ T i ⊆ D ∩ slab u s r))
    intro i hi
    exact ⟨hQP i hi.1, fun p hp => ⟨hTD (j i) (hQP i hi.1) hp, hi.2 (hTV i hp)⟩⟩
  rw [hvol]
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hc)) le_rfl).trans
    ((h u s r hu hr).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hF hL))
        (measure_mono (inter_subset_inter_left _ hDD))))

/-- The form of the preceding lemma used for affine images of closed tubes. -/
lemma affine_local_slab_enlargement {n m : ℕ} {T : Fin n → Set Space}
    {V : Fin m → Set Space} {D D' : Set Space} {L F J : ℝ}
    {P : Fin n → Prop} {Q : Fin m → Prop}
    (hL : 0 ≤ L) (h : SlabBound D L P T)
    (j : Fin m → Fin n) (hj : Function.Injective j)
    (hQP : ∀ i, Q i → P (j i)) (hTV : ∀ i, T (j i) ⊆ V i)
    (hTD : ∀ i, P i → T i ⊆ D) (hDD : D ⊆ D') (hvol : volume D' = volume D)
    (hF : (Set.ncard {i | P i} : ℝ) ≤ F)
    (f : Space ≃ᵃ[ℝ] Space)
    (hJ : ∀ W, volume (f '' W) = ENNReal.ofReal J * volume W) :
    ∀ u s r, ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i | Q i ∧ f '' V i ⊆ slab u s r} : ℝ) * volume (f '' D') ≤
        ENNReal.ofReal (L * F) * volume (f '' D' ∩ slab u s r) := by
  have hh := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.slabBound_affine_image f J hJ h
  exact local_slab_enlargement hL hh j hj hQP (fun i => image_mono (hTV i))
    (fun i hi => image_mono (hTD i hi)) (image_mono hDD) (by rw [hJ, hJ, hvol]) hF

/-- A version with a fixed coefficient, convenient when the original fiber and
the retained fiber have different cardinalities. -/
lemma fixed_slab_affine_enlargement {n m : ℕ} {T : Fin n → Set Space}
    {V : Fin m → Set Space} {D D' : Set Space} {C J : ℝ}
    {P : Fin n → Prop} {Q : Fin m → Prop}
    (h : ∀ u s r, ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i | P i ∧ T i ⊆ slab u s r} : ℝ) * volume D ≤
        ENNReal.ofReal C * volume (D ∩ slab u s r))
    (j : Fin m → Fin n) (hj : Function.Injective j)
    (hQP : ∀ i, Q i → P (j i)) (hTV : ∀ i, T (j i) ⊆ V i)
    (hDD : D ⊆ D') (hvol : volume D' = volume D)
    (f : Space ≃ᵃ[ℝ] Space)
    (hJ : ∀ W, volume (f '' W) = ENNReal.ofReal J * volume W) :
    ∀ u s r, ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i | Q i ∧ f '' V i ⊆ slab u s r} : ℝ) * volume (f '' D') ≤
        ENNReal.ofReal C * volume (f '' D' ∩ slab u s r) := by
  intro u s r hu hr
  obtain ⟨u', s', r', hu', hr', heq⟩ :=
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.affine_preimage_slab f hu s hr
  have hc : Set.ncard {i | Q i ∧ f '' V i ⊆ slab u s r} ≤
      Set.ncard {i | P i ∧ T i ⊆ slab u' s' r'} := by
    refine (Set.ncard_mono (b := {i | P (j i) ∧ T (j i) ⊆ slab u' s' r'}) ?_).trans
      (count_subfamily j hj (fun i => P i ∧ T i ⊆ slab u' s' r'))
    intro i hi
    refine ⟨hQP i hi.1, ?_⟩
    rw [← heq]
    intro p hp
    exact hi.2 ⟨p, hTV i hp, rfl⟩
  have hh := (mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hc)) le_rfl).trans
    (h u' s' r' hu' hr')
  have hinter : volume (f '' D' ∩ slab u s r) =
      ENNReal.ofReal J * volume (D' ∩ slab u' s' r') := by
    rw [← WangZahlLot.Obl.wz_rescaled_fibre_alternatives.image_inter_preimage, hJ, heq]
  rw [hJ, hvol, hinter]
  calc
    _ = ENNReal.ofReal J *
        (ENNReal.ofReal (Set.ncard {i | Q i ∧ f '' V i ⊆ slab u s r} : ℝ) * volume D) := by ring
    _ ≤ ENNReal.ofReal J * (ENNReal.ofReal C * volume (D ∩ slab u' s' r')) :=
      mul_le_mul' le_rfl hh
    _ ≤ ENNReal.ofReal J * (ENNReal.ofReal C * volume (D' ∩ slab u' s' r')) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (measure_mono (inter_subset_inter_left _ hDD)))
    _ = _ := by ring

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
