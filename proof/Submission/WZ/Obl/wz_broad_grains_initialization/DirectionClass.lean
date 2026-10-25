-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.DirectionClass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.DominantClass
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CordobaSlab

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (bodyCount)
open scoped Classical

/-- A unit vector can be made the third coordinate axis. -/
lemma frame_last_of_unit {w : Space} (hw : ‖w‖ = 1) :
    ∃ e : Space ≃ₗᵢ[ℝ] Space, e w = EuclideanSpace.single 2 (1 : ℝ) := by
  obtain ⟨b, hb⟩ := wz_clustered_cover_volume_gain.Parent.Factor.exists_frame_first hw
  let b' := b.reindex (Fin.revPerm : Equiv.Perm (Fin 3))
  have hb' : b' 2 = w := by simpa [b', OrthonormalBasis.reindex_apply, Fin.revPerm] using hb
  refine ⟨b'.repr, ?_⟩
  rw [← hb', OrthonormalBasis.repr_self]

/-- One direction class provides a common frame for every occupied tube,
while retaining pointwise broadness up to an absolute constant. -/
theorem aligned_shading_class {n : ℕ} (hn : 0 < n) (v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1) (Y : Fin n → Set Space) (hY : ∀ i, MeasurableSet (Y i)) :
    ∃ (e : Space ≃ₗᵢ[ℝ] Space) (Z : Fin n → Set Space),
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ ((Z i).Nonempty →
        1 / 2 ≤ e (v i) 2 ∧ ∀ j : Fin 3, j ≠ 2 → |e (v i) j| ≤ 1 / 100)) ∧
      (∑ i, volume (Y i)) ≤ ENNReal.ofReal ((2002 : ℝ) ^ 6) * ∑ i, volume (Z i) ∧
      ∀ p ∈ ⋃ i, Z i, bodyCount Y p ≤ (2002 : ℝ) ^ 3 * bodyCount Z p := by
  classical
  let θ : ℝ := 1 / 1000
  have hθ : 0 < θ := by norm_num [θ]
  let G := Finset.univ.image (fun i => wz_balanced_cluster_cover.cell θ (v i))
  have hGne : G.Nonempty := ⟨_, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  let κ := {g // g ∈ G}
  letI : Fintype κ := inferInstance
  letI : Nonempty κ := ⟨⟨hGne.choose, hGne.choose_spec⟩⟩
  let E := Fintype.equivFin κ
  let f : Fin n → Fin (Fintype.card κ) := fun i => E
    ⟨wz_balanced_cluster_cover.cell θ (v i), Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨k, Z, hZ, hmass, hcount⟩ := dominant_shading_class (Fintype.card_pos) f Y hY
  let ℓ := (E.symm k).val
  obtain ⟨i₀, _, hi₀⟩ := Finset.mem_image.mp (E.symm k).property
  have hcode (i : Fin n) (hi : (Z i).Nonempty) :
      wz_balanced_cluster_cover.cell θ (v i) = wz_balanced_cluster_cover.cell θ (v i₀) := by
    have hh := congrArg (fun j => (E.symm j).val) ((hZ i).2.2 hi)
    have he : wz_balanced_cluster_cover.cell θ (v i) = (E.symm k).val := by
      simpa only [f, Equiv.symm_apply_apply] using hh
    exact he.trans hi₀.symm
  obtain ⟨e, he⟩ := frame_last_of_unit (hv i₀)
  have hbound : (Fintype.card κ : ℝ) ≤ (2002 : ℝ) ^ 3 := by
    have hsub : G ⊆ wz_balanced_cluster_cover.box θ 0 1 := by
      intro g hg
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
      exact wz_balanced_cluster_cover.cell_mem_box hθ (by simpa [hv i])
    have hcard := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
    have hbox := wz_balanced_cluster_cover.card_box_le hθ (0 : Space) (by norm_num : (0 : ℝ) ≤ 1)
    have hκ : Fintype.card κ = G.card := Fintype.card_coe _
    rw [hκ]
    exact hcard.trans (by norm_num [θ] at hbox ⊢; exact hbox)
  refine ⟨e, Z, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hZ i).1, (hZ i).2.1, ?_⟩
    intro hi
    have hd : ‖v i - v i₀‖ ≤ 2 * θ := wz_balanced_cluster_cover.norm_sub_le_of_cell_eq hθ (hcode i hi)
    have hcoord (j : Fin 3) : |e (v i) j - e (v i₀) j| ≤ 2 * θ := by
      have hh := wz_balanced_cluster_cover.abs_apply_le_norm (e (v i - v i₀)) j
      rw [e.norm_map] at hh
      simpa only [map_sub, PiLp.sub_apply] using hh.trans hd
    have hl := hcoord 2
    rw [he] at hl
    norm_num [EuclideanSpace.single, θ] at hl
    refine ⟨by linarith [abs_le.mp hl], ?_⟩
    intro j hj
    have hh := hcoord j
    rw [he] at hh
    have hz : (EuclideanSpace.single 2 (1 : ℝ) : Space) j = 0 := by simp [EuclideanSpace.single, hj]
    rw [hz, sub_zero] at hh
    norm_num [θ] at hh
    linarith
  · apply hmass.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hh := sq_le_sq' (by nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card κ)] : -(2002 : ℝ) ^ 3 ≤ (Fintype.card κ : ℝ)) hbound
    nlinarith only [hh]
  · intro p hp
    exact (hcount p hp).trans (mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _))

end WangZahlLot.Obl.wz_broad_grains_initialization
