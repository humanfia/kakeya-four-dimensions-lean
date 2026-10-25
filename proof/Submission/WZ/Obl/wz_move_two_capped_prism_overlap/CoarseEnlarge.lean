-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.CoarseEnlarge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.AngularScale
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_coarse_tube_grains.Geom
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PrismNeighborhood
import Submission.WZ.Obl.wz_coarse_grains_assembly.DoubleSelection

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, CoarseEnlarge.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O P T X ι)

/-- Reindex retained prism and coarse labels, and set a new coarse radius. -/
def PrismData.select {n L N : ℕ} (D : PrismData n) (s : ℝ)
    (f : Fin L → Fin D.L) (g : Fin N → Fin D.N) (γ : Fin L → Fin N) : PrismData n where
  a := D.a
  s := s
  L := L
  N := N
  z := D.z ∘ f
  e := D.e ∘ f
  W := fun i j => D.W i (f j)
  y := D.y ∘ g
  w := D.w ∘ g
  γ := γ

/-- Every prism in valid data carries an actual fine incidence. -/
theorem valid_prism_nonempty {ω ζ δ h ρ c : ℝ} {n o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (H : D.Valid ω ζ δ h ρ c x v Y o) (j : Fin D.L) :
    ∃ i, (D.W i j).Nonempty := by
  rcases H with ⟨ha, hab, hbc, _, _, _, hdense, _⟩
  have ha0 := hδ.trans_le ha
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  have hp : 0 < O (δ ^ h) * volume (P D.a (ρ * c) c (D.z j) (D.e j)) := by
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume ha0.le hb0.le hc0.le]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ h)).ne'
      (ENNReal.ofReal_pos.mpr (mul_pos (mul_pos ha0 hb0) hc0)).ne'
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero (hp.trans_le (hdense j)).ne'
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  exact ⟨i, p, hi⟩

/-- Doubling the middle width and the coarse radius preserves all geometric
conditions when the original length is at most one quarter. Retaining whole
prism labels also preserves pointwise broadness at its explicit scale cost. -/
theorem valid_double_selected {ω ζ δ h h' ρ c : ℝ} {n L N : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hβ : 0 ≤ ω * ζ / 100)
    (hρ2 : 2 * ρ ≤ 1) (hc4 : c ≤ 1 / 4)
    (hdensity : 2 * O (δ ^ h') ≤ O (δ ^ h))
    (hangular : δ ^ (-h) * (2 : ℝ) ^ (ω * ζ / 100) ≤ δ ^ (-h'))
    (H : D.Valid ω ζ δ h ρ c x v Y 1)
    (f : Fin L → Fin D.L) (hf : Function.Injective f)
    (g : Fin N → Fin D.N) (γ : Fin L → Fin N)
    (hγ : ∀ j, g (γ j) = D.γ (f j))
    (hmass : O (δ ^ h') * ∑ i, volume (Y i) ≤ ∑ i, ∑ j, volume (D.W i (f j)))
    (hX : X (2 * ρ) N (D.y ∘ g) (D.w ∘ g)) :
    (D.select (2 * ρ) f g γ).Valid ω ζ δ h' (2 * ρ) c x v Y 1 := by
  have Hcopy := H
  rcases Hcopy with ⟨ha, hab, hbc, hc, hW, _, hdense, hcross, hbroad, _, hw, hcover, _⟩
  have ha0 := hδ.trans_le ha
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  have hρ : 0 < ρ := (mul_pos_iff.mp hb0).resolve_right
    (by intro h; linarith [h.2]) |>.1
  have hs : D.s = ρ := (hcover (by norm_num)).1
  have hwide (j : Fin D.L) : P D.a (ρ * c) c (D.z j) (D.e j) ⊆
      P D.a (2 * ρ * c) c (D.z j) (D.e j) := by
    intro p hp
    exact ⟨hp.1, hp.2.1.trans (by nlinarith), hp.2.2⟩
  dsimp only [PrismData.Valid, PrismData.select, Function.comp_apply]
  refine ⟨ha, hab.trans (by nlinarith), by nlinarith, hc, ?_, hmass, ?_, ?_, ?_, hX,
    fun k => hw _, ?_, by norm_num⟩
  · intro i j
    refine ⟨(hW i (f j)).1, ?_, fun j' hne => (hW i (f j)).2.2 (f j')
      (fun he => hne (hf he))⟩
    exact fun p hp => ⟨((hW i (f j)).2.1 hp).1, hwide (f j) ((hW i (f j)).2.1 hp).2⟩
  · intro j
    have hv : volume (P D.a (2 * ρ * c) c (D.z (f j)) (D.e (f j))) =
        2 * volume (P D.a (ρ * c) c (D.z (f j)) (D.e (f j))) := by
      rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume ha0.le (by positivity) hc0.le,
        WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume ha0.le hb0.le hc0.le]
      rw [show D.a * (2 * ρ * c) * c = 2 * (D.a * (ρ * c) * c) by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    change O (δ ^ h') * volume (P D.a (2 * ρ * c) c (D.z (f j)) (D.e (f j))) ≤ _
    rw [hv, ← mul_assoc, mul_comm (O _) 2]
    exact (mul_le_mul' hdensity le_rfl).trans (hdense (f j))
  · intro i j hnon
    obtain ⟨ht, hfr, hend⟩ := hcross i (f j) hnon
    refine ⟨?_, ?_, ?_⟩
    · simp only [hγ]
      rw [hs] at ht
      exact ht.trans (thickening_mono (by linarith : ρ ≤ 2 * ρ) _)
    · have hne : (T δ (x i) (v i) ∩ P D.a (ρ * c) c (D.z (f j)) (D.e (f j))).Nonempty := by
        obtain ⟨p, hp, _⟩ := hend (c / 2) (by simp)
        exact ⟨p, hp⟩
      exact (WangZahlLot.Obl.wz_coarse_tube_grains.Geom.crossing_widen
        isOpen_thickening ((convex_segment _ _).thickening δ) hc0
        (by nlinarith : ρ * c ≤ 2 * ρ * c) hne hfr).1
    · intro t ht
      obtain ⟨p, hp, he⟩ := hend t ht
      exact ⟨p, ⟨hp.1, hwide (f j) hp.2⟩, he⟩
  · intro j p
    apply angular_bound_enlarge v {i | p ∈ D.W i (f j)} hδ hρ (by linarith) hβ
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith : -h ≤ 0))
    · simpa only [mul_div_cancel_right₀ _ hρ.ne'] using hangular
    · exact hbroad (f j) p
  · intro _
    refine ⟨rfl, ?_⟩
    intro j
    simp only [hγ]
    obtain ⟨i, hi⟩ := valid_prism_nonempty D hδ H (f j)
    obtain ⟨ht, _, hend⟩ := hcross i (f j) hi
    rw [hs] at ht
    have hend' : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ), ∃ p ∈
        T δ (x i) (v i) ∩ P D.a (2 * ρ * c) c (D.z (f j)) (D.e (f j)),
        (D.e (f j)) (p - D.z (f j)) 2 = t := by
      intro t ht
      obtain ⟨p, hp, he⟩ := hend t ht
      exact ⟨p, ⟨hp.1, hwide (f j) hp.2⟩, he⟩
    refine ⟨WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.crossing_prism_subset_expanded_coarse
      ha0.le (hab.trans (by nlinarith)) (by positivity) hc0 (by nlinarith)
      (D.e (f j)) ht hend', ?_⟩
    have hh := ((hcover (by norm_num)).2 (f j)).2
    nlinarith [sq_nonneg ρ]

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
