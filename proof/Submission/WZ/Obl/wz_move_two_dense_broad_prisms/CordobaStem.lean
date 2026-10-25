-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.CordobaStem.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.TransverseSelection
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.PerTube

/-! The short-stem Córdoba estimate used in a dense broad prism. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- Local pieces of uniformly positive mass, crossing a shaded stem at angle
at least `r`, have a quantitatively large union. No planarity premise is needed. -/
theorem cordoba_stem_mass_bound {d r L mass : ℝ} {n : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hd1 : d ≤ 1/100) (hr : 0 < r) (hr1 : r ≤ 1)
    (hL : 2*d ≤ L) (hmass : 0 ≤ mass)
    {x u : V} (hu : ‖u‖ = 1) (E : Set V) (hEm : MeasurableSet E)
    (hET : E ⊆ T d x u)
    (y v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (Y : Fin n → Set V) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ T d (y i) (v i))
    (hYmass : ∀ i, (Y i).Nonempty → O mass ≤ volume (Y i))
    (hlocal : ∀ i p, p ∈ E → p ∈ Y i → Y i ⊆ ball p L)
    (hpartner : ∀ p ∈ E, ∃ i, p ∈ Y i ∧ r < min ‖v i-u‖ ‖v i+u‖)
    (hUfin : volume (⋃ i, Y i) ≠ ∞) :
    mass^2 * volume.real E * r ≤
      1000000000 * L * d^5 * (1+Real.log (1/d)) * volume.real (⋃ i, Y i) := by
  classical
  have hEfin : volume E ≠ ∞ := measure_ne_top_of_subset hET
    (wz_flat_cluster_slab_filling.tube_volume_ne_top d x u)
  obtain ⟨g, E', hg, hE'm, hE'E, hhalf, hcross⟩ :=
    select_transverse_coordinate hu hr.le v hv Y hYm E hEm hEfin hpartner
  have hE'T : E' ⊆ T d x u := hE'E.trans hET
  have hE'fin : volume E' ≠ ∞ := measure_ne_top_of_subset hE'E hEfin
  let D : ℝ := 32*d/(r/2)
  have hD : 0 < D := by dsimp [D]; positivity
  let M : ℕ := ⌈(1+2*d)/D⌉₊
  obtain ⟨hM, hlog⟩ := wz_flat_cluster_slab_filling.pt_log_cells hd hd1
    (show 0 < r/2 by positivity) (show r/2 ≤ 1 by linarith) (show D = 32*d/(r/2) from rfl)
  let F : Finset (Fin M) := Finset.univ.filter
    (fun m => (E' ∩ wz_flat_cluster_slab_filling.cell d D x u m).Nonempty)
  have hcells := wz_flat_cluster_slab_filling.many_cells hd hu hD E' hE'm hE'T
    (a := volume.real E') (by exact le_of_eq (ENNReal.ofReal_toReal hE'fin)) M hM
  change volume.real E' ≤ 128*(2*(D+2*d)+d)*d^2*(F.card : ℝ) at hcells
  have hex : ∀ m ∈ F, ∃ p, p ∈ E' ∧ p ∈ wz_flat_cluster_slab_filling.cell d D x u m := by
    intro m hm
    exact (Finset.mem_filter.mp hm).2
  choose! pt hptE hptcell using hex
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  choose! jf hjY hjr using hcross
  have hcor := wz_flat_cluster_slab_filling.cordoba_box hd (by linarith : d ≤ 1)
    (show 0 < r/2 by positivity) (show r/2 ≤ 1 by linarith) hL
    (show D = 32*d/(r/2) from rfl) hmass hu hg F pt
    (fun m => y (jf (pt m))) (fun m => v (jf (pt m))) (fun m => Y (jf (pt m)))
    (fun m => hv _) (fun m hm => hE'T (hptE m hm)) hptcell
    (fun m hm => hYT _ (hjY _ (hptE m hm)))
    (fun m hm => by simpa only [div_div, show (2:ℝ)*2=4 by norm_num] using hjr _ (hptE m hm))
    (fun m _ => hYm _) (fun m hm => by
      intro q hq
      exact ⟨hYT _ hq, hlocal _ _ (hE'E (hptE m hm)) (hjY _ (hptE m hm)) hq⟩)
    (fun m hm => hYmass _ ⟨pt m, hjY _ (hptE m hm)⟩)
    (⋃ i, Y i) (MeasurableSet.iUnion hYm) hUfin
    (fun m _ => subset_iUnion Y (jf (pt m)))
  have hL0 : 0 ≤ L := by linarith
  have hlog0 : 0 ≤ 1+Real.log (1/d) := by
    have hh : (1 : ℝ) ≤ 1/d := (le_div_iff₀ hd).mpr (by linarith)
    linarith [Real.log_nonneg hh]
  have hcor' : mass^2*(F.card : ℝ) ≤
      20000*L*d^2*(1+Real.log (1/d))*volume.real (⋃ i, Y i) := by
    refine hcor.trans ?_
    change 20000*L*d^2*(1+Real.log (M : ℝ))*volume.real (⋃ i, Y i) ≤ _
    gcongr
  have hDr : r*(2*(D+2*d)+d) ≤ 133*d := by
    have he : r*(2*(D+2*d)+d) = 128*d+5*d*r := by dsimp [D]; field_simp <;> ring
    rw [he]
    nlinarith
  have hcellr : volume.real E' * r ≤ 17024*d^3*(F.card : ℝ) := by
    calc
      _ ≤ (128*(2*(D+2*d)+d)*d^2*(F.card : ℝ))*r :=
        mul_le_mul_of_nonneg_right hcells hr.le
      _ = 128*(r*(2*(D+2*d)+d))*d^2*(F.card : ℝ) := by ring
      _ ≤ 128*(133*d)*d^2*(F.card : ℝ) := by gcongr
      _ = _ := by ring
  have hEr : volume.real E*r ≤ 34048*d^3*(F.card : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hhalf hr.le
    nlinarith
  calc
    mass^2 * volume.real E * r = mass^2*(volume.real E*r) := by ring
    _ ≤ mass^2*(34048*d^3*(F.card : ℝ)) := mul_le_mul_of_nonneg_left hEr (sq_nonneg mass)
    _ = 34048*d^3*(mass^2*(F.card : ℝ)) := by ring
    _ ≤ 34048*d^3*(20000*L*d^2*(1+Real.log (1/d))*volume.real (⋃ i, Y i)) := by gcongr
    _ = 680960000*L*d^5*(1+Real.log (1/d))*volume.real (⋃ i, Y i) := by ring
    _ ≤ _ := by gcongr <;> norm_num

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
