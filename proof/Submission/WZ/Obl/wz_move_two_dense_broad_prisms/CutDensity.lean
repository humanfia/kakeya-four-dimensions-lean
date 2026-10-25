-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.CutDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PacketCore
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.CordobaStem

/-! Córdoba density inside a common spatial cut of a broad packet. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set Metric
open scoped ENNReal
open wz_measurable_angular_selection (pd)

/-- Only the tubes meeting the stem are used by Córdoba. All packet pieces
remain in the common cut, preserving their angular broadness there. -/
theorem broad_packet_cut_mass {n : ℕ} {d r L mass B : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hd1 : d ≤ 1/100)
    (hr : 0 < r) (hr1 : r ≤ 1) (hL : 2*d ≤ L) (hmass : 0 ≤ mass)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (Y : Fin n → Set V) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (z : V) (hball : ∀ i, Y i ⊆ ball z (L/2))
    (hYmass : ∀ i, (Y i).Nonempty → O mass ≤ volume (Y i))
    (i₀ : Fin n) (hi₀ : (Y i₀).Nonempty)
    (hB : B < 1)
    (hBr : ∀ p ∈ Y i₀,
      q n {i | p ∈ Y i ∧ pd (v i) (v i₀) ≤ r} ≤ B*q n {i | p ∈ Y i})
    (Q : Set V) (hQm : MeasurableSet Q)
    (hQ : ∀ i, (Y i₀ ∩ Y i).Nonempty → Y i ⊆ Q) :
    mass^3*r ≤ 1000000000*L*d^5*(1+Real.log (1/d))*
      volume.real (⋃ i, Y i ∩ Q) := by
  classical
  let W : Fin n → Set V := fun i => if (Y i₀ ∩ Y i).Nonempty then Y i else ∅
  have hWm (i : Fin n) : MeasurableSet (W i) := by
    dsimp [W]
    split_ifs <;> simp_all
  have hWY (i : Fin n) : W i ⊆ Y i := by
    dsimp [W]
    split_ifs <;> simp
  have hWQ (i : Fin n) : W i ⊆ Y i ∩ Q := by
    dsimp [W]
    split_ifs with hi
    · exact fun p hp => ⟨hp, hQ i hi hp⟩
    · exact empty_subset _
  have hWmass (i : Fin n) (hi : (W i).Nonempty) : O mass ≤ volume (W i) := by
    have hne : (Y i₀ ∩ Y i).Nonempty := by
      by_contra hn
      simpa [W, hn] using hi
    rw [show W i = Y i by simp [W, hne]]
    exact hYmass i (hi.mono (hWY i))
  have hpartner (p : V) (hp : p ∈ Y i₀) :
      ∃ i, p ∈ W i ∧ r < min ‖v i-v i₀‖ ‖v i+v i₀‖ := by
    obtain ⟨i, hi, hri⟩ := transverse_partner_of_broad hB (hBr p hp)
      (mem_iUnion.mpr ⟨i₀, hp⟩)
    refine ⟨i, ?_, hri⟩
    simp only [W, if_pos (show (Y i₀ ∩ Y i).Nonempty from ⟨p, hp, hi⟩)]
    exact hi
  have hlocal (i : Fin n) (p : V) (hp : p ∈ Y i₀) (_hpi : p ∈ W i) :
      W i ⊆ ball p L := by
    intro q hq
    have hqz : dist q z < L/2 := hball i (hWY i hq)
    have hzp : dist z p < L/2 := by simpa [dist_comm] using hball i₀ hp
    exact (dist_triangle q z p).trans_lt (by linarith)
  have hYfin (i : Fin n) : volume (Y i) ≠ ∞ := measure_ne_top_of_subset (hYT i)
    (wz_flat_cluster_slab_filling.tube_volume_ne_top d (x i) (v i))
  have hUfin : volume (⋃ i, Y i ∩ Q) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ∑ i, volume (Y i ∩ Q) := by
        simpa only [tsum_fintype] using measure_iUnion_le (fun i => Y i ∩ Q)
      _ < ∞ := ENNReal.sum_lt_top.mpr (fun i _ => lt_top_iff_ne_top.mpr
        (measure_ne_top_of_subset inter_subset_left (hYfin i)))
  have hWfin : volume (⋃ i, W i) ≠ ∞ :=
    measure_ne_top_of_subset (iUnion_mono hWQ) hUfin
  have hcor := cordoba_stem_mass_bound hn hd hd1 hr hr1 hL hmass (hv i₀)
    (Y i₀) (hYm i₀) (hYT i₀) x v hv W hWm
    (fun i => (hWY i).trans (hYT i)) hWmass hlocal hpartner hWfin
  have hreal : mass ≤ volume.real (Y i₀) := by
    have hh := ENNReal.toReal_mono (hYfin i₀) (hYmass i₀ hi₀)
    change mass ≤ (volume (Y i₀)).toReal
    simpa only [O, ENNReal.toReal_ofReal hmass] using hh
  have hmono : volume.real (⋃ i, W i) ≤ volume.real (⋃ i, Y i ∩ Q) :=
    ENNReal.toReal_mono hUfin (measure_mono (iUnion_mono hWQ))
  have hlog : 0 ≤ 1+Real.log (1/d) := by
    have hh : (1 : ℝ) ≤ 1/d := (le_div_iff₀ hd).mpr (by linarith)
    linarith [Real.log_nonneg hh]
  calc
    mass^3*r = mass^2*mass*r := by ring
    _ ≤ mass^2*volume.real (Y i₀)*r := by gcongr
    _ ≤ 1000000000*L*d^5*(1+Real.log (1/d))*volume.real (⋃ i, W i) := hcor
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (by
      have hL0 : 0 ≤ L := by linarith
      exact mul_nonneg (by positivity) hlog)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
