-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.MappedPrismAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CellPrismAssembly
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.MappedCellAssembly

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

set_option maxHeartbeats 1000000 in
/-- Assemble physical prism packets whose cells and carriers are separated
in a common transformed coordinate system. -/
theorem assemble_local_prism_packets_mapped {δ r s ρ c ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 < s) (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (hε : 0 ≤ ε) {n N : ℕ}
    (x v : Fin n → V) (Y : Fin n → Set V) (C : Fin N → Set V)
    (q : Fin N → V) (y w : V) (φ : V → V)
    (hY : ∀ i, MeasurableSet (Y i)) (hC : ∀ j, MeasurableSet (C j))
    (hball : ∀ j, C j ⊆ φ ⁻¹' ball (φ (q j)) s)
    (hdisj : Pairwise fun j k => Disjoint (C j) (C k))
    (hcover : (⋃ i, Y i) ⊆ ⋃ j, C j)
    (hsep : ∀ i j k, j ≠ k → (Y i ∩ C j).Nonempty → (Y i ∩ C k).Nonempty →
      10 * s < dist (φ (q j)) (φ (q k)))
    (hlog : (Nat.log 2 n + 1 : ℝ) ≤ δ ^ (-ε))
    (R : ∀ j, LocalPrismPacket δ r ρ c ε x v (fun i => Y i ∩ C j) (q j) y w)
    (hlocal : ∀ j z, z ∈ (R j).centers →
      P (16 * δ) (128 * ρ * c) c z (R j).frame ⊆ φ ⁻¹' ball (φ (q j)) (3 * s)) :
    Nonempty (CellPrismFamily δ r ρ c (2 * ε) x v Y C q y w) := by
  let W : Fin N → Fin n → Set V := fun j => (R j).shading
  let F : Fin N → Finset V := fun j => (R j).centers
  let H : Fin N → V → Set V := fun j => (R j).pieces
  let P' : Fin N → V → Set V := fun j z =>
    P (16 * δ) (128 * ρ * c) c z (R j).frame
  let Q : Fin n → Fin N → V → Prop := fun i j z =>
    (∀ p ∈ T δ (x i) (v i) ∩ frontier (P' j z), |(R j).frame (p - z) 2| = c / 2) ∧
      ∀ s ∈ ({-c / 2, c / 2} : Set ℝ),
        ∃ p ∈ T δ (x i) (v i) ∩ P' j z, (R j).frame (p - z) 2 = s
  let b : ENNReal := o (δ ^ ε * ((16 * δ) * (128 * ρ * c) * c))
  have hHsub (j : Fin N) (z : V) (hz : z ∈ F j) : H j z ⊆ C j := by
    intro p hp
    have hp' : p ∈ ⋃ i, W j i := (R j).union_eq ▸
      mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, hp⟩⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp'
    exact ((R j).refines i).2 hi |>.2
  have hkeep : o (δ ^ ε) * (∑ i, μ (Y i)) ≤ ∑ j, ∑ i, μ (W j i) := by
    rw [← shading_mass_partition μ Y C hY hC hdisj hcover, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (R j).retains
  have hdense (j : Fin N) : b * (F j).card ≤ ∑ z ∈ F j, μ (H j z) := by
    have he : b * (F j).card = o (δ ^ ε * (F j).card * ((16 * δ) * (128 * ρ * c) * c)) := by
      change ENNReal.ofReal _ * _ = ENNReal.ofReal _
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [he]
    exact (R j).density
  obtain ⟨m, L, cell, z, Z, _, hz, hZ, hHdisj, hunion, hmass, hdensity, hcross, hlevel⟩ :=
    assemble_uniform_cell_pieces_mapped μ φ hs Y C q F W H P' Q (fun j => (R j).level)
      hdisj (fun j i => (R j).refines i)
      (fun j i => ((R j).refines i).2.trans (inter_subset_right.trans (hball j)))
      (fun i j k hjk hj hk => hsep i j k hjk
        (hj.mono ((R j).refines i).2) (hk.mono ((R k).refines i).2))
      (fun j z hz z' hz' hzz => ((R j).disjoint hz hz' hzz).mono
        ((R j).piece_data z hz).2.1 ((R j).piece_data z' hz').2.1)
      (fun j => (R j).union_eq)
      (fun j z hz => hlocal j z hz)
      (fun j z hz i hi => (R j).crossing i z hz hi)
      (fun j p hp => (R j).uniform p hp) hkeep hdense
  have hlog' : ((Nat.log 2 n + 1 : ℕ) : ENNReal) ≤ o (δ ^ (-ε)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hlog)
  have hcancel : o (δ ^ ε) * o (δ ^ (-ε)) = 1 := by
    change ENNReal.ofReal (δ ^ ε) * ENNReal.ofReal (δ ^ (-ε)) = 1
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
    simp [o]
  have hpower : o (δ ^ (2 * ε)) = o (δ ^ ε) * o (δ ^ ε) := by
    change ENNReal.ofReal (δ ^ (2 * ε)) = ENNReal.ofReal (δ ^ ε) * ENNReal.ofReal (δ ^ ε)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
    congr 2
    ring
  refine ⟨{
    level := m
    count := L
    cell := cell
    centers := z
    frames := fun l => (R (cell l)).frame
    shading := Z
    pieces := fun l => H (cell l) (z l)
    aligned := fun l => (R (cell l)).aligned
    refines := hZ
    disjoint := hHdisj
    piece_data := fun l => (R (cell l)).piece_data (z l) (hz l)
    localized := fun l => hHsub _ _ (hz l)
    union_eq := hunion
    retains := ?_
    density := ?_
    crossing := hcross
    uniform := hlevel
  }⟩
  · calc
      _ = o (δ ^ ε) * (o (δ ^ ε) * ∑ i, μ (Y i)) := by rw [hpower, mul_assoc]
      _ ≤ o (δ ^ ε) * (((Nat.log 2 n + 1 : ℕ) : ENNReal) * ∑ i, μ (Z i)) :=
        mul_le_mul_right hmass _
      _ ≤ o (δ ^ ε) * (o (δ ^ (-ε)) * ∑ i, μ (Z i)) :=
        mul_le_mul_right (mul_le_mul_left hlog' _) _
      _ = _ := by rw [← mul_assoc, hcancel, one_mul]
  · have hpow : δ ^ (2 * ε) ≤ δ ^ ε :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    calc
      _ ≤ o (δ ^ ε * L * ((16 * δ) * (128 * ρ * c) * c)) :=
        ENNReal.ofReal_le_ofReal (by gcongr)
      _ = b * L := by
        change ENNReal.ofReal _ = ENNReal.ofReal _ * _
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ _ := hdensity

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
