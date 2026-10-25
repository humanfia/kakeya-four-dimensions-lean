-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.NormalizedRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.RegularTransfer
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CellLevelSelection
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Indexing

noncomputable section
namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
open Set MeasureTheory

/-- Incidence mass normalized by a pointwise multiplicity cap is the density
condition that survives dyadic regularization. Caps may differ between prisms. -/
theorem normalized_prism_refinement {ω ζ δ h h' s ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh' : h ≤ h')
    (D : PrismData ω ζ δ h ρ c n x v Y) (M : Fin D.L → ℝ)
    (hM : ∀ j, 0 < M j)
    (hcap : ∀ j p, q n {i | p ∈ D.W i j} ≤ M j)
    (hnormal : ∀ j, O (δ ^ s * M j) * μ (P D.a (ρ * c) c (D.z j) (D.e j)) ≤
      ∑ i, μ (D.W i j))
    (havoid : ∀ i j j', j ≠ j' → D.γ j = D.γ j' → (D.W i j).Nonempty →
      Disjoint (D.W i j') (P D.a (ρ * c) c (D.z j) (D.e j)))
    (hmassbudget : ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ 2 * δ ^ h' ≤ δ ^ h)
    (hdensebudget : ((Nat.log 2 n + 1 : ℕ) : ℝ) * δ ^ h' ≤ δ ^ s) :
    ∃ (D' : PrismData ω ζ δ h' ρ c n x v Y) (m : ℝ),
      D'.a = D.a ∧ 0 < m ∧
      (∀ j p, p ∈ pieceSupport D'.W j → q n {i | p ∈ D'.W i j} ∈ Set.Icc m (2 * m)) ∧
      ∀ i j j', j ≠ j' → D'.γ j = D'.γ j' → (D'.W i j).Nonempty →
        Disjoint (D'.W i j') (P D'.a (ρ * c) c (D'.z j) (D'.e j)) := by
  classical
  have ha : 0 < D.a := hδ.trans_le D.lower
  have hrc : 0 < ρ * c := ha.trans_le D.middle
  have hc : 0 < c := hrc.trans_le D.upper
  have hρ : 0 < ρ := pos_of_mul_pos_left hrc hc.le
  let B : ℕ := Nat.log 2 n + 1
  have hB : 0 < B := Nat.succ_pos _
  have hex (j : Fin D.L) :=
    WangZahlLot.Obl.wz_coarse_tube_grains.RIS.dyadic_shading_refinement_common volume
      (fun i => D.W i j) (fun i => (D.pieces i j).1)
  choose k Z hk hZ hmass hlevel using hex
  obtain ⟨m, J, _, hJ, hselect⟩ :=
    WangZahlLot.Obl.wz_coarse_tube_grains.RIS.common_cell_multiplicity_level
      volume Z k (fun j p hp => (hlevel j p hp).1)
  let fj := WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx J
  let W' := fun i j => Z (fj j) i
  have hupper (j : Fin D.L) : (∑ i, μ (Z j i)) ≤ O (M j) * μ (⋃ i, Z j i) := by
    have hh := WangZahlLot.Obl.wz_clustered_cover_volume_gain.body_mass_le_mul_of_count
      (Y := Z j) (Z := fun _ : Fin 1 => ⋃ i, Z j i)
      (fun i => (hZ j i).1) (fun _ => MeasurableSet.iUnion (fun i => (hZ j i).1)) (hM j).le ?_
    · simpa only [Finset.univ_unique, Finset.sum_singleton] using hh
    · intro p
      by_cases hp : p ∈ ⋃ i, Z j i
      · have hone : WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount
            (fun _ : Fin 1 => ⋃ i, Z j i) p = 1 := by
          simp [WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount, hp]
        rw [hone, mul_one]
        change q n {i | p ∈ Z j i} ≤ M j
        have he : {i | p ∈ Z j i} = {i | p ∈ D.W i j} := by
          ext i
          exact (hlevel j p hp).2.2 i
        rw [he]
        exact hcap j p
      · have he : {i | p ∈ Z j i} = (∅ : Set (Fin n)) := by
          ext i
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun hi => hp (Set.mem_iUnion.mpr ⟨i, hi⟩)
        simp only [WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount, he,
          Set.ncard_empty, Nat.cast_zero, hp, Set.ofPred_false, mul_zero, le_refl]
  have hdense (j : Fin D.L) : O (δ ^ h') * μ (P D.a (ρ * c) c (D.z j) (D.e j)) ≤
      μ (⋃ i, Z j i) := by
    have hBM : 0 < (B : ℝ) * M j := mul_pos (Nat.cast_pos.mpr hB) (hM j)
    apply WangZahlLot.Obl.wz_rescaled_fibre_alternatives.cancel_volume_factor hBM
    calc
      _ = O (M j * ((B : ℝ) * δ ^ h')) * μ (P D.a (ρ * c) c (D.z j) (D.e j)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hBM.le]
        congr 2
        ring
      _ ≤ O (M j * δ ^ s) * μ (P D.a (ρ * c) c (D.z j) (D.e j)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hdensebudget (hM j).le)) le_rfl
      _ ≤ ∑ i, μ (D.W i j) := by simpa only [mul_comm (M j) (δ ^ s)] using hnormal j
      _ ≤ (B : ENNReal) * ∑ i, μ (Z j i) := by simpa only [Fintype.card_fin] using hmass j
      _ ≤ (B : ENNReal) * (O (M j) * μ (⋃ i, Z j i)) := mul_le_mul' le_rfl (hupper j)
      _ = _ := by
        rw [← mul_assoc, O, ENNReal.ofReal_mul (Nat.cast_nonneg B), ENNReal.ofReal_natCast]
  have hnewsum : (∑ i, ∑ j, μ (W' i j)) = ∑ j ∈ J, ∑ i, μ (Z j i) := by
    rw [Finset.sum_comm]
    exact WangZahlLot.Obl.wz_regular_transverse_affine_cells.sum_enumerate J (fun j => ∑ i, μ (Z j i))
  have hret : O (δ ^ h') * ∑ i, μ (Y i) ≤ ∑ i, ∑ j, μ (W' i j) := by
    have hB2 : 0 < (B : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr hB)
    apply WangZahlLot.Obl.wz_rescaled_fibre_alternatives.cancel_volume_factor hB2
    calc
      _ = O ((B : ℝ) ^ 2 * δ ^ h') * ∑ i, μ (Y i) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hB2.le]
      _ ≤ O (δ ^ h) * ∑ i, μ (Y i) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hmassbudget) le_rfl
      _ ≤ ∑ i, ∑ j, μ (D.W i j) := D.mass
      _ = ∑ j, ∑ i, μ (D.W i j) := Finset.sum_comm
      _ ≤ ∑ j, (B : ENNReal) * ∑ i, μ (Z j i) :=
        Finset.sum_le_sum (fun j _ => by simpa only [Fintype.card_fin] using hmass j)
      _ = (B : ENNReal) * ∑ j, ∑ i, μ (Z j i) := (Finset.mul_sum _ _ _).symm
      _ ≤ (B : ENNReal) * ((B : ENNReal) * ∑ j ∈ J, ∑ i, μ (Z j i)) :=
        mul_le_mul' le_rfl hselect
      _ = _ := by
        rw [hnewsum, ← mul_assoc, ENNReal.ofReal_pow (Nat.cast_nonneg B), ENNReal.ofReal_natCast, pow_two]
  let D' : PrismData ω ζ δ h' ρ c n x v Y := {
    a := D.a
    L := J.card
    N := D.N
    z := D.z ∘ fj
    e := D.e ∘ fj
    W := W'
    y := D.y
    w := D.w
    γ := D.γ ∘ fj
    lower := D.lower
    middle := D.middle
    upper := D.upper
    length := D.length
    pieces := fun i j => ⟨(hZ (fj j) i).1, (hZ (fj j) i).2.trans (D.pieces i (fj j)).2.1,
      fun j' hne => ((D.pieces i (fj j)).2.2 (fj j')
        (fun he => hne (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective J he))).mono
        (hZ (fj j) i).2 (hZ (fj j') i).2⟩
    mass := hret
    dense := fun j => hdense (fj j)
    crossing := fun i j hne => D.crossing i (fj j) (hne.mono (hZ (fj j) i).2)
    broad := by
      intro j p u r hu hdr hrρ
      by_cases hp : p ∈ ⋃ i, Z (fj j) i
      · have he := (hlevel (fj j) p hp).2.2
        change q n {i | p ∈ Z (fj j) i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
          δ ^ (-h') * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ Z (fj j) i}
        simp only [he]
        apply (D.broad (fj j) p u r hu hdr hrρ).trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hhh'))
            (Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ.le) _)) (Nat.cast_nonneg _)
      · have he (i : Fin n) : p ∉ W' i j :=
          fun hi => hp (Set.mem_iUnion.mpr ⟨i, hi⟩)
        simp only [he, false_and, Set.ofPred_false, q, Set.ncard_empty, Nat.cast_zero, mul_zero, le_refl]
    distinct := D.distinct
    unit := D.unit
    geometry := fun j => D.geometry (fj j)
    disjoint := by
      intro j j' hne he
      apply (D.disjoint (fj j) (fj j')
        (fun hh => hne (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective J hh)) he).mono
      · exact Set.iUnion_mono (fun i => (hZ (fj j) i).2)
      · exact Set.iUnion_mono (fun i => (hZ (fj j') i).2)
  }
  refine ⟨D', (2 : ℝ) ^ m, rfl, by positivity, ?_, ?_⟩
  · intro j p hp
    have hh := hlevel (fj j) p hp
    have hj : k (fj j) = m := hJ (fj j) (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_mem J j)
    rw [hj] at hh
    have he : {i | p ∈ W' i j} = (Finset.univ.filter (fun i => p ∈ Z (fj j) i) : Set (Fin n)) := by
      ext i
      simp [W']
    change q n {i | p ∈ W' i j} ∈ Set.Icc ((2 : ℝ) ^ m) (2 * 2 ^ m)
    simp only [he, q, Set.ncard_coe_finset, Set.mem_Icc]
    constructor
    · exact_mod_cast hh.1
    · have hhi : (Finset.univ.filter fun i => p ∈ Z (fj j) i).card ≤ 2 * 2 ^ m := by
        have hh' := hh.2.1
        rw [pow_succ] at hh'
        omega
      exact_mod_cast hhi
  · intro i j j' hne he hnonempty
    exact (havoid i (fj j) (fj j')
      (fun hh => hne (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective J hh)) he
      (hnonempty.mono (hZ (fj j) i).2)).mono_left (hZ (fj j') i).2

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
