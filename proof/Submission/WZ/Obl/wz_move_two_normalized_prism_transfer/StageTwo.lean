-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.StageTwo.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Assignment
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.SelectedUnion
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.PrismData
import Submission.WZ.Obl.wz_coarse_grains_assembly.Restrict
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.MassTransfer

noncomputable section
namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
open Set MeasureTheory

/-- At an absolute cost in mass, stage two can be made compatible with a unique fine
assignment. All the original prism geometry, density and broadness is retained. -/
theorem assigned_stage_two_with_embedding {ω ζ δ η h ρ c : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηh : η ≤ h)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (D : PrismData ω ζ δ η ρ c n x v Y)
    (hbudget : (10 ^ 16 : ℝ) * δ ^ h ≤ δ ^ η) :
    ∃ (D' : PrismData ω ζ δ h ρ c n x v Y) (f : Fin n → Fin D'.N)
      (S : Finset (Fin n)) (Z : Fin n → Set V),
      D'.a = D.a ∧
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅)) ∧
      O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i) ∧
      (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (D'.y (f i)) (D'.w (f i))) ∧
      (∀ i j, (D'.W i j).Nonempty → i ∈ S ∧ f i = D'.γ j) ∧
      (∀ i, Z i = ⋃ j, D'.W i j) ∧
      Broad ω ζ δ h ρ n D'.N v S Z f ∧
      (∀ i k k', T δ (x i) (v i) ⊆ T ρ (D'.y k) (D'.w k) →
        T δ (x i) (v i) ⊆ T ρ (D'.y k') (D'.w k') → k = k') ∧
      ∃ fj : Fin D'.L → Fin D.L, Function.Injective fj ∧
        (∀ i j, D'.W i j = D.W i (fj j)) ∧
        (∀ j, P D'.a (ρ * c) c (D'.z j) (D'.e j) =
          P D.a (ρ * c) c (D.z (fj j)) (D.e (fj j))) ∧
        ∀ j j', D'.γ j = D'.γ j' → D.γ (fj j) = D.γ (fj j') := by
  classical
  have ha : 0 < D.a := hδ.trans_le D.lower
  have hrc : 0 < ρ * c := ha.trans_le D.middle
  have hc : 0 < c := hrc.trans_le D.upper
  have hρ : 0 < ρ := pos_of_mul_pos_left hrc hc.le
  have hρ1 : ρ ≤ 1 := le_of_mul_le_mul_right (by simpa using D.upper) hc
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
  have hYpos : 0 < ∑ i, μ (Y i) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hA.2.2.2.1
  have hpos : 0 < ∑ i, ∑ j, μ (D.W i j) := lt_of_lt_of_le
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ η)).ne' hYpos.ne') D.mass
  obtain ⟨Q, f, hQ, hmass, hfQ, hassign, huniq⟩ := assigned_prism_selection hδ hρ hρ1
    (fun i => (hA.2.1 i).1) D.unit D.distinct (fun i j => (D.pieces i j).1)
    (fun i j j' hjj' => (D.pieces i j).2.2 j' hjj')
    (fun i j h => (D.crossing i j h).1) hpos
  obtain ⟨S, Z, hZ, hSmem, hcont, hsum, hbr, hWZ, hZW⟩ := selected_fibre_union Q f hfQ hassign
    (fun i j => ⟨(D.pieces i j).1, fun p hp => ((D.pieces i j).2.1 hp).1⟩)
    (fun i j h => (D.crossing i j h).1) D.disjoint D.broad
  have hret : O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i) := by
    apply WangZahlLot.Obl.wz_rescaled_fibre_alternatives.cancel_volume_factor
      (by norm_num : (0 : ℝ) < 10 ^ 16)
    have hcoef : O (10 ^ 16 : ℝ) * O (δ ^ h) ≤ O (δ ^ η) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal hbudget
    calc
      _ = (O (10 ^ 16 : ℝ) * O (δ ^ h)) * ∑ i, μ (Y i) := (mul_assoc _ _ _).symm
      _ ≤ O (δ ^ η) * ∑ i, μ (Y i) := mul_le_mul' hcoef le_rfl
      _ ≤ ∑ i, ∑ j, μ (D.W i j) := D.mass
      _ ≤ (10 ^ 16 : ENNReal) * ∑ k ∈ Q, ∑ i, μ (pieceFibre D.W D.γ k i) := hmass
      _ = _ := by rw [hsum]; norm_num [O]
  let J := Finset.univ.filter (fun j => D.γ j ∈ Q)
  let fj := WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx J
  let fk := WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx Q
  let γ' := fun j => WangZahlLot.Obl.wz_coarse_grains_assembly.rFib Q hQ D.γ (fj j)
  let f' := WangZahlLot.Obl.wz_coarse_grains_assembly.rFib Q hQ f
  have hfj (j : Fin J.card) : D.γ (fj j) ∈ Q :=
    (Finset.mem_filter.mp (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_mem J j)).2
  have hγ' (j : Fin J.card) : fk (γ' j) = D.γ (fj j) :=
    WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_rFib Q hQ D.γ (hfj j)
  have hf' (i : Fin n) : fk (f' i) = f i :=
    WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_rFib Q hQ f (hfQ i)
  have hZeq (i : Fin n) : Z i = ⋃ j : Fin J.card, D.W i (fj j) := by
    ext p
    constructor
    · intro hp
      obtain ⟨j, hj, hji, hpj⟩ := hZW i p hp
      have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      refine Set.mem_iUnion.mpr ⟨J.equivFin ⟨j, hjJ⟩, ?_⟩
      simpa only [fj, WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx, Equiv.symm_apply_apply] using hpj
    · intro hp
      obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hp
      exact hWZ i (fj j) (hfj j) hpj
  have hnewmass : (∑ i ∈ S, μ (Z i)) = ∑ i, ∑ j : Fin J.card, μ (D.W i (fj j)) := by
    calc
      _ = ∑ i, μ (Z i) := Finset.sum_subset (Finset.subset_univ S)
        (fun i _ hi => by simp only [(hZ i).2.2 hi, μ, measure_empty])
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hZeq]
        simpa only [μ, tsum_fintype] using measure_iUnion
          (fun j j' hne => (D.pieces i (fj j)).2.2 (fj j')
            (fun he => hne (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective J he)))
          (fun j => (D.pieces i (fj j)).1)
  have hpowers := WangZahlLot.Obl.wz_coarse_grains_assembly.rpow_err_le hδ hδ1 hηh
  let D' : PrismData ω ζ δ h ρ c n x v Y := {
    a := D.a
    L := J.card
    N := Q.card
    z := D.z ∘ fj
    e := D.e ∘ fj
    W := fun i j => D.W i (fj j)
    y := D.y ∘ fk
    w := D.w ∘ fk
    γ := γ'
    lower := D.lower
    middle := D.middle
    upper := D.upper
    length := D.length
    pieces := fun i j => ⟨(D.pieces i (fj j)).1, (D.pieces i (fj j)).2.1,
      fun j' hne => (D.pieces i (fj j)).2.2 (fj j')
        (fun he => hne (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective J he))⟩
    mass := hret.trans_eq hnewmass
    dense := fun j => (mul_le_mul' (ENNReal.ofReal_le_ofReal hpowers.1) le_rfl).trans (D.dense (fj j))
    crossing := by
      intro i j hne
      simpa only [Function.comp_apply, hγ'] using D.crossing i (fj j) hne
    broad := by
      intro j p u r hu hdr hrρ
      apply (D.broad (fj j) p u r hu hdr hrρ).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpowers.2
          (Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ.le) _)) (Nat.cast_nonneg _)
    distinct := fun k k' hne => D.distinct (fk k) (fk k')
      (fun he => hne (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective Q he))
    unit := fun k => D.unit (fk k)
    geometry := by
      intro j
      simpa only [Function.comp_apply, hγ'] using D.geometry (fj j)
    disjoint := by
      intro j j' hne he
      apply D.disjoint (fj j) (fj j')
        (fun hh => hne (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective J hh))
      simpa only [hγ'] using congrArg fk he
  }
  refine ⟨D', f', S, Z, rfl, hZ, hret, ?_, ?_, hZeq, ?_, ?_, ?_⟩
  · intro i hi
    change T δ (x i) (v i) ⊆ T ρ (D.y (fk (f' i))) (D.w (fk (f' i)))
    rw [hf']
    exact hcont i hi
  · intro i j hne
    obtain ⟨p, hp⟩ := hne
    have hi : p ∈ Z i := hWZ i (fj j) (hfj j) hp
    refine ⟨(hSmem i).mpr ⟨p, hi⟩, ?_⟩
    apply WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective Q
    change fk (f' i) = fk (γ' j)
    rw [hf', hγ']
    exact hassign i (fj j) (hfj j) ⟨p, hp⟩
  · apply WangZahlLot.Obl.wz_coarse_grains_assembly.Broad_mono hδ hδ1 hηh
    have hh := WangZahlLot.Obl.wz_coarse_grains_assembly.broad_restrict Q hQ hbr
    have hs : S.filter (fun i => f i ∈ Q) = S := Finset.filter_true_of_mem (fun i _ => hfQ i)
    rw [hs] at hh
    simpa only [hfQ, ite_true] using hh
  · intro i k k' hik hik'
    apply WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective Q
    exact huniq i (fk k) (fk k')
      (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_mem Q k)
      (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_mem Q k') hik hik'

  · refine ⟨fj, WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective J,
      fun _ _ => rfl, fun _ => rfl, ?_⟩
    intro j j' he
    change γ' j = γ' j' at he
    simpa only [hγ'] using congrArg fk he

/-- At an absolute cost in mass, stage two can be made compatible with a unique fine
assignment. All the original prism geometry, density and broadness is retained. -/
theorem assigned_stage_two {ω ζ δ η h ρ c : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηh : η ≤ h)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (D : PrismData ω ζ δ η ρ c n x v Y)
    (hbudget : (10 ^ 16 : ℝ) * δ ^ h ≤ δ ^ η) :
    ∃ (D' : PrismData ω ζ δ h ρ c n x v Y) (f : Fin n → Fin D'.N)
      (S : Finset (Fin n)) (Z : Fin n → Set V),
      D'.a = D.a ∧
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅)) ∧
      O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i) ∧
      (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (D'.y (f i)) (D'.w (f i))) ∧
      (∀ i j, (D'.W i j).Nonempty → i ∈ S ∧ f i = D'.γ j) ∧
      (∀ i, Z i = ⋃ j, D'.W i j) ∧
      Broad ω ζ δ h ρ n D'.N v S Z f ∧
      ∀ i k k', T δ (x i) (v i) ⊆ T ρ (D'.y k) (D'.w k) →
        T δ (x i) (v i) ⊆ T ρ (D'.y k') (D'.w k') → k = k' := by
  obtain ⟨D', f, S, Z, ha, hZ, hm, hc, has, he, hb, hu, _⟩ :=
    assigned_stage_two_with_embedding hδ hδ1 hηh hA D hbudget
  exact ⟨D', f, S, Z, ha, hZ, hm, hc, has, he, hb, hu⟩

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
