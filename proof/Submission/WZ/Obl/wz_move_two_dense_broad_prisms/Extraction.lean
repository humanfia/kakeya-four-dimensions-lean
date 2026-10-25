-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.Extraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.GreedyGrains

/-! The finite iteration in WZ Lemma 8.2, Step 4. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set
open scoped ENNReal

/-- A nonempty finite family of good pieces at a common scale supplies the exact
stage-0 predicate once its retained mass is large enough. -/
theorem stage_zero_of_pieces {n N J : ℕ} {ω ζ d h a c s : ℝ} {ρ : Fin J → ℝ}
    {x v : Fin n → V} {y w : Fin N → V} {Y : Fin n → Set V}
    (F : Finset (PrismPiece n N J)) (hF : F.Nonempty) (k : Fin J)
    (hgood : ∀ B ∈ F, B.Good ω ζ d h a c s ρ x v y w)
    (hscale : ∀ B ∈ F, B.scale = k)
    (hsub : ∀ B ∈ F, ∀ i, B.piece i ⊆ Y i)
    (hdis : ∀ i, PairwiseDisjoint (F : Set (PrismPiece n N J)) (fun B => B.piece i))
    (hmass : O (d ^ h) * ∑ i, μ (Y i) ≤ ∑ B ∈ F, ∑ i, μ (B.piece i))
    (hX : X s N y w) (hw : ∀ k, ‖w k‖ = 1) :
    G ω ζ d h (ρ k) c n x v Y 0 := by
  classical
  let L := F.card
  let eqv : Fin L ≃ {B // B ∈ F} := F.equivFin.symm
  let B : Fin L → PrismPiece n N J := fun j => (eqv j).val
  have hBF (j : Fin L) : B j ∈ F := (eqv j).property
  have hBgood (j : Fin L) := hgood (B j) (hBF j)
  have hBscale (j : Fin L) := hscale (B j) (hBF j)
  have hBinj : Function.Injective B := Subtype.val_injective.comp eqv.injective
  have hsum : (∑ j : Fin L, ∑ i, μ ((B j).piece i)) = ∑ B ∈ F, ∑ i, μ (B.piece i) := by
    exact (eqv.sum_comp (fun B : {B // B ∈ F} => ∑ i, μ (B.val.piece i))).trans
      (Finset.sum_coe_sort F (fun B => ∑ i, μ (B.piece i)))
  obtain ⟨B₀, hB₀⟩ := hF
  obtain ⟨hda, hab, hbc, hc1, _⟩ := hgood B₀ hB₀
  rw [hscale B₀ hB₀] at hab hbc
  refine ⟨a, s, L, N, (fun j => (B j).center), (fun j => (B j).frame),
    (fun i j => (B j).piece i), y, w, (fun j => (B j).coarse), hda, hab, hbc, hc1,
    ?_, ?_, ?_, ?_, ?_, hX, hw, ?_, ?_⟩
  · intro i j
    have hg := hBgood j
    refine ⟨(hg.2.2.2.2.1 i).1, ?_, ?_⟩
    · exact fun p hp => ⟨hsub (B j) (hBF j) i hp, by
        simpa only [hBscale j] using (hg.2.2.2.2.1 i).2 hp⟩
    · intro j' hjj'
      exact hdis i (hBF j) (hBF j') (fun heq => hjj' (hBinj heq))
  · rw [Finset.sum_comm, hsum]
    exact hmass
  · intro j
    simpa only [hBscale j] using (hBgood j).2.2.2.2.2.1
  · intro i j hi
    simpa only [Crosses, hBscale j] using (hBgood j).2.2.2.2.2.2.1 i hi
  · intro j p u r hu hr hrρ
    have hh := (hBgood j).2.2.2.2.2.2.2
    rw [hBscale j] at hh
    exact hh p u r hu hr hrρ
  · omega
  · omega

/-- Pigeonhole the finite extracted family by its scale label. -/
lemma weighted_scale_selection {α : Type*} {J : ℕ} (hJ : 0 < J)
    (F : Finset α) (label : α → Fin J) (weight : α → ℝ) :
    ∃ k : Fin J, (∑ B ∈ F, weight B) ≤
      J * ∑ B ∈ F.filter (fun B => label B = k), weight B := by
  classical
  let mass (k : Fin J) := ∑ B ∈ F.filter (fun B => label B = k), weight B
  have hne : (Finset.univ : Finset (Fin J)).Nonempty := ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ mass hne
  refine ⟨k, ?_⟩
  have hsum : (∑ k : Fin J, mass k) = ∑ B ∈ F, weight B := by
    simp only [mass, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  rw [← hsum]
  calc
    (∑ k : Fin J, mass k) ≤ ∑ _k : Fin J, mass k :=
      Finset.sum_le_sum fun k' _ => hk k' (Finset.mem_univ _)
    _ = J * mass k := by simp

/-- Finite iteration and scale pigeonholing produce stage zero from a local
selector on every large residual shading. -/
theorem stage_zero_of_residual_selector {n N J : ℕ} (hJ : 0 < J)
    {ω ζ d h τ a c s q₀ : ℝ} {ρ : Fin J → ℝ}
    {x v : Fin n → V} {y w : Fin N → V} {Y Z : Fin n → Set V}
    (hd : 0 < d) (hq₀ : 0 < q₀)
    (hYfin : ∀ i, volume (Y i) ≠ ∞)
    (hZm : ∀ i, MeasurableSet (Z i)) (hZY : ∀ i, Z i ⊆ Y i)
    (hYpos : 0 < ∑ i, volume.real (Y i))
    (hretain : d ^ τ * ∑ i, volume.real (Y i) ≤ ∑ i, volume.real (Z i))
    (hbudget : 2 * J * d ^ h ≤ d ^ τ)
    (hX : X s N y w) (hw : ∀ k, ‖w k‖ = 1)
    (hselect : ∀ R : Fin n → Set V, (∀ i, MeasurableSet (R i)) →
      (∀ i, R i ⊆ Z i) →
      (∑ i, volume.real (Z i)) / 2 ≤ ∑ i, volume.real (R i) →
      ∃ B : PrismPiece n N J, B.Good ω ζ d h a c s ρ x v y w ∧
        (∀ i, B.piece i ⊆ R i) ∧ q₀ ≤ ∑ i, volume.real (B.piece i)) :
    ∃ k : Fin J, G ω ζ d h (ρ k) c n x v Y 0 := by
  classical
  have hZfin (i) : volume (Z i) ≠ ∞ := measure_ne_top_of_subset (hZY i) (hYfin i)
  obtain ⟨F, hF, hdis, hmass⟩ := finite_greedy_shading_extraction volume Z
    (fun B : PrismPiece n N J => B.piece)
    (fun B => B.Good ω ζ d h a c s ρ x v y w) hZm hZfin hq₀ (by
      intro R hRm hRZ hRmass
      obtain ⟨B, hB, hBR, hBmass⟩ := hselect R hRm hRZ hRmass
      exact ⟨B, hB, fun i => ⟨(hB.2.2.2.2.1 i).1, hBR i⟩, hBmass⟩)
  have hBfin (B) (hB : B ∈ F) (i) : volume (B.piece i) ≠ ∞ :=
    measure_ne_top_of_subset ((hF B hB).2 i).2 (hZfin i)
  have hsum : (∑ i, volume.real (⋃ B ∈ F, B.piece i)) =
      ∑ B ∈ F, ∑ i, volume.real (B.piece i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact measureReal_biUnion_finset (hdis i) (fun B hB => ((hF B hB).2 i).1)
      (fun B hB => hBfin B hB i)
  rw [hsum] at hmass
  obtain ⟨k, hk⟩ := weighted_scale_selection hJ F PrismPiece.scale
    (fun B => ∑ i, volume.real (B.piece i))
  let Fk := F.filter (fun B => B.scale = k)
  have hFk (B) (hB : B ∈ Fk) : B ∈ F := (Finset.mem_filter.mp hB).1
  have hreal : d ^ h * (∑ i, volume.real (Y i)) ≤
      ∑ B ∈ Fk, ∑ i, volume.real (B.piece i) := by
    have h0 : 0 < (J : ℝ) := Nat.cast_pos.mpr hJ
    have h1 := mul_le_mul_of_nonneg_right hbudget hYpos.le
    change (∑ B ∈ F, ∑ i, volume.real (B.piece i)) ≤
      J * ∑ B ∈ Fk, ∑ i, volume.real (B.piece i) at hk
    nlinarith
  have hFkne : Fk.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty.mp hnot, Finset.sum_empty] at hreal
    exact (not_le.mpr (mul_pos (Real.rpow_pos_of_pos hd _) hYpos)) hreal
  refine ⟨k, stage_zero_of_pieces Fk hFkne k
    (fun B hB => (hF B (hFk B hB)).1)
    (fun B hB => (Finset.mem_filter.mp hB).2)
    (fun B hB i => (((hF B (hFk B hB)).2 i).2).trans (hZY i))
    (fun i B hB B' hB' hne => hdis i (hFk B hB) (hFk B' hB') hne) ?_ hX hw⟩
  have hleftfin : O (d ^ h) * ∑ i, μ (Y i) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.mpr (fun i _ => hYfin i))
  have hrightfin : (∑ B ∈ Fk, ∑ i, μ (B.piece i)) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun B hB => ENNReal.sum_ne_top.mpr (fun i _ => hBfin B (hFk B hB) i))
  apply (ENNReal.toReal_le_toReal hleftfin hrightfin).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hd.le _),
    ENNReal.toReal_sum (fun i _ => hYfin i),
    ENNReal.toReal_sum (fun B hB => ENNReal.sum_ne_top.mpr (fun i _ => hBfin B (hFk B hB) i))]
  convert hreal using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro B hB
    exact ENNReal.toReal_sum (fun i _ => hBfin B (hFk B hB) i)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
