-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedPrismExtraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedPrismPiece
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.VariableExtraction
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CappedEndpoint

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms
  (PrismPiece finite_greedy_shading_extraction weighted_scale_selection)
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- Assemble finitely many capped pieces without forgetting their cap
witnesses. Pieces are disjoint on each fine tube, as in the accepted greedy
extraction, while different tubes may overlap. -/
theorem capped_prism_data_of_pieces {n N J : ℕ} {ω ζ d h a c s : ℝ}
    {ρ : Fin J → ℝ} {x v : Fin n → V} {y w : Fin N → V} {Y : Fin n → Set V}
    (F : Finset (PrismPiece n N J)) (hF : F.Nonempty) (k : Fin J)
    (hgood : ∀ Q ∈ F, Q.Good ω ζ d h a c s ρ x v y w)
    (hcaps : ∀ Q ∈ F, PrismPieceCap d h a c ρ Q)
    (hscale : ∀ Q ∈ F, Q.scale = k)
    (hsub : ∀ Q ∈ F, ∀ i, Q.piece i ⊆ Y i)
    (hdis : ∀ i, PairwiseDisjoint (F : Set (PrismPiece n N J)) (fun Q => Q.piece i))
    (hmass : O (d ^ h) * ∑ i, μ (Y i) ≤ ∑ Q ∈ F, ∑ i, μ (Q.piece i))
    (hX : X s N y w) (hw : ∀ k, ‖w k‖ = 1) :
    ∃ D : PrismData n, D.Valid ω ζ d h (ρ k) c x v Y 0 ∧ D.HasCaps d h (ρ k) c := by
  classical
  let L := F.card
  let eqv : Fin L ≃ {Q // Q ∈ F} := F.equivFin.symm
  let Q : Fin L → PrismPiece n N J := fun j => (eqv j).val
  have hQF (j : Fin L) : Q j ∈ F := (eqv j).property
  have hQgood (j : Fin L) := hgood (Q j) (hQF j)
  have hQscale (j : Fin L) := hscale (Q j) (hQF j)
  have hQinj : Function.Injective Q := Subtype.val_injective.comp eqv.injective
  let D : PrismData n := ⟨a, s, L, N, (fun j => (Q j).center), (fun j => (Q j).frame),
    (fun i j => (Q j).piece i), y, w, (fun j => (Q j).coarse)⟩
  have hsum : (∑ j : Fin L, ∑ i, μ ((Q j).piece i)) = ∑ Q ∈ F, ∑ i, μ (Q.piece i) :=
    (eqv.sum_comp (fun Q : {Q // Q ∈ F} => ∑ i, μ (Q.val.piece i))).trans
      (Finset.sum_coe_sort F (fun Q => ∑ i, μ (Q.piece i)))
  obtain ⟨Q₀, hQ₀⟩ := hF
  have hg₀ := hgood Q₀ hQ₀
  unfold PrismPiece.Good at hg₀
  rw [hscale Q₀ hQ₀] at hg₀
  refine ⟨D, ?_, ?_⟩
  · refine ⟨hg₀.1, hg₀.2.1, hg₀.2.2.1, hg₀.2.2.2.1, ?_, ?_, ?_, ?_, ?_, hX, hw, ?_, ?_⟩
    · intro i j
      have hg := hQgood j
      refine ⟨(hg.2.2.2.2.1 i).1, ?_, ?_⟩
      · exact fun p hp => ⟨hsub (Q j) (hQF j) i hp, by
          simpa only [hQscale j] using (hg.2.2.2.2.1 i).2 hp⟩
      · intro j' hne
        exact hdis i (hQF j) (hQF j') (fun he => hne (hQinj he))
    · change O (d ^ h) * ∑ i, μ (Y i) ≤ ∑ i, ∑ j : Fin L, μ ((Q j).piece i)
      rw [Finset.sum_comm, hsum]
      exact hmass
    · intro j
      simpa only [hQscale j] using (hQgood j).2.2.2.2.2.1
    · intro i j hi
      simpa only [hQscale j, WangZahlLot.Obl.wz_move_two_dense_broad_prisms.Crosses] using
        (hQgood j).2.2.2.2.2.2.1 i hi
    · intro j p u r hu hr hrρ
      have hh := (hQgood j).2.2.2.2.2.2.2
      rw [hQscale j] at hh
      exact hh p u r hu hr hrρ
    · omega
    · omega
  · have hex := fun j => hcaps (Q j) (hQF j)
    choose m hm hc ha using hex
    refine ⟨m, hm, hc, ?_⟩
    intro j
    simpa only [hQscale j] using ha j

/-- The finite residual iteration can retain arbitrary positive caps on its
selected pieces. Only the usual finite palette loss occurs. -/
theorem capped_stage_zero_of_variable_selector {n N J : ℕ} (hJ : 0 < J)
    {ω ζ d h τ s : ℝ} {a c ρ : Fin J → ℝ} (valid : Fin J → Prop)
    {x v : Fin n → V} {y w : Fin N → V} {Y Z : Fin n → Set V}
    (hd : 0 < d) (hYfin : ∀ i, volume (Y i) ≠ ∞)
    (hZm : ∀ i, MeasurableSet (Z i)) (hZY : ∀ i, Z i ⊆ Y i)
    (hYpos : 0 < ∑ i, volume.real (Y i))
    (hretain : d ^ τ * (∑ i, volume.real (Y i)) ≤ ∑ i, volume.real (Z i))
    (hbudget : 2 * J * d ^ h ≤ d ^ τ) (hX : X s N y w) (hw : ∀ k, ‖w k‖ = 1)
    (hselect : ∀ R : Fin n → Set V, (∀ i, MeasurableSet (R i)) →
      (∀ i, R i ⊆ Z i) → (∑ i, volume.real (Z i)) / 2 ≤ ∑ i, volume.real (R i) →
      ∃ Q : PrismPiece n N J,
        Q.Good ω ζ d h (a Q.scale) (c Q.scale) s ρ x v y w ∧ valid Q.scale ∧
        (∀ i, Q.piece i ⊆ R i) ∧ PrismPieceCap d h (a Q.scale) (c Q.scale) ρ Q) :
    ∃ k : Fin J, valid k ∧ ∃ D : PrismData n,
      D.Valid ω ζ d h (ρ k) (c k) x v Y 0 ∧ D.HasCaps d h (ρ k) (c k) := by
  classical
  have hZfin (i) : volume (Z i) ≠ ∞ := measure_ne_top_of_subset (hZY i) (hYfin i)
  let Good : PrismPiece n N J → Prop := fun Q =>
    Q.Good ω ζ d h (a Q.scale) (c Q.scale) s ρ x v y w ∧ valid Q.scale ∧
      PrismPieceCap d h (a Q.scale) (c Q.scale) ρ Q
  obtain ⟨F, hF, hdis, hmass⟩ := finite_greedy_shading_extraction volume Z
    (fun Q : PrismPiece n N J => Q.piece) Good hZm hZfin
    (mul_pos (Real.rpow_pos_of_pos hd h) (pow_pos hd 3)) (by
      intro R hRm hRZ hRmass
      obtain ⟨Q, hQ, hv, hQR, hc⟩ := hselect R hRm hRZ hRmass
      exact ⟨Q, ⟨hQ, hv, hc⟩, fun i => ⟨(hQ.2.2.2.2.1 i).1, hQR i⟩, hQ.incidence_mass hd⟩)
  have hQfin (Q) (hQ : Q ∈ F) (i) : volume (Q.piece i) ≠ ∞ :=
    measure_ne_top_of_subset ((hF Q hQ).2 i).2 (hZfin i)
  have hsum : (∑ i, volume.real (⋃ Q ∈ F, Q.piece i)) =
      ∑ Q ∈ F, ∑ i, volume.real (Q.piece i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact measureReal_biUnion_finset (hdis i) (fun Q hQ => ((hF Q hQ).2 i).1)
      (fun Q hQ => hQfin Q hQ i)
  rw [hsum] at hmass
  obtain ⟨k, hk⟩ := weighted_scale_selection hJ F PrismPiece.scale
    (fun Q => ∑ i, volume.real (Q.piece i))
  let Fk := F.filter (fun Q => Q.scale = k)
  have hFk (Q) (hQ : Q ∈ Fk) : Q ∈ F := (Finset.mem_filter.mp hQ).1
  have hscale (Q) (hQ : Q ∈ Fk) : Q.scale = k := (Finset.mem_filter.mp hQ).2
  have hreal : d ^ h * (∑ i, volume.real (Y i)) ≤
      ∑ Q ∈ Fk, ∑ i, volume.real (Q.piece i) := by
    have hJpos : 0 < (J : ℝ) := Nat.cast_pos.mpr hJ
    have hcost := mul_le_mul_of_nonneg_right hbudget hYpos.le
    change (∑ Q ∈ F, ∑ i, volume.real (Q.piece i)) ≤
      J * ∑ Q ∈ Fk, ∑ i, volume.real (Q.piece i) at hk
    nlinarith
  have hFkne : Fk.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hreal
    exact (not_le.mpr (mul_pos (Real.rpow_pos_of_pos hd _) hYpos)) hreal
  obtain ⟨Q₀, hQ₀⟩ := hFkne
  have hvk : valid k := by
    simpa only [hscale Q₀ hQ₀] using (hF Q₀ (hFk Q₀ hQ₀)).1.2.1
  refine ⟨k, hvk, capped_prism_data_of_pieces Fk ⟨Q₀, hQ₀⟩ k
    (fun Q hQ => by simpa only [hscale Q hQ] using (hF Q (hFk Q hQ)).1.1)
    (fun Q hQ => by simpa only [hscale Q hQ] using (hF Q (hFk Q hQ)).1.2.2)
    hscale (fun Q hQ i => (((hF Q (hFk Q hQ)).2 i).2).trans (hZY i))
    (fun i Q hQ Q' hQ' hne => hdis i (hFk Q hQ) (hFk Q' hQ') hne) ?_ hX hw⟩
  have hleftfin : O (d ^ h) * ∑ i, μ (Y i) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.mpr (fun i _ => hYfin i))
  have hrightfin : (∑ Q ∈ Fk, ∑ i, μ (Q.piece i)) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun Q hQ => ENNReal.sum_ne_top.mpr
      (fun i _ => hQfin Q (hFk Q hQ) i))
  apply (ENNReal.toReal_le_toReal hleftfin hrightfin).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hd.le h),
    ENNReal.toReal_sum (fun i _ => hYfin i),
    ENNReal.toReal_sum (fun Q hQ => ENNReal.sum_ne_top.mpr (fun i _ => hQfin Q (hFk Q hQ) i))]
  convert hreal using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro Q hQ
    exact ENNReal.toReal_sum (fun i _ => hQfin Q (hFk Q hQ) i)

end WangZahlLot.Obl.wz_broad_grains_improvement
