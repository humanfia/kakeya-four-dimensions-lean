-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.VariableExtraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PieceMass

/-! Finite extraction with a palette of thicknesses and lengths as well as angles. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory
open scoped ENNReal

/-- A finite label can record length and thickness in addition to broadness.
An arbitrary validity predicate is inherited by the selected common label. -/
theorem stage_zero_of_variable_residual_selector {n N J : ℕ} (hJ : 0 < J)
    {ω ζ d h τ s q₀ : ℝ} {a c ρ : Fin J → ℝ} (valid : Fin J → Prop)
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
      ∃ B : PrismPiece n N J, B.Good ω ζ d h (a B.scale) (c B.scale) s ρ x v y w ∧ valid B.scale ∧
        (∀ i, B.piece i ⊆ R i) ∧ q₀ ≤ ∑ i, volume.real (B.piece i)) :
    ∃ k : Fin J, valid k ∧ G ω ζ d h (ρ k) (c k) n x v Y 0 := by
  classical
  have hZfin (i) : volume (Z i) ≠ ∞ := measure_ne_top_of_subset (hZY i) (hYfin i)
  obtain ⟨F, hF, hdis, hmass⟩ := finite_greedy_shading_extraction volume Z
    (fun B : PrismPiece n N J => B.piece)
    (fun B => B.Good ω ζ d h (a B.scale) (c B.scale) s ρ x v y w ∧ valid B.scale) hZm hZfin hq₀ (by
      intro R hRm hRZ hRmass
      obtain ⟨B, hB, hvalid, hBR, hBmass⟩ := hselect R hRm hRZ hRmass
      exact ⟨B, ⟨hB, hvalid⟩, fun i => ⟨(hB.2.2.2.2.1 i).1, hBR i⟩, hBmass⟩)
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
  have hscale (B) (hB : B ∈ Fk) : B.scale = k := (Finset.mem_filter.mp hB).2
  obtain ⟨B₀, hB₀⟩ := hFkne
  have hvk : valid k := by simpa only [hscale B₀ hB₀] using (hF B₀ (hFk B₀ hB₀)).1.2
  refine ⟨k, hvk, stage_zero_of_pieces Fk ⟨B₀, hB₀⟩ k
    (fun B hB => by simpa only [hscale B hB] using (hF B (hFk B hB)).1.1)
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


/-- Density again supplies the positive increment for the finite iteration. -/
theorem stage_zero_of_variable_selector {n N J : ℕ} (hJ : 0 < J)
    {ω ζ d h τ s : ℝ} {a c ρ : Fin J → ℝ} (valid : Fin J → Prop)
    {x v : Fin n → V} {y w : Fin N → V} {Y Z : Fin n → Set V}
    (hd : 0 < d) (hYfin : ∀ i, volume (Y i) ≠ ∞)
    (hZm : ∀ i, MeasurableSet (Z i)) (hZY : ∀ i, Z i ⊆ Y i)
    (hYpos : 0 < ∑ i, volume.real (Y i))
    (hretain : d^τ*(∑ i, volume.real (Y i)) ≤ ∑ i, volume.real (Z i))
    (hbudget : 2*J*d^h ≤ d^τ) (hX : X s N y w) (hw : ∀ k, ‖w k‖ = 1)
    (hselect : ∀ R : Fin n → Set V, (∀ i, MeasurableSet (R i)) →
      (∀ i, R i ⊆ Z i) → (∑ i, volume.real (Z i))/2 ≤ ∑ i, volume.real (R i) →
      ∃ B : PrismPiece n N J, B.Good ω ζ d h (a B.scale) (c B.scale) s ρ x v y w ∧
        valid B.scale ∧ ∀ i, B.piece i ⊆ R i) :
    ∃ k : Fin J, valid k ∧ G ω ζ d h (ρ k) (c k) n x v Y 0 := by
  apply stage_zero_of_variable_residual_selector hJ valid hd
    (mul_pos (Real.rpow_pos_of_pos hd h) (pow_pos hd 3))
    hYfin hZm hZY hYpos hretain hbudget hX hw
  intro R hRm hRZ hRmass
  obtain ⟨B, hB, hvalid, hBR⟩ := hselect R hRm hRZ hRmass
  exact ⟨B, hB, hvalid, hBR, hB.incidence_mass hd⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
