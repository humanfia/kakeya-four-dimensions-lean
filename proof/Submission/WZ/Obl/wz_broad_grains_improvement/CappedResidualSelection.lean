-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedResidualSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.LocalPrismCapsPower
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedPrismExtraction

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (PrismPiece)
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- An ordinary local selector already suffices for capped global extraction:
cap its individual outputs before the finite residual iteration. -/
theorem capped_stage_zero_of_good_selector {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
      ∀ {n N J : ℕ}, 0 < J →
      ∀ {ω ζ d h τ s : ℝ} {a c ρ : Fin J → ℝ} (valid : Fin J → Prop)
        {x v : Fin n → V} {y w : Fin N → V} {Y Z : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ ε/2 → (n:ℝ) ≤ d^(-D) →
      (∀ i, volume (Y i) ≠ ⊤) → (∀ i, MeasurableSet (Z i)) → (∀ i,Z i ⊆ Y i) →
      0 < ∑ i,volume.real (Y i) →
      d^τ*(∑ i,volume.real (Y i)) ≤ ∑ i,volume.real (Z i) →
      2*J*d^ε ≤ d^τ → X s N y w → (∀ k,‖w k‖=1) →
      (∀ R : Fin n → Set V, (∀ i,MeasurableSet (R i)) → (∀ i,R i ⊆ Z i) →
        (∑ i,volume.real (Z i))/2 ≤ ∑ i,volume.real (R i) →
        ∃ Q : PrismPiece n N J, Q.Good ω ζ d h (a Q.scale) (c Q.scale) s ρ x v y w ∧
          valid Q.scale ∧ ∀ i,Q.piece i ⊆ R i) →
      ∃ k : Fin J, valid k ∧ ∃ P : PrismData n,
        P.Valid ω ζ d ε (ρ k) (c k) x v Y 0 ∧ P.HasCaps d ε (ρ k) (c k) := by
  obtain ⟨d₀,hd₀,hd₀1,HC⟩ := capped_cut_of_good_prism_power hε hD
  refine ⟨d₀,hd₀,hd₀1,?_⟩
  intro n N J hJ ω ζ d h τ s a c ρ valid x v y w Y Z hd hdd hh hn
    hYfin hZm hZY hYpos hretain hbudget hX hw hselect
  apply capped_stage_zero_of_variable_selector hJ valid hd hYfin hZm hZY
    hYpos hretain hbudget hX hw
  intro R hRm hRZ hRmass
  obtain ⟨Q,HQ,hvalid,hQR⟩ := hselect R hRm hRZ hRmass
  obtain ⟨C,hCm,Hcut,Hcaps⟩ := HC hd hdd hh hn Q HQ
  exact ⟨cutPrismPiece Q C,Hcut,hvalid,fun i => inter_subset_left.trans (hQR i),Hcaps⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
