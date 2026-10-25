-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PrismPieces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PrismCores
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.EndTrimming

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

namespace Interfaces

theorem measurableSet_prism (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    MeasurableSet (P a b c z e) := by
  have hcont (i : Fin 3) : Continuous (fun p : V => |e (p - z) i|) := by fun_prop
  exact ((isClosed_le (hcont 0) continuous_const).inter
    ((isClosed_le (hcont 1) continuous_const).inter
      (isClosed_le (hcont 2) continuous_const))).measurableSet

end Interfaces

/-- Select disjoint prism cores using total shading mass as the measure. -/
theorem shading_prism_core_selection :
    ∃ D : ℕ, 0 < D ∧ ∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c →
      ∀ (e : Space ≃ₗᵢ[ℝ] Space) (n : ℕ) (Y : Fin n → Set Space),
      (∀ i, MeasurableSet (Y i)) → TotallyBounded (⋃ i, Y i) →
      ∃ F : Finset Space, (↑F : Set Space) ⊆ ⋃ i, Y i ∧
        (↑F : Set Space).PairwiseDisjoint (fun z => Interfaces.P a b c z e) ∧
        (∑ i, volume (Y i)) ≤ (D : ENNReal) *
          ∑ i, volume (Y i ∩ ⋃ z ∈ F, Interfaces.P (a / 8) (b / 8) (c / 8) z e) := by
  classical
  obtain ⟨D, hD, hcore⟩ := exists_disjoint_prism_cores
  refine ⟨D, hD, ?_⟩
  intro a b c ha hb hc e n Y hY hbounded
  let E := ⋃ i, Y i
  have hEm : MeasurableSet E := MeasurableSet.iUnion hY
  let μ : Measure Space := ∑ i, volume.restrict (Y i)
  obtain ⟨F, hFE, hFdisj, hmass⟩ := hcore a b c ha hb hc e μ hEm hbounded
  let W := ⋃ z ∈ F, Interfaces.P (a / 8) (b / 8) (c / 8) z e
  have hWm : MeasurableSet W := F.measurableSet_biUnion
    (fun z _ => Interfaces.measurableSet_prism _ _ _ z e)
  have hμE : μ E = ∑ i, volume (Y i) := by
    simp only [μ, Measure.finsetSum_apply, Measure.restrict_apply hEm]
    apply Finset.sum_congr rfl
    intro i _
    rw [inter_eq_right.mpr (subset_iUnion Y i)]
  have hμW : μ (E ∩ W) = ∑ i, volume (Y i ∩ W) := by
    simp only [μ, Measure.finsetSum_apply, Measure.restrict_apply (hEm.inter hWm)]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ext p
    constructor
    · exact fun hp => ⟨hp.2, hp.1.2⟩
    · exact fun hp => ⟨⟨subset_iUnion Y i hp.1, hp.2⟩, hp.1⟩
  rw [hμE, hμW] at hmass
  exact ⟨F, hFE, hFdisj, hmass⟩

namespace Interfaces

/-- Construct disjoint prism pieces and the exact crossing clauses for a
family with prescribed short direction bounds. The remaining grains inputs
(coarse cover, density and local convex counts) are not assumed here. -/
theorem geometric_prism_piece_refinement :
    ∃ D : ℕ, 0 < D ∧ ∀ (δ a b c lam : ℝ), 0 < δ →
      16 * δ ≤ a → 16 * δ ≤ b → 16 * δ ≤ c → c ≤ 1 / 2 → 2560 * c ≤ lam →
      ∀ (e : V ≃ₗᵢ[ℝ] V) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      (∀ i, ‖v i‖ = 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) →
      TotallyBounded (⋃ i, Y i) →
      o (lam * n * δ ^ 2) ≤ ∑ i, μ (Y i) →
      (∀ i, 1 / 2 ≤ |e (v i) 2| ∧ c * |e (v i) 0| ≤ a / 16 ∧
        c * |e (v i) 1| ≤ b / 16) →
      ∃ (F : Finset V) (Z : Fin n → Set V) (H : V → Set V),
        (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
        (↑F : Set V).PairwiseDisjoint (fun z => P a b c z e) ∧
        (∀ z ∈ F, MeasurableSet (H z) ∧ H z ⊆ P a b c z e) ∧
        (⋃ z ∈ F, H z) = ⋃ i, Z i ∧
        (∑ i, μ (Y i)) ≤ (D : ENNReal) * ∑ i, μ (Z i) ∧
        (∀ i z, z ∈ F → (Z i ∩ H z).Nonempty →
          Z i ∩ P a b c z e ⊆ H z ∧
          (∀ p ∈ T δ (x i) (v i) ∩ frontier (P a b c z e), |e (p - z) 2| = c / 2) ∧
          (∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
            ∃ p ∈ T δ (x i) (v i) ∩ P a b c z e, e (p - z) 2 = t)) := by
  classical
  obtain ⟨D, hD, hselect⟩ := shading_prism_core_selection
  refine ⟨2 * D, by omega, ?_⟩
  intro δ a b c lam hδ hδa hδb hδc hc hbudget e n x v Y hY hbounded hdense hdir
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  obtain ⟨Y₀, hY₀, hhalf⟩ := trim_tube_ends_half x v Y hδ (by linarith) hc hbudget
    (fun i => (hY i).1) (fun i => (hY i).2.1) hdense
  have hbounded₀ : TotallyBounded (⋃ i, Y₀ i) :=
    hbounded.subset (iUnion_mono fun i => (hY₀ i).2.1)
  obtain ⟨F, -, hFdisj, hmass⟩ := hselect a b c ha hb hc0 e n Y₀
    (fun i => (hY₀ i).1) hbounded₀
  let W := ⋃ z ∈ F, P (a / 8) (b / 8) (c / 8) z e
  let Z := fun i => Y₀ i ∩ W
  let H := fun z => (⋃ i, Z i) ∩ P a b c z e
  have hWm : MeasurableSet W := F.measurableSet_biUnion
    (fun z _ => measurableSet_prism _ _ _ z e)
  have hZm (i : Fin n) : MeasurableSet (Z i) := (hY₀ i).1.inter hWm
  have hsmall (z : V) : P (a / 8) (b / 8) (c / 8) z e ⊆ P a b c z e := by
    intro p hp
    exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hZU : (⋃ i, Z i) ⊆ ⋃ z ∈ F, P a b c z e := by
    intro p hp
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
    obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hpi.2
    exact mem_iUnion₂.mpr ⟨z, hz, hsmall z hpz⟩
  have hZcore (i : Fin n) (z : V) (hz : z ∈ F) :
      Z i ∩ P a b c z e ⊆ P (a / 8) (b / 8) (c / 8) z e := by
    intro p hp
    obtain ⟨z', hz', hpz'⟩ := mem_iUnion₂.mp hp.1.2
    by_cases he : z' = z
    · exact he ▸ hpz'
    · exact False.elim (Set.disjoint_left.mp (hFdisj hz' hz he) (hsmall z' hpz') hp.2)
  refine ⟨F, Z, H, (fun i => ⟨hZm i, inter_subset_left.trans (hY₀ i).2.1⟩),
    hFdisj, (fun z _ => ⟨(MeasurableSet.iUnion hZm).inter (measurableSet_prism _ _ _ z e),
      inter_subset_right⟩), ?_, ?_, ?_⟩
  · ext p
    constructor
    · intro hp
      obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
      exact hpz.1
    · intro hp
      obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp (hZU hp)
      exact mem_iUnion₂.mpr ⟨z, hz, hp, hpz⟩
  · calc
      (∑ i, μ (Y i)) = 2 * ((1 / 2 : ENNReal) * ∑ i, μ (Y i)) := by
        rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ 2 * ∑ i, μ (Y₀ i) := mul_le_mul_right hhalf _
      _ ≤ 2 * ((D : ENNReal) * ∑ i, μ (Z i)) := mul_le_mul_right hmass _
      _ = _ := by rw [Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  · intro i z hz hmeet
    obtain ⟨q, hqZi, hqH⟩ := hmeet
    have hqcore := hZcore i z hz ⟨hqZi, hqH.2⟩
    have hqend : q ∈ T δ (x i) (v i) \ tubeEnds δ c (x i) (v i) :=
      ⟨(hY i).2.2 ((hY₀ i).2.1 hqZi.1),
        fun hqE => Set.disjoint_left.mp (hY₀ i).2.2 hqZi.1 hqE⟩
    have hcross := prism_crossing_of_core_point e hδ hδa hδb hδc
      (hdir i).1 (hdir i).2.1 (hdir i).2.2 ⟨hqend, hqcore⟩
    exact ⟨fun p hp => ⟨subset_iUnion Z i hp.1, hp.2⟩, hcross⟩

end Interfaces
end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
