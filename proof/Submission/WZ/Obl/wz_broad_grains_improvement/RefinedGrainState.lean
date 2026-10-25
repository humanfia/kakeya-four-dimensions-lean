-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.RefinedGrainState.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.RefinedGrains
import Submission.WZ.Obl.wz_coarse_grains_assembly.ColorRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CrossScaleCount
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs

/- Adapted from this workspace: o169/x0670, branch x0641, commit5642ec0,
RefinementStage.lean. These unaccepted modules cannot be imported here. -/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory Set
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Broad)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber fiberBodyCount fiberBodyCount_eq_ncard)

private lemma sum_supported {n : ℕ} {S : Finset (Fin n)} {Z : Fin n → Set V}
    (hZ : ∀ i, i ∉ S → Z i = ∅) : (∑ i ∈ S, μ (Z i)) = ∑ i, μ (Z i) := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  simp [hZ i hi, μ]

/-- The pointwise fraction lemma applied separately to the supported fibres. -/
theorem broad_shading_refine {ω ζ δ h h' ρ R : ℝ} {n N : ℕ}
    {v : Fin n → V} {S : Finset (Fin n)} {Z W : Fin n → Set V}
    {f : Fin n → Fin N} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hWZ : ∀ i, W i ⊆ Z i)
    (hfrac : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} ≤
        R * q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i})
    (hbudget : R * δ ^ (-h) ≤ δ ^ (-h'))
    (hbr : Broad ω ζ δ h ρ n N v S Z f) :
    Broad ω ζ δ h' ρ n N v S W f := by
  classical
  intro k p u r hu hdr hrρ
  let Zk (i : Fin n) : Set V := if i ∈ S ∧ f i = k then Z i else ∅
  let Wk (i : Fin n) : Set V := if i ∈ S ∧ f i = k then W i else ∅
  have hZW i : Wk i ⊆ Zk i := by
    dsimp [Wk, Zk]
    split_ifs <;> first | exact hWZ i | exact Subset.rfl
  have hmemZ (i : Fin n) (p : V) : p ∈ Zk i ↔ i ∈ S ∧ f i = k ∧ p ∈ Z i := by
    by_cases hi : i ∈ S <;> by_cases hf : f i = k <;> simp [Zk, hi, hf]
  have hmemW (i : Fin n) (p : V) : p ∈ Wk i ↔ i ∈ S ∧ f i = k ∧ p ∈ W i := by
    by_cases hi : i ∈ S <;> by_cases hf : f i = k <;> simp [Wk, hi, hf]
  have hcount : ∀ p, (∃ i, p ∈ Wk i) →
      q n {i | p ∈ Zk i} ≤ R * q n {i | p ∈ Wk i} := by
    simpa only [hmemZ, hmemW, exists_and_left] using hfrac k
  have hcap : ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ Zk i ∧ min ‖v i-u‖ ‖v i+u‖ ≤ r} ≤
        δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ Zk i} := by
    simpa only [hmemZ, and_assoc] using hbr k
  have hnew := WangZahlLot.Obl.wz_coarse_grains_assembly.broad_of_pointwise_fraction
    hδ.le hρ (by positivity : 0 ≤ δ ^ (-h)) hZW hcount hcap p u r hu hdr hrρ
  simp only [hmemW, and_assoc] at hnew
  apply hnew.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ.le) _))
    (Nat.cast_nonneg _)

/-- An arbitrary fine refinement with mass and incidence budgets gives all the
stage predicates, with the old grain boxes and their exact crossing clauses. -/
theorem shading_refine_stage_data {ω ζ δ h h' ρ a c b g m m' t R : ℝ}
    {n N L : ℕ} {x v : Fin n → V} {Y Z W : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hs : Fin L → Set V}
    {γ : Fin L → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hhh' : h ≤ h')
    (hm : 0 < m) (ht : 0 ≤ t)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hHB : HB δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hWm : ∀ i, MeasurableSet (W i)) (hWZ : ∀ i, W i ⊆ Z i)
    (hretain : O t * ∑ i, μ (Z i) ≤ ∑ i, μ (W i))
    (hbudget : δ ^ h' ≤ (t / 2) * δ ^ h)
    (hfrac : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} ≤
        R * q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i})
    (hbrbudget : R * δ ^ (-h) ≤ δ ^ (-h'))
    (hlevel : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i} ∈ Icc m' (2 * m')) :
    C δ h' n x v Y S W ρ N y w f True ∧
    Broad ω ζ δ h' ρ n N v S W f ∧
    H δ h' n x v S W ρ N y w f a c b g := by
  have hsupport : ∀ i, i ∉ S → Z i = ∅ := fun i => (hC.1 i).2.2
  have hWoff : ∀ i, i ∉ S → W i = ∅ := fun i hi =>
    subset_empty_iff.mp ((hWZ i).trans (by rw [hsupport i hi]))
  have hZm : ∀ i, MeasurableSet (Z i) := fun i => (hC.1 i).1
  have hHm : ∀ j, MeasurableSet (Hs j) := fun j => (hHB.2.2.2.2.1 j).1
  have hfib (k) : assignedFiber γ Hs k = assignedFiber f Z k := by
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_eq_supported f hsupport]
    exact hHB.2.2.2.2.2.2.1 k
  have hlevelZ : ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m := by
    intro k p hp
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_eq_supported f hsupport] at hp
    rw [← WangZahlLot.Obl.wz_clustered_cover_volume_gain.supported_fine_count f hsupport]
    exact hHB.2.2.2.2.2.2.2.2.1 k p hp
  have hgrain := refinedGrain_mass f γ hm ht hZm hWm hHm hWZ
    hHB.2.2.2.2.2.1 hfib hlevelZ hretain
  have hmassC : O (δ ^ h') * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (W i) := by
    rw [sum_supported hWoff]
    calc O (δ ^ h') * ∑ i, μ (Y i)
        ≤ (O t * O (δ ^ h)) * ∑ i, μ (Y i) := by
          apply mul_le_mul' _ le_rfl
          rw [← ENNReal.ofReal_mul ht]
          apply ENNReal.ofReal_le_ofReal
          exact hbudget.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      _ = O t * (O (δ ^ h) * ∑ i, μ (Y i)) := mul_assoc _ _ _
      _ ≤ O t * ∑ i, μ (Z i) :=
        mul_le_mul' le_rfl (hC.2.1.trans_eq (sum_supported hsupport))
      _ ≤ _ := hretain
  have hCnew : C δ h' n x v Y S W ρ N y w f True :=
    ⟨fun i => ⟨hWm i, (hWZ i).trans (hC.1 i).2.1, hWoff i⟩,
      hmassC, (cover_mono hδ hδ1 hhh' hC).2.2⟩
  refine ⟨hCnew, broad_shading_refine hδ hρ hWZ hfrac hbrbudget hbr, ?_⟩
  refine H_iff.mpr ⟨L, z, e, refinedGrain f γ Hs W, γ, m',
    HB_shading_refine hWm hWZ hsupport hHB ?_ hlevel⟩
  have ha : 0 < a := hδ.trans_le hHB.1
  have hρc : 0 < ρ * c := ha.trans_le hHB.2.1
  have hc : 0 < c := hρc.trans_le hHB.2.2.1
  calc O (δ ^ h' * L * a * (ρ * c) * c)
      ≤ O (t / 2) * O (δ ^ h * L * a * (ρ * c) * c) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        calc δ ^ h' * L * a * (ρ * c) * c
            ≤ ((t / 2) * δ ^ h) * L * a * (ρ * c) * c := by gcongr
          _ = _ := by ring
    _ ≤ O (t / 2) * ∑ j, μ (Hs j) := mul_le_mul' le_rfl hHB.2.2.2.2.2.2.2.1
    _ ≤ _ := hgrain

end WangZahlLot.Obl.wz_broad_grains_improvement
