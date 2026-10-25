-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_compact_offset_normalization.Main.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_compact_offset_normalization.Select

/-!
# The compact offset range from the bounded offset range

For `1 < |f 0| ≤ 100`, the shear-compression `shear (f 0)` carries the family to a family of
round unit tubes for the slope `f - f 0`, which vanishes at `0`, at the same scale `δ`. A
greedy selection restores the half-volume distinctness; the losses are absolute constants,
absorbed by halving the exponent `η`.
-/

namespace WangZahlLot.Obl.wz_compact_offset_normalization

open Set Metric MeasureTheory
open scoped ENNReal

/-- The constant `sa² / (M + 1)` absorbing the losses of the construction. -/
noncomputable def lossConst : ℝ := sa ^ 2 / ((degreeBound : ℝ) + 1)

theorem lossConst_pos : 0 < lossConst := by
  unfold lossConst
  have := sa_pos
  positivity

/-- Reversing the axes with negative height increment. -/
theorem flip_family {η δ : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hfam : Family η δ n x v Y) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hF : Frostman η δ n x v) :
    ∃ x' v' : Fin n → Space, Family η δ n x' v' Y ∧ (∀ i, (1 / 2 : ℝ) ≤ v' i 2) ∧
      Frostman η δ n x' v' := by
  obtain ⟨hn, hv, hball, hover, hYm, hYT, hmass⟩ := hfam
  let x' : Fin n → Space := fun i => if 0 ≤ v i 2 then x i else x i + v i
  let v' : Fin n → Space := fun i => if 0 ≤ v i 2 then v i else -v i
  have hT : ∀ i, Tube δ (x' i) (v' i) = Tube δ (x i) (v i) := by
    intro i
    simp only [x', v']
    split_ifs
    · rfl
    · exact tube_flip δ (x i) (v i)
  have hv' : ∀ i, ‖v' i‖ = 1 := by
    intro i
    simp only [v']
    split_ifs
    · exact hv i
    · rw [norm_neg]; exact hv i
  have hv'2 : ∀ i, v' i 2 = |v i 2| := by
    intro i
    simp only [v']
    split_ifs with h
    · exact (abs_of_nonneg h).symm
    · rw [PiLp.neg_apply, abs_of_neg (lt_of_not_ge h)]
  refine ⟨x', v', ⟨hn, hv', fun i => by rw [hT]; exact hball i,
    fun i j hij => by rw [hT, hT]; exact hover i j hij, hYm, fun i => by rw [hT]; exact hYT i,
    hmass⟩, fun i => by rw [hv'2]; exact htrans i, ?_⟩
  intro W hW
  have hset : {i | Tube δ (x' i) (v' i) ⊆ W} = {i | Tube δ (x i) (v i) ⊆ W} := by
    ext i
    rw [mem_ofPred_eq, mem_ofPred_eq, hT]
  rw [hset]
  exact hF W hW

open Classical in
/-- The construction of the new family. -/
theorem core {η δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10000)
    (hq : δ ^ η ≤ lossConst)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hfam : Family η δ n x v Y) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ v i 2) (hF : Frostman η δ n x v)
    {c : ℝ} (hc : |c| ≤ 100) :
    ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
      Family (2 * η) δ m x' v' Y' ∧ (∀ i, (1 / 2 : ℝ) ≤ |v' i 2|) ∧
      Frostman (2 * η) δ m x' v' ∧ (⋃ i, Y' i) ⊆ shear c '' (⋃ i, Y i) := by
  obtain ⟨hn, hv, hTball, hover, hYmeas, hYT, hmass⟩ := hfam
  have hδ100 : δ ≤ 1 / 100 := by linarith
  -- the conflict relation between the new tubes
  let T' : Fin n → Set Space := fun i => Tube δ (newBase c (x i) (v i)) (newDir c (v i))
  let R : Fin n → Fin n → Prop := fun i k => ENNReal.ofReal (δ ^ 2 / 2) < volume (T' i ∩ T' k)
  have hsymm : ∀ i k, R i k → R k i := fun i k h => by
    simpa only [R, Set.inter_comm] using h
  have hdeg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (Finset.univ.filter (R i)).card ≤ degreeBound :=
    fun i _ => conflict_degree hδ hδ1 hc x v hv hv2 hover i
  obtain ⟨S, -, hSpair, hScard, hSmass⟩ :=
    greedy_select R hsymm (fun i => volume (Y i)) degreeBound Finset.univ hdeg
  rw [Finset.card_univ, Fintype.card_fin] at hScard
  set m := S.card with hm
  let idx : Fin m → Fin n := fun j => (S.equivFin.symm j : Fin n)
  have hidx : Function.Injective idx := Subtype.val_injective.comp S.equivFin.symm.injective
  have hmemS : ∀ j, idx j ∈ S := fun j => (S.equivFin.symm j).2
  have hmn : m ≤ n := by
    have := Finset.card_le_univ S
    rwa [Fintype.card_fin] at this
  have hsum : ∀ g : Fin n → ℝ≥0∞, ∑ j : Fin m, g (idx j) = ∑ i ∈ S, g i := by
    intro g
    rw [← Finset.sum_coe_sort S g]
    exact Equiv.sum_comp S.equivFin.symm (fun i : S => g i)
  have hcoef : (δ ^ (2 * η)) = δ ^ η * δ ^ η := by
    rw [two_mul, Real.rpow_add hδ]
  have hδη : 0 < δ ^ η := Real.rpow_pos_of_pos hδ η
  have hM : (0 : ℝ) < (degreeBound : ℝ) + 1 := by positivity
  refine ⟨m, fun j => newBase c (x (idx j)) (v (idx j)), fun j => newDir c (v (idx j)),
    fun j => shear c '' Y (idx j), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- the new family is not empty
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hScard
      omega
    · exact h0
  · exact fun j => newDir_norm (hv2 _)
  · exact fun j => new_tube_subset_ball hc hδ hδ100 (hv _) (hv2 _) (hTball _)
  · -- half-volume distinctness from the absence of conflicts
    intro j j' hjj'
    have hnot := hSpair _ (hmemS j) _ (hmemS j') (hidx.ne hjj')
    have hle : volume (T' (idx j) ∩ T' (idx j')) ≤ ENNReal.ofReal (δ ^ 2 / 2) :=
      not_lt.mp hnot
    refine hle.trans ?_
    calc ENNReal.ofReal (δ ^ 2 / 2) = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (δ ^ 2) := by
          rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos
            (by norm_num)]
          norm_num
      _ ≤ (1 / 2 : ℝ≥0∞) * volume (T' (idx j)) := by
          gcongr
          exact WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hδ _ _
            (newDir_norm (hv2 _))
  · exact fun j => shear_measurableSet_image c (hYmeas _)
  · exact fun j => (image_mono (hYT _)).trans (shear_image_tube_subset_new hc δ (hv _) (hv2 _))
  · -- the shading mass
    have hvolsum : ∑ j : Fin m, volume (shear c '' Y (idx j)) =
        ENNReal.ofReal (sa ^ 2) * ∑ i ∈ S, volume (Y i) := by
      simp only [shear_volume_image]
      rw [← Finset.mul_sum]
      congr 1
      exact hsum (fun i => volume (Y i))
    rw [hvolsum]
    calc ENNReal.ofReal (δ ^ (2 * η) * (m : ℝ) * δ ^ 2)
        ≤ ENNReal.ofReal (lossConst * (δ ^ η * (n : ℝ) * δ ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hcoef]
          have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
          have h1 : δ ^ η * δ ^ η * (m : ℝ) ≤ lossConst * δ ^ η * n := by
            have := mul_le_mul hq hmn' (Nat.cast_nonneg _) lossConst_pos.le
            nlinarith
          nlinarith [sq_nonneg δ]
      _ = ENNReal.ofReal lossConst * ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) :=
          ENNReal.ofReal_mul lossConst_pos.le
      _ ≤ ENNReal.ofReal lossConst * ∑ i, volume (Y i) := by gcongr
      _ ≤ ENNReal.ofReal lossConst * (((degreeBound + 1 : ℕ) : ℝ≥0∞) * ∑ i ∈ S, volume (Y i)) := by
          gcongr
      _ = ENNReal.ofReal (sa ^ 2) * ∑ i ∈ S, volume (Y i) := by
          rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul lossConst_pos.le]
          congr 2
          rw [lossConst]
          push_cast
          field_simp
  · exact fun j => newDir_transversal hc (hv _) (hv2 _)
  · -- the convex count
    intro W hW
    have h1 : Set.ncard {j : Fin m | Tube δ (newBase c (x (idx j)) (v (idx j)))
        (newDir c (v (idx j))) ⊆ W} ≤ Set.ncard {k : Fin n | Tube δ (x k) (v k) ⊆ shear c ⁻¹' W} := by
      apply Set.ncard_le_ncard_of_injOn idx _ hidx.injOn
      intro j hj p hp
      exact hj (shear_image_tube_subset_new hc δ (hv _) (hv2 _) ⟨p, hp, rfl⟩)
    have h2 := hF (shear c ⁻¹' W) (shear_convex_preimage c hW)
    rw [shear_volume_preimage, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at h2
    refine (ENNReal.ofReal_le_ofReal (by exact_mod_cast h1)).trans (h2.trans ?_)
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    -- `δ^(-η) n / sa² ≤ δ^(-2η) m`
    have hnM : (n : ℝ) ≤ ((degreeBound : ℝ) + 1) * m := by exact_mod_cast hScard
    have hneg : δ ^ (-(2 * η)) = (δ ^ η)⁻¹ * (δ ^ η)⁻¹ := by
      rw [Real.rpow_neg hδ.le, hcoef, mul_inv]
    rw [Real.rpow_neg hδ.le, hneg]
    have hinv : lossConst⁻¹ ≤ (δ ^ η)⁻¹ := inv_anti₀ hδη hq
    have hsa : (sa ^ 2)⁻¹ * ((degreeBound : ℝ) + 1) = lossConst⁻¹ := by
      rw [lossConst, inv_div]
      field_simp
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    calc (δ ^ η)⁻¹ * (n : ℝ) * (sa ^ 2)⁻¹
        ≤ (δ ^ η)⁻¹ * (((degreeBound : ℝ) + 1) * m) * (sa ^ 2)⁻¹ := by gcongr
      _ = (δ ^ η)⁻¹ * (lossConst⁻¹ * m) := by rw [← hsa]; ring
      _ ≤ (δ ^ η)⁻¹ * ((δ ^ η)⁻¹ * m) := by gcongr
      _ = (δ ^ η)⁻¹ * (δ ^ η)⁻¹ * (m : ℝ) := by ring
  · exact iUnion_subset fun j => image_mono (subset_iUnion _ _)

/-- **The compact offset range.** The bounded offset estimate implies the estimate for
offsets `1 < |f 0| ≤ 100`. -/
theorem compact_estimate (hB : Estimate (fun c => |c| ≤ 1)) :
    Estimate (fun c => 1 < |c| ∧ |c| ≤ 100) := by
  intro ε hε
  obtain ⟨ηB, hηB, dB, hdB, hBε⟩ := hB ε hε
  set η := ηB / 2 with hηdef
  have hη : 0 < η := by positivity
  set d1 := lossConst ^ (1 / η) with hd1
  have hd1pos : 0 < d1 := Real.rpow_pos_of_pos lossConst_pos _
  refine ⟨η, hη, min (min dB d1) (1 / 10000), by positivity, ?_⟩
  intro δ hδ hδd0 hδ100 n x v Y hfam htrans hF f hf hc
  have hδdB : δ ≤ dB := hδd0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδd1 : δ ≤ d1 := hδd0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 / 10000 := hδd0.trans (min_le_right _ _)
  have hq : δ ^ η ≤ lossConst := by
    calc δ ^ η ≤ d1 ^ η := Real.rpow_le_rpow hδ.le hδd1 hη.le
      _ = lossConst := by
        rw [hd1, ← Real.rpow_mul lossConst_pos.le, one_div_mul_cancel hη.ne', Real.rpow_one]
  obtain ⟨x₁, v₁, hfam₁, hv₁, hF₁⟩ := flip_family hfam htrans hF
  obtain ⟨m, x', v', Y', hfam', htrans', hF', hsub⟩ :=
    core hδ hδ1 hq hfam₁ hv₁ hF₁ hc.2
  have h2η : 2 * η = ηB := by rw [hηdef]; ring
  rw [h2η] at hfam' hF'
  have hslope : Slope (fun z => f z - f 0) := by
    refine ⟨hf.1.sub contDiff_const, fun z hz => ?_⟩
    have hd : deriv (fun z => f z - f 0) = deriv f := funext fun w => deriv_sub_const _
    rw [hd]
    exact hf.2 z hz
  have key := hBε δ hδ hδdB hδ100 m x' v' Y' hfam' htrans' hF' (fun z => f z - f 0) hslope
    (by simp)
  calc ENNReal.ofReal (δ ^ ε) ≤ volume (Projection (fun z => f z - f 0) (⋃ i, Y' i)) := key
    _ ≤ volume (Projection (fun z => f z - f 0) (shear (f 0) '' ⋃ i, Y i)) :=
        measure_mono (image_mono hsub)
    _ = volume (planeScale '' Projection f (⋃ i, Y i)) := by rw [projection_shear]
    _ ≤ volume (Projection f (⋃ i, Y i)) := volume_planeScale_image_le _

end WangZahlLot.Obl.wz_compact_offset_normalization
