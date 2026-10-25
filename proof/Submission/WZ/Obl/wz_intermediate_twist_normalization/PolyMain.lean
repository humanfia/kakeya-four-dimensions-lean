-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.PolyMain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.PolySelect
import Submission.WZ.Obl.wz_compact_offset_normalization.Main

/-!
# Offsets of polynomial size from the bounded offset range

For an offset `c = f 0`, the shear-compression `pshear c` carries the family to a family of
round unit tubes for the slope `f - c`, which vanishes at `0`, at the same scale `δ`. A
greedy selection restores the half-volume distinctness. All losses are bounded by a power of
`1 + |c|`: the shading mass loses `psa c ^ 2 / (pdegreeBound c + 1) ≥ 1 / (3·10⁴⁶ (1 + |c|)⁶)`
and so does the convex count. When `|c| ≤ δ^(-κ)` with `κ = η_B / 24`, these losses are
absorbed by halving the exponent `η_B` of the bounded offset estimate.

This proves the projection estimate of `wz_intermediate_twist_normalization` (and of the whole
large offset reduction) from the bounded offset estimate whenever `|f 0| ≤ δ^(-κ(ε))`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_compact_offset_normalization (Space Tube Family Frostman Slope
  Projection Estimate flip_family greedy_select)

/-- The constant `psa c ² / (M + 1)` absorbing the losses of the construction. -/
noncomputable def plossConst (c : ℝ) : ℝ := psa c ^ 2 / ((pdegreeBound c : ℝ) + 1)

theorem plossConst_pos (c : ℝ) : 0 < plossConst c := by
  unfold plossConst
  have := psa_pos c
  positivity

open Classical in
/-- The construction of the new family, for an arbitrary offset `c`. -/
theorem pcore {η δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10000) {c : ℝ}
    (hq : δ ^ η ≤ plossConst c)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hfam : Family η δ n x v Y) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ v i 2) (hF : Frostman η δ n x v) :
    ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
      Family (2 * η) δ m x' v' Y' ∧ (∀ i, (1 / 2 : ℝ) ≤ |v' i 2|) ∧
      Frostman (2 * η) δ m x' v' ∧ (⋃ i, Y' i) ⊆ pshear c '' (⋃ i, Y i) := by
  obtain ⟨hn, hv, hTball, hover, hYmeas, hYT, hmass⟩ := hfam
  have hδ100 : δ ≤ 1 / 100 := by linarith
  -- the conflict relation between the new tubes
  let T' : Fin n → Set Space := fun i => Tube δ (pnewBase c (x i) (v i)) (pnewDir c (v i))
  let R : Fin n → Fin n → Prop := fun i k => ENNReal.ofReal (δ ^ 2 / 2) < volume (T' i ∩ T' k)
  have hsymm : ∀ i k, R i k → R k i := fun i k h => by
    simpa only [R, Set.inter_comm] using h
  have hdeg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (Finset.univ.filter (R i)).card ≤ pdegreeBound c :=
    fun i _ => pconflict_degree hδ hδ1 c x v hv hv2 hover i
  obtain ⟨S, -, hSpair, hScard, hSmass⟩ :=
    greedy_select R hsymm (fun i => volume (Y i)) (pdegreeBound c) Finset.univ hdeg
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
  have hM : (0 : ℝ) < (pdegreeBound c : ℝ) + 1 := by positivity
  refine ⟨m, fun j => pnewBase c (x (idx j)) (v (idx j)), fun j => pnewDir c (v (idx j)),
    fun j => pshear c '' Y (idx j), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- the new family is not empty
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hScard
      omega
    · exact h0
  · exact fun j => pnewDir_norm (hv2 _)
  · exact fun j => pnew_tube_subset_ball c hδ hδ100 (hv _) (hv2 _) (hTball _)
  · -- half-volume distinctness from the absence of conflicts
    intro j j' hjj'
    have hnot := hSpair _ (hmemS j) _ (hmemS j') (hidx.ne hjj')
    have hle : volume (T' (idx j) ∩ T' (idx j')) ≤ ENNReal.ofReal (δ ^ 2 / 2) :=
      not_lt.mp hnot
    refine hle.trans ?_
    calc ENNReal.ofReal (δ ^ 2 / 2) = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (δ ^ 2) := by
          rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
      _ ≤ (1 / 2 : ℝ≥0∞) * volume (T' (idx j)) := by
          gcongr
          exact WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hδ _ _
            (pnewDir_norm (hv2 _))
  · exact fun j => pshear_measurableSet_image c (hYmeas _)
  · exact fun j => (image_mono (hYT _)).trans
      (pshear_image_tube_subset_new c δ (hv _) (hv2 _))
  · -- the shading mass
    have hvolsum : ∑ j : Fin m, volume (pshear c '' Y (idx j)) =
        ENNReal.ofReal (psa c ^ 2) * ∑ i ∈ S, volume (Y i) := by
      simp only [pshear_volume_image]
      rw [← Finset.mul_sum]
      congr 1
      exact hsum (fun i => volume (Y i))
    rw [hvolsum]
    calc ENNReal.ofReal (δ ^ (2 * η) * (m : ℝ) * δ ^ 2)
        ≤ ENNReal.ofReal (plossConst c * (δ ^ η * (n : ℝ) * δ ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hcoef]
          have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
          have h1 : δ ^ η * δ ^ η * (m : ℝ) ≤ plossConst c * δ ^ η * n := by
            have := mul_le_mul hq hmn' (Nat.cast_nonneg _) (plossConst_pos c).le
            nlinarith
          nlinarith [sq_nonneg δ]
      _ = ENNReal.ofReal (plossConst c) * ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) :=
          ENNReal.ofReal_mul (plossConst_pos c).le
      _ ≤ ENNReal.ofReal (plossConst c) * ∑ i, volume (Y i) := by gcongr
      _ ≤ ENNReal.ofReal (plossConst c) *
            (((pdegreeBound c + 1 : ℕ) : ℝ≥0∞) * ∑ i ∈ S, volume (Y i)) := by
          gcongr
      _ = ENNReal.ofReal (psa c ^ 2) * ∑ i ∈ S, volume (Y i) := by
          rw [← mul_assoc, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (plossConst_pos c).le]
          congr 2
          rw [plossConst]
          push_cast
          field_simp
  · exact fun j => pnewDir_transversal (hv _) (hv2 _)
  · -- the convex count
    intro W hW
    have h1 : Set.ncard {j : Fin m | Tube δ (pnewBase c (x (idx j)) (v (idx j)))
        (pnewDir c (v (idx j))) ⊆ W} ≤
        Set.ncard {k : Fin n | Tube δ (x k) (v k) ⊆ pshear c ⁻¹' W} := by
      apply Set.ncard_le_ncard_of_injOn idx _ hidx.injOn
      intro j hj p hp
      exact hj (pshear_image_tube_subset_new c δ (hv _) (hv2 _) ⟨p, hp, rfl⟩)
    have h2 := hF (pshear c ⁻¹' W) (pshear_convex_preimage c hW)
    rw [pshear_volume_preimage, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at h2
    refine (ENNReal.ofReal_le_ofReal (by exact_mod_cast h1)).trans (h2.trans ?_)
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    -- `δ^(-η) n / psa² ≤ δ^(-2η) m`
    have hnM : (n : ℝ) ≤ ((pdegreeBound c : ℝ) + 1) * m := by exact_mod_cast hScard
    have hneg : δ ^ (-(2 * η)) = (δ ^ η)⁻¹ * (δ ^ η)⁻¹ := by
      rw [Real.rpow_neg hδ.le, hcoef, mul_inv]
    rw [Real.rpow_neg hδ.le, hneg]
    have hinv : (plossConst c)⁻¹ ≤ (δ ^ η)⁻¹ := inv_anti₀ hδη hq
    have hsa : (psa c ^ 2)⁻¹ * ((pdegreeBound c : ℝ) + 1) = (plossConst c)⁻¹ := by
      rw [plossConst, inv_div]
      have := psa_pos c
      field_simp
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    calc (δ ^ η)⁻¹ * (n : ℝ) * (psa c ^ 2)⁻¹
        ≤ (δ ^ η)⁻¹ * (((pdegreeBound c : ℝ) + 1) * m) * (psa c ^ 2)⁻¹ := by gcongr
      _ = (δ ^ η)⁻¹ * ((plossConst c)⁻¹ * m) := by rw [← hsa]; ring
      _ ≤ (δ ^ η)⁻¹ * ((δ ^ η)⁻¹ * m) := by gcongr
      _ = (δ ^ η)⁻¹ * (δ ^ η)⁻¹ * (m : ℝ) := by ring
  · exact iUnion_subset fun j => image_mono (subset_iUnion _ _)

/-- The loss constant is at least a power of `δ` when `|c| ≤ δ^(-κ)`. -/
theorem plossConst_ge {c δ κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 ≤ κ)
    (hc : |c| ≤ δ ^ (-κ)) : δ ^ (6 * κ) / (2 * 10 ^ 48) ≤ plossConst c := by
  set m := 1 + |c| with hmdef
  have hm1 : 1 ≤ m := by have := abs_nonneg c; linarith
  have hm0 : 0 < m := by linarith
  have hD1 : 1 ≤ δ ^ (-κ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hmD : m ≤ 2 * δ ^ (-κ) := by linarith
  have hm6 : m ^ 6 ≤ 64 * δ ^ (-(6 * κ)) := by
    have h1 : m ^ 6 ≤ (2 * δ ^ (-κ)) ^ 6 := pow_le_pow_left₀ hm0.le hmD 6
    have h2 : (δ ^ (-κ)) ^ 6 = δ ^ (-(6 * κ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      congr 1
      push_cast
      ring
    calc m ^ 6 ≤ (2 * δ ^ (-κ)) ^ 6 := h1
      _ = 64 * (δ ^ (-κ)) ^ 6 := by ring
      _ = 64 * δ ^ (-(6 * κ)) := by rw [h2]
  have hdeg : (pdegreeBound c : ℝ) + 1 ≤ 3 * 10 ^ 40 * m ^ 4 := by
    have h1 := pdegreeBound_le c
    have h2 : 1 ≤ m ^ 4 := one_le_pow₀ hm1
    nlinarith
  have hpsa : psa c ^ 2 = 1 / (10 ^ 6 * m ^ 2) := by
    rw [← inv_inv (psa c ^ 2), psa_sq_inv, one_div]
  have hloss : 1 / (3 * 10 ^ 46 * m ^ 6) ≤ plossConst c := by
    rw [plossConst, hpsa]
    have hpos : (0 : ℝ) < (pdegreeBound c : ℝ) + 1 := by positivity
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    nlinarith [pow_pos hm0 2]
  have hneg : δ ^ (-(6 * κ)) * δ ^ (6 * κ) = 1 := by
    rw [← Real.rpow_add hδ]
    simp
  have hpos6 : 0 < δ ^ (6 * κ) := Real.rpow_pos_of_pos hδ _
  refine le_trans ?_ hloss
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc δ ^ (6 * κ) * (3 * 10 ^ 46 * m ^ 6)
      ≤ δ ^ (6 * κ) * (3 * 10 ^ 46 * (64 * δ ^ (-(6 * κ)))) := by gcongr
    _ = 192 * 10 ^ 46 * (δ ^ (-(6 * κ)) * δ ^ (6 * κ)) := by ring
    _ = 192 * 10 ^ 46 := by rw [hneg, mul_one]
    _ ≤ 2 * 10 ^ 48 := by norm_num

/-- **Offsets of polynomial size.** The bounded offset estimate implies the projection
estimate for all offsets `|f 0| ≤ δ^(-κ)`, for some `κ > 0` depending on `ε`. -/
theorem poly_estimate (hB : Estimate (fun c => |c| ≤ 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
      Frostman η δ n x v → ∀ f : ℝ → ℝ, Slope f → |f 0| ≤ δ ^ (-κ) →
      ENNReal.ofReal (δ ^ ε) ≤ volume (Projection f (⋃ i, Y i)) := by
  intro ε hε
  obtain ⟨ηB, hηB, dB, hdB, hBε⟩ := hB ε hε
  set κ := ηB / 24 with hκdef
  set η := ηB / 2 with hηdef
  have hκ : 0 < κ := by positivity
  have hη : 0 < η := by positivity
  set d1 := (1 / (2 * 10 ^ 48) : ℝ) ^ (4 / ηB) with hd1
  have hd1pos : 0 < d1 := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨κ, hκ, η, hη, min (min dB d1) (1 / 10000), by positivity, ?_⟩
  intro δ hδ hδd0 hδ100 n x v Y hfam htrans hF f hf hc
  have hδdB : δ ≤ dB := hδd0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδd1 : δ ≤ d1 := hδd0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 / 10000 := hδd0.trans (min_le_right _ _)
  -- the loss is absorbed
  have hq : δ ^ η ≤ plossConst (f 0) := by
    have h1 := plossConst_ge hδ (by linarith) hκ.le hc
    have h6 : 6 * κ = ηB / 4 := by rw [hκdef]; ring
    have h2 : δ ^ (ηB / 4) ≤ 1 / (2 * 10 ^ 48) := by
      calc δ ^ (ηB / 4) ≤ d1 ^ (ηB / 4) := Real.rpow_le_rpow hδ.le hδd1 (by positivity)
        _ = 1 / (2 * 10 ^ 48) := by
          rw [hd1, ← Real.rpow_mul (by norm_num)]
          have : 4 / ηB * (ηB / 4) = 1 := by field_simp
          rw [this, Real.rpow_one]
    have h3 : δ ^ η = δ ^ (ηB / 4) * δ ^ (6 * κ) := by
      rw [← Real.rpow_add hδ, h6, hηdef]
      congr 1
      ring
    have hpos : 0 ≤ δ ^ (6 * κ) := (Real.rpow_pos_of_pos hδ _).le
    calc δ ^ η = δ ^ (ηB / 4) * δ ^ (6 * κ) := h3
      _ ≤ 1 / (2 * 10 ^ 48) * δ ^ (6 * κ) := mul_le_mul_of_nonneg_right h2 hpos
      _ = δ ^ (6 * κ) / (2 * 10 ^ 48) := by ring
      _ ≤ plossConst (f 0) := h1
  obtain ⟨x₁, v₁, hfam₁, hv₁, hF₁⟩ := flip_family hfam htrans hF
  obtain ⟨m, x', v', Y', hfam', htrans', hF', hsub⟩ :=
    pcore hδ hδ1 hq hfam₁ hv₁ hF₁
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
    _ ≤ volume (Projection (fun z => f z - f 0) (pshear (f 0) '' ⋃ i, Y i)) :=
        measure_mono (image_mono hsub)
    _ = volume (pplaneScale (f 0) '' Projection f (⋃ i, Y i)) := by rw [projection_pshear]
    _ ≤ volume (Projection f (⋃ i, Y i)) := volume_pplaneScale_image_le _ _

end WangZahlLot.Obl.wz_intermediate_twist_normalization
