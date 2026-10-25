-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_cell_weighted_cover.Assembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Global

/-!
# Assembly of the weighted tube cover

Helper lemmas for the final assembly of `WangZahlLot.wz_transverse_cell_weighted_cover`:

* `asm_exists_delta`: the choice of `δ₀` for `r = s / 16`, written through `u = δ ^ (s / 16)`
  (so `δ ^ s = u ^ 16` and `log (1 / δ) = (16 / s) (- log u) ≤ (16 / s) / u`);
* `asm_density_arith`: `δ ^ s (4 b) ^ 2` is below the bound of `cell_density`, because
  `log (b / a) ≤ 100 log (1 / δ)`;
* `asm_coverage`, `asm_cell_count`, `asm_slab`: the counting inequalities, from `net_cover`'s
  fraction `netConst` and `δ ^ s ≤ netConst · δ ^ (s / 16)`;
* `asm_transport`: the Jacobian-weighted volume transport, from the disjointness of the images
  of the shadings of distinct cells.
-/

namespace WangZahlLot.Obl.wz_transverse_cell_weighted_cover

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

theorem asm_netConst_le_one : netConst ≤ 1 := by
  unfold netConst
  rw [div_le_one (by positivity)]
  norm_num

/-- The power-log inequality behind the density bound, in terms of `u = δ ^ (s / 16)` and
`L = - log u`. -/
theorem asm_poly {u L s Cd : ℝ} (hs : 0 < s) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (huL : u * L ≤ 1) (huK : (16 + 25600 / s) * u ≤ Cd) :
    16 * u ^ 16 * (1 + 100 * (16 / s * L)) ≤ Cd * u ^ 8 := by
  have h1 : 16 * u ^ 16 * (1 + 100 * (16 / s * L)) =
      16 * u ^ 16 + 25600 / s * u ^ 15 * (u * L) := by
    field_simp
    ring
  have h2 : u ^ 16 ≤ u ^ 9 := pow_le_pow_of_le_one hu0.le hu1 (by norm_num)
  have h3 : u ^ 15 ≤ u ^ 9 := pow_le_pow_of_le_one hu0.le hu1 (by norm_num)
  have hs' : 0 ≤ 25600 / s := by positivity
  have h4 : 25600 / s * u ^ 15 * (u * L) ≤ 25600 / s * u ^ 9 := by
    have h5 : 0 ≤ 25600 / s * u ^ 15 := by positivity
    calc 25600 / s * u ^ 15 * (u * L) ≤ 25600 / s * u ^ 15 * 1 :=
          mul_le_mul_of_nonneg_left huL h5
      _ = 25600 / s * u ^ 15 := mul_one _
      _ ≤ 25600 / s * u ^ 9 := mul_le_mul_of_nonneg_left h3 hs'
  have h8 : 0 ≤ u ^ 8 := by positivity
  calc 16 * u ^ 16 * (1 + 100 * (16 / s * L)) =
        16 * u ^ 16 + 25600 / s * u ^ 15 * (u * L) := h1
    _ ≤ 16 * u ^ 9 + 25600 / s * u ^ 9 := by linarith
    _ = ((16 + 25600 / s) * u) * u ^ 8 := by ring
    _ ≤ Cd * u ^ 8 := mul_le_mul_of_nonneg_right huK h8

/-- The choice of `δ₀` (with `r = s / 16`). -/
theorem asm_exists_delta {s Cd : ℝ} (hs : 0 < s) (hCd : 0 < Cd) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      0 < δ ^ (s / 16) ∧ δ ^ (s / 16) ≤ 1 ∧ 0 < δ ^ s ∧ δ ^ s ≤ δ ^ (s / 16) ∧
      δ ^ s ≤ netConst * δ ^ (s / 16) ∧
      16 * δ ^ s * (1 + 100 * Real.log (1 / δ)) ≤ Cd * (δ ^ (s / 16)) ^ 8 := by
  set K : ℝ := min netConst (Cd / (16 + 25600 / s)) with hK
  have hK0 : 0 < K := lt_min netConst_pos (by positivity)
  refine ⟨min (1 / 100) (K ^ (16 / s)), lt_min (by norm_num) (Real.rpow_pos_of_pos hK0 _),
    min_le_left _ _, ?_⟩
  intro δ hδ hδ₀
  have hδ1 : δ ≤ 1 := hδ₀.trans ((min_le_left _ _).trans (by norm_num))
  set u := δ ^ (s / 16) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hδ _
  have hu1 : u ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have huK : u ≤ K := by
    calc u = δ ^ (s / 16) := rfl
      _ ≤ (K ^ (16 / s)) ^ (s / 16) :=
          Real.rpow_le_rpow hδ.le (hδ₀.trans (min_le_right _ _)) (by positivity)
      _ = K := by
          rw [← Real.rpow_mul hK0.le]
          have : 16 / s * (s / 16) = 1 := by field_simp
          rw [this, Real.rpow_one]
  have hds : δ ^ s = u ^ 16 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    push_cast
    ring
  have hlog : Real.log (1 / δ) = 16 / s * (-Real.log u) := by
    rw [hu, Real.log_rpow hδ, one_div, Real.log_inv]
    field_simp
  have huL : u * (-Real.log u) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hu0)
    rw [Real.log_inv] at h
    have h' : u * (-Real.log u) ≤ u * (u⁻¹ - 1) := mul_le_mul_of_nonneg_left h hu0.le
    rw [mul_sub, mul_inv_cancel₀ hu0.ne', mul_one] at h'
    linarith
  refine ⟨hu0, hu1, by rw [hds]; positivity, ?_, ?_, ?_⟩
  · rw [hds]
    exact pow_le_of_le_one hu0.le hu1 (by norm_num)
  · rw [hds]
    have h15 : u ^ 15 ≤ u := pow_le_of_le_one hu0.le hu1 (by norm_num)
    have hKn : u ≤ netConst := huK.trans (min_le_left _ _)
    calc u ^ 16 = u ^ 15 * u := by ring
      _ ≤ netConst * u := mul_le_mul_of_nonneg_right (h15.trans hKn) hu0.le
  · rw [hds, hlog]
    apply asm_poly hs hu0 hu1 huL
    have h1 : u ≤ Cd / (16 + 25600 / s) := huK.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith

/-- The density arithmetic: the output density `δ ^ s (4 b) ^ 2` is dominated by the bound of
`cell_density`. -/
theorem asm_density_arith {δ s r a b Cd : ℝ} (hδ : 0 < δ) (ha : δ ^ (100 : ℕ) ≤ a)
    (hab : a ≤ b) (hb1 : b ≤ 1)
    (hA2 : 16 * δ ^ s * (1 + 100 * Real.log (1 / δ)) ≤ Cd * (δ ^ r) ^ 8) :
    δ ^ s * (4 * b) ^ 2 ≤ Cd * (δ ^ r) ^ 8 * b ^ 2 / (1 + Real.log (b / a)) := by
  have hδ100 : 0 < δ ^ (100 : ℕ) := pow_pos hδ 100
  have ha0 : 0 < a := lt_of_lt_of_le hδ100 ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hlog0 : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha0).mpr hab)
  have hlog : Real.log (b / a) ≤ 100 * Real.log (1 / δ) := by
    have h1 : b / a ≤ (1 / δ) ^ (100 : ℕ) := by
      rw [div_pow, one_pow, div_le_div_iff₀ ha0 hδ100]
      have : b * δ ^ (100 : ℕ) ≤ 1 * δ ^ (100 : ℕ) := mul_le_mul_of_nonneg_right hb1 hδ100.le
      linarith
    calc Real.log (b / a) ≤ Real.log ((1 / δ) ^ (100 : ℕ)) :=
          Real.log_le_log (div_pos hb0 ha0) h1
      _ = 100 * Real.log (1 / δ) := by rw [Real.log_pow]; norm_num
  rw [le_div_iff₀ (by linarith)]
  have hds : 0 ≤ δ ^ s := (Real.rpow_pos_of_pos hδ s).le
  have hb2 : 0 ≤ b ^ 2 := by positivity
  calc δ ^ s * (4 * b) ^ 2 * (1 + Real.log (b / a)) ≤
        δ ^ s * (4 * b) ^ 2 * (1 + 100 * Real.log (1 / δ)) := by gcongr
    _ = (16 * δ ^ s * (1 + 100 * Real.log (1 / δ))) * b ^ 2 := by ring
    _ ≤ (Cd * (δ ^ r) ^ 8) * b ^ 2 := mul_le_mul_of_nonneg_right hA2 hb2

/-- The centre of a prism lies in it. -/
theorem asm_center_mem {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (c : Space) (u : Fin 3 → Space) :
    c ∈ prism a b c u := by
  simp only [prism, mem_ofPred_eq, sub_self, inner_zero_right, abs_zero]
  exact ⟨ha, hb, by norm_num⟩

/-- A prism inside `B(0, 1/100)` has its centre inside it. -/
theorem asm_norm_lt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {c : Space} {u : Fin 3 → Space}
    (hP : prism a b c u ⊆ ball (0 : Space) (1 / 100)) : ‖c‖ < 1 / 100 := by
  have h := hP (asm_center_mem ha hb c u)
  rwa [mem_ball_zero_iff] at h

/-- Per-cell counting: `h' · #I ≤ h · ∑ #F`. -/
theorem asm_cell_count {h h' Ic Fc : ℝ} (hh : 0 ≤ h) (hIc : 0 ≤ Ic)
    (hA1 : h' ≤ netConst * h) (hnet : netConst * Ic ≤ Fc) : h' * Ic ≤ h * Fc := by
  calc h' * Ic ≤ netConst * h * Ic := mul_le_mul_of_nonneg_right hA1 hIc
    _ = h * (netConst * Ic) := by ring
    _ ≤ h * Fc := mul_le_mul_of_nonneg_left hnet hh

/-- The coverage inequality. -/
theorem asm_coverage {m n : ℕ} {M : Fin m → ℕ} (I : Fin m → Finset (Fin n))
    (F : (j : Fin m) → Fin (M j) → Finset (Fin n)) {h h' : ℝ}
    (hA1 : h' ≤ netConst * h) (hcov : h * (n : ℝ) ≤ ∑ j, ((I j).card : ℝ))
    (hnet : ∀ j, netConst * ((I j).card : ℝ) ≤ ∑ α, ((F j α).card : ℝ)) :
    h' * (n : ℝ) ≤ ∑ j, ∑ α, ((F j α).card : ℝ) := by
  calc h' * (n : ℝ) ≤ netConst * h * n := mul_le_mul_of_nonneg_right hA1 (Nat.cast_nonneg n)
    _ = netConst * (h * n) := by ring
    _ ≤ netConst * ∑ j, ((I j).card : ℝ) := mul_le_mul_of_nonneg_left hcov netConst_pos.le
    _ = ∑ j, netConst * ((I j).card : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ∑ j, ∑ α, ((F j α).card : ℝ) := Finset.sum_le_sum (fun j _ => hnet j)

/-- The slab inequality for one cell. -/
theorem asm_slab {n M : ℕ} (I : Finset (Fin n)) (F : Fin M → Finset (Fin n))
    (Pr : Fin n → Set Space) (Tu : Fin M → Set Space) (S : Set Space) {h h' : ℝ}
    (hh : 0 < h) (hh' : 0 < h') (hF : ∀ α, F α ⊆ I) (hPT : ∀ α, ∀ i ∈ F α, Pr i ⊆ Tu α)
    (hcard : h' * (I.card : ℝ) ≤ h * ∑ α, ((F α).card : ℝ))
    (hC : ENNReal.ofReal (Set.ncard {i : Fin n | i ∈ I ∧ Pr i ⊆ S} : ℝ) ≤
      ENNReal.ofReal (h⁻¹ * (I.card : ℝ)) * volume S) :
    ENNReal.ofReal (Set.ncard {i : Fin n | ∃ α, i ∈ F α ∧ Tu α ⊆ S} : ℝ) ≤
      ENNReal.ofReal (h'⁻¹ * ∑ α, ((F α).card : ℝ)) * volume S := by
  have hsub : {i : Fin n | ∃ α, i ∈ F α ∧ Tu α ⊆ S} ⊆ {i : Fin n | i ∈ I ∧ Pr i ⊆ S} := by
    rintro i ⟨α, hiF, hT⟩
    exact ⟨hF α hiF, (hPT α i hiF).trans hT⟩
  have hnc : (Set.ncard {i : Fin n | ∃ α, i ∈ F α ∧ Tu α ⊆ S} : ℝ) ≤
      Set.ncard {i : Fin n | i ∈ I ∧ Pr i ⊆ S} := by
    exact_mod_cast Set.ncard_le_ncard hsub
  have hcoef : h⁻¹ * (I.card : ℝ) ≤ h'⁻¹ * ∑ α, ((F α).card : ℝ) := by
    rw [← div_eq_inv_mul, ← div_eq_inv_mul, div_le_div_iff₀ hh hh']
    calc (I.card : ℝ) * h' = h' * I.card := mul_comm _ _
      _ ≤ h * ∑ α, ((F α).card : ℝ) := hcard
      _ = (∑ α, ((F α).card : ℝ)) * h := mul_comm _ _
  calc ENNReal.ofReal (Set.ncard {i : Fin n | ∃ α, i ∈ F α ∧ Tu α ⊆ S} : ℝ) ≤
        ENNReal.ofReal (Set.ncard {i : Fin n | i ∈ I ∧ Pr i ⊆ S} : ℝ) :=
        ENNReal.ofReal_le_ofReal hnc
    _ ≤ ENNReal.ofReal (h⁻¹ * (I.card : ℝ)) * volume S := hC
    _ ≤ ENNReal.ofReal (h'⁻¹ * ∑ α, ((F α).card : ℝ)) * volume S := by
        gcongr

/-- Images of measurable sets under affine equivalences are measurable. -/
theorem asm_measurableSet_image (f : Space ≃ᵃ[ℝ] Space) {S : Set Space}
    (hS : MeasurableSet S) : MeasurableSet (f '' S) := by
  rw [← AffineEquiv.preimage_symm]
  exact f.symm.continuous_of_finiteDimensional.measurable hS

/-- The volume transport inequality. -/
theorem asm_transport {m n : ℕ} (I : Fin m → Finset (Fin n)) (f : Fin m → Space ≃ᵃ[ℝ] Space)
    (D : Fin m → ℝ) (H : Fin m → Fin n → Set Space) (Y : Fin n → Set Space)
    {M : Fin m → ℕ} (Z : (j : Fin m) → Fin (M j) → Set Space)
    (hvol : ∀ j (Q : Set Space), volume (f j '' Q) = ENNReal.ofReal (D j) * volume Q)
    (hZm : ∀ j α, MeasurableSet (Z j α))
    (hZH : ∀ j α, Z j α ⊆ ⋃ i ∈ I j, H j i)
    (hHY : ∀ j, ∀ i ∈ I j, H j i ⊆ f j ⁻¹' (Y i))
    (hdisj : ∀ j j', j ≠ j' →
      Disjoint (f j '' (⋃ i ∈ I j, H j i)) (f j' '' (⋃ i ∈ I j', H j' i))) :
    ∑ j, ENNReal.ofReal (D j) * volume (⋃ α, Z j α) ≤ volume (⋃ i, Y i) := by
  have hmeas : ∀ j ∈ (Finset.univ : Finset (Fin m)), MeasurableSet (f j '' ⋃ α, Z j α) :=
    fun j _ => asm_measurableSet_image (f j) (MeasurableSet.iUnion fun α => hZm j α)
  have hsubH : ∀ j, f j '' (⋃ α, Z j α) ⊆ f j '' (⋃ i ∈ I j, H j i) :=
    fun j => image_mono (iUnion_subset fun α => hZH j α)
  have hpd : PairwiseDisjoint (↑(Finset.univ : Finset (Fin m)))
      (fun j => f j '' ⋃ α, Z j α) := by
    intro j _ j' _ hjj'
    exact (hdisj j j' hjj').mono (hsubH j) (hsubH j')
  calc ∑ j, ENNReal.ofReal (D j) * volume (⋃ α, Z j α) = ∑ j, volume (f j '' ⋃ α, Z j α) :=
        Finset.sum_congr rfl (fun j _ => (hvol j _).symm)
    _ = volume (⋃ j ∈ (Finset.univ : Finset (Fin m)), f j '' ⋃ α, Z j α) :=
        (measure_biUnion_finset hpd hmeas).symm
    _ ≤ volume (⋃ i, Y i) := by
        apply measure_mono
        intro p hp
        simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_image] at hp
        obtain ⟨j, q, ⟨α, hq⟩, rfl⟩ := hp
        have hq' := hZH j α hq
        simp only [mem_iUnion] at hq'
        obtain ⟨i, hi, hqi⟩ := hq'
        exact mem_iUnion.mpr ⟨i, hHY j i hi hqi⟩

end

end WangZahlLot.Obl.wz_transverse_cell_weighted_cover
