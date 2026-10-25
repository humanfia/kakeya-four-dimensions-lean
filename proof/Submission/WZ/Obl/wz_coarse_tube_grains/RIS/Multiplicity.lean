-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Multiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.Arithmetic

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The multiplicity of a finite measurable shading. -/
noncomputable def multiplicity {n : ℕ} (Y : Fin n → Set Space) (p : Space) : ENNReal :=
  ∑ i, (Y i).indicator (fun _ => 1) p

/-- Agreement between the indicator sum and the finite set cardinality convention. -/
theorem multiplicity_eq_ncard {n : ℕ} (Y : Fin n → Set Space) (p : Space) :
    multiplicity Y p = ({i : Fin n | p ∈ Y i}.ncard : ENNReal) := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  simp [multiplicity, Set.indicator, Finset.sum_boole]

/-- Integrating a pointwise multiplicity estimate bounds the total shading mass. -/
theorem mass_le_multiplicity_mul_volume {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) {M : ENNReal}
    (hM : ∀ p, multiplicity Y p ≤ M) :
    ∑ i, volume (Y i) ≤ M * volume (⋃ i, Y i) := by
  classical
  have hU : MeasurableSet (⋃ i, Y i) := MeasurableSet.iUnion hY
  calc
    ∑ i, volume (Y i) = ∫⁻ p, multiplicity Y p := by
      change ∑ i, volume (Y i) = ∫⁻ p, ∑ i, (Y i).indicator (fun _ => 1) p
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_indicator_const (hY i), one_mul]
      · intro i _
        exact measurable_const.indicator (hY i)
    _ ≤ ∫⁻ p, (⋃ i, Y i).indicator (fun _ => M) p := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ ⋃ i, Y i
      · simpa only [Set.indicator_of_mem hp] using hM p
      · have hnone : ∀ i, p ∉ Y i := fun i hi => hp (Set.mem_iUnion.mpr ⟨i, hi⟩)
        simp [multiplicity, Set.indicator_of_notMem, hp, hnone]
    _ = M * volume (⋃ i, Y i) := lintegral_indicator_const hU M

/-- The division step converting multiplicity into a lower volume bound. -/
theorem volume_lower_of_multiplicity {δ η σ ω g C : ℝ}
    (hδ : 0 < δ) (hC : 0 < C) {n : ℕ} (hn : 0 < n)
    {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i))
    (hdense : Dense δ η Y)
    (hmult : ∀ p, multiplicity Y p ≤
      ENNReal.ofReal (C * δ ^ (-ω + g) * ((n : ℝ) * δ) ^ σ)) :
    ENNReal.ofReal (C⁻¹ * δ ^ (ω + η - g) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
      volume (⋃ i, Y i) := by
  have hnδ : 0 < (n : ℝ) * δ := mul_pos (Nat.cast_pos.mpr hn) hδ
  let M := C * δ ^ (-ω + g) * ((n : ℝ) * δ) ^ σ
  have hM : 0 < M := by positivity
  have hcancel :
      M * (C⁻¹ * δ ^ (ω + η - g) * (n * δ ^ 2) * (n * δ) ^ (-σ)) =
      δ ^ η * n * δ ^ 2 := by
    calc
      _ = (C⁻¹ * C) * (δ ^ (ω + η - g) * δ ^ (-ω + g)) *
          ((n : ℝ) * δ ^ 2) * (((n : ℝ) * δ) ^ (-σ) * ((n : ℝ) * δ) ^ σ) := by
        dsimp [M]
        ring
      _ = δ ^ η * n * δ ^ 2 := by
        rw [inv_mul_cancel₀ hC.ne', ← Real.rpow_add hδ, Real.rpow_neg hnδ.le,
          inv_mul_cancel₀ (Real.rpow_pos_of_pos hnδ σ).ne', one_mul, mul_one]
        rw [show ω + η - g + (-ω + g) = η by ring]
        ring
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hM).ne'
    ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal M *
        ENNReal.ofReal (C⁻¹ * δ ^ (ω + η - g) * (n * δ ^ 2) * (n * δ) ^ (-σ)) =
        ENNReal.ofReal (δ ^ η * n * δ ^ 2) := by
      rw [← ENNReal.ofReal_mul hM.le, hcancel]
    _ ≤ ∑ i, volume (Y i) := hdense
    _ ≤ ENNReal.ofReal M * volume (⋃ i, Y i) := mass_le_multiplicity_mul_volume hY hmult

/-- Cancellation of the fine, intermediate, and coarse scale factors in WZ (9.10). -/
theorem three_scale_product {δ ρ r n N : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hr : 0 < r) (hn : 0 < n) (hN : 0 < N) (σ ω : ℝ) :
    ((δ / ρ) ^ (-ω) * (n / N * δ * ρ / r ^ 2) ^ σ) *
      ((ρ / r) ^ (-ω - σ)) * (r ^ (-ω) * (N * r) ^ σ) =
      δ ^ (-ω) * (n * δ) ^ σ := by
  have hδρ : 0 < δ / ρ := div_pos hδ hρ
  have hρr : 0 < ρ / r := div_pos hρ hr
  have hq : 0 < n / N * δ * ρ / r ^ 2 := by positivity
  rw [sub_eq_add_neg (-ω) σ, Real.rpow_add hρr, Real.rpow_neg hρr.le σ]
  calc
    _ = (((δ / ρ) ^ (-ω) * (ρ / r) ^ (-ω)) * r ^ (-ω)) *
        (((n / N * δ * ρ / r ^ 2) ^ σ / (ρ / r) ^ σ) * (N * r) ^ σ) := by ring
    _ = (((δ / ρ) * (ρ / r)) * r) ^ (-ω) *
        (((n / N * δ * ρ / r ^ 2) / (ρ / r)) * (N * r)) ^ σ := by
      rw [Real.mul_rpow (mul_nonneg hδρ.le hρr.le) hr.le,
        Real.mul_rpow hδρ.le hρr.le,
        Real.mul_rpow (div_nonneg hq.le hρr.le) (mul_nonneg hN.le hr.le),
        Real.div_rpow hq.le hρr.le]
    _ = _ := by
      have heq₁ : δ / ρ * (ρ / r) * r = δ := by field_simp
      have heq₂ : n / N * δ * ρ / r ^ 2 / (ρ / r) * (N * r) = n * δ := by field_simp
      rw [heq₁, heq₂]

/-- Keeping a δ^b fraction of the mass adds b to the density exponent. -/
theorem density_of_retained_mass {δ η b : ℝ} (hδ : 0 < δ) {n : ℕ}
    {Y Z : Fin n → Set Space} (hY : Dense δ η Y)
    (hmass : ENNReal.ofReal (δ ^ b) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i)) :
    Dense δ (η + b) Z := by
  calc
    ENNReal.ofReal (δ ^ (η + b) * n * δ ^ 2) =
        ENNReal.ofReal (δ ^ b) * ENNReal.ofReal (δ ^ η * n * δ ^ 2) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.rpow_add hδ]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (δ ^ b) * ∑ i, volume (Y i) := mul_le_mul_right hY _
    _ ≤ ∑ i, volume (Z i) := hmass

/-- A multiplicity gain on a mass-preserving refinement yields alternative (A). -/
theorem first_alternative_of_refined_multiplicity {δ η b σ ω g α C : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 < C)
    (hgain : η + b + α ≤ g) {n : ℕ} (hn : 0 < n)
    {Y Z : Fin n → Set Space} (hZ : ∀ i, MeasurableSet (Z i))
    (hZY : ∀ i, Z i ⊆ Y i) (hdense : Dense δ η Y)
    (hmass : ENNReal.ofReal (δ ^ b) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i))
    (hmult : ∀ p, multiplicity Z p ≤
      ENNReal.ofReal (C * δ ^ (-ω + g) * ((n : ℝ) * δ) ^ σ)) :
    ENNReal.ofReal (C⁻¹ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
      volume (⋃ i, Y i) := by
  have hZdense := density_of_retained_mass hδ hdense hmass
  have hbound := volume_lower_of_multiplicity hδ hC hn hZ hZdense hmult
  have hp : δ ^ (ω - α) ≤ δ ^ (ω + (η + b) - g) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hcompare :
      ENNReal.ofReal (C⁻¹ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
      ENNReal.ofReal (C⁻¹ * δ ^ (ω + (η + b) - g) * (n * δ ^ 2) *
        (n * δ) ^ (-σ)) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hC.le)) (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  exact hcompare.trans (hbound.trans (measure_mono (Set.iUnion_mono hZY)))

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
