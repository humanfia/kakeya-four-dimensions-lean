-- From this LOT obligation o230, session x0803, commit 872bba82,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CoreCells.lean.
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreGeometry
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreWitnessPoly

/-!
# Frame cells: the cell map and the cell mass ceiling

A frame cell of side `ξ` lies in boundedly many normalized base squares of
side `ξ`, so the base-density ceiling bounds the mass of every cell.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open scoped Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set
open scoped ENNReal

/-- Normalized base coordinates about `(a, y₀)`. -/
noncomputable def coreBase (h a y₀ : ℝ) (p : Incidence) : Fin 2 → ℝ :=
  normalizedBase h ![a, y₀] p

theorem coreBase_zero (h a y₀ : ℝ) (p : Incidence) : coreBase h a y₀ p 0 = (p.2 - a) / h := by
  simp [coreBase, normalizedBase]

theorem coreBase_one (h a y₀ : ℝ) (p : Incidence) :
    coreBase h a y₀ p 1 = (scalarY p.1 p.2 - y₀) / h := by
  simp [coreBase, normalizedBase]

/-- The frame cell of an incidence. -/
noncomputable def coreCell (h a y₀ v₁ v₂ Bf ξ : ℝ) (p : Incidence) :
    Fin (gridSize Bf ξ) × Fin (gridSize Bf ξ) :=
  (gridIdx Bf ξ (frameOf v₁ v₂ (coreBase h a y₀ p) 0),
    gridIdx Bf ξ (frameOf v₁ v₂ (coreBase h a y₀ p) 1))

theorem measurable_coreBase (h a y₀ : ℝ) : Measurable (coreBase h a y₀) :=
  measurable_normalizedBase h ![a, y₀]

theorem measurable_coreCell (h a y₀ v₁ v₂ Bf ξ : ℝ) :
    Measurable (coreCell h a y₀ v₁ v₂ Bf ξ) := by
  have hf := (measurable_frameOf v₁ v₂).comp (measurable_coreBase h a y₀)
  exact ((measurable_gridIdx Bf ξ).comp ((measurable_pi_apply 0).comp hf)).prodMk
    ((measurable_gridIdx Bf ξ).comp ((measurable_pi_apply 1).comp hf))

/-- Floor bins of a coordinate in an interval of length `ℓ ≤ k ξ`. -/
theorem floor_mem_Icc_of_close {x c ξ ℓ : ℝ} (hξ : 0 < ξ) (hx : |x - c| ≤ ℓ) :
    ⌊x / ξ⌋ ∈ Finset.Icc (⌊c / ξ⌋ - ⌈ℓ / ξ⌉ - 1) (⌊c / ξ⌋ + ⌈ℓ / ξ⌉ + 1) := by
  rw [Finset.mem_Icc]
  have h1 : |x / ξ - c / ξ| ≤ ℓ / ξ := by
    rw [← sub_div, abs_div, abs_of_pos hξ]
    exact div_le_div_of_nonneg_right hx hξ.le
  have h2 := abs_le.mp h1
  have hc1 : ℓ / ξ ≤ (⌈ℓ / ξ⌉ : ℝ) := Int.le_ceil _
  have hx1 : (⌊x / ξ⌋ : ℝ) ≤ x / ξ := Int.floor_le _
  have hx2 : x / ξ < ⌊x / ξ⌋ + 1 := Int.lt_floor_add_one _
  have hc2 : (⌊c / ξ⌋ : ℝ) ≤ c / ξ := Int.floor_le _
  have hc3 : c / ξ < ⌊c / ξ⌋ + 1 := Int.lt_floor_add_one _
  constructor
  · have : ((⌊c / ξ⌋ - ⌈ℓ / ξ⌉ - 1 : ℤ) : ℝ) < ⌊x / ξ⌋ + 1 := by push_cast; linarith
    have := Int.cast_lt.mp (by exact_mod_cast this :
      ((⌊c / ξ⌋ - ⌈ℓ / ξ⌉ - 1 : ℤ) : ℝ) < ((⌊x / ξ⌋ + 1 : ℤ) : ℝ))
    omega
  · have : (⌊x / ξ⌋ : ℝ) < ((⌊c / ξ⌋ + ⌈ℓ / ξ⌉ + 1 : ℤ) : ℝ) + 1 := by push_cast; linarith
    have := Int.cast_lt.mp (by exact_mod_cast this :
      ((⌊x / ξ⌋ : ℤ) : ℝ) < ((⌊c / ξ⌋ + ⌈ℓ / ξ⌉ + 1 + 1 : ℤ) : ℝ))
    omega


/-- Frame coordinates of a point of a cell lie in that cell. -/
theorem coreCell_spec {h a y₀ v₁ v₂ Bf ξ : ℝ} (hξ : 0 < ξ) (p : Incidence)
    (hbox : ∀ i, |frameOf v₁ v₂ (coreBase h a y₀ p) i| ≤ Bf) :
    (gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ p).1 ≤ frameOf v₁ v₂ (coreBase h a y₀ p) 0 ∧
      frameOf v₁ v₂ (coreBase h a y₀ p) 0 < gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ p).1 + ξ) ∧
    (gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ p).2 ≤ frameOf v₁ v₂ (coreBase h a y₀ p) 1 ∧
      frameOf v₁ v₂ (coreBase h a y₀ p) 1 < gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ p).2 + ξ) :=
  ⟨gridIdx_spec hξ (hbox 0), gridIdx_spec hξ (hbox 1)⟩

/-- The mass ceiling of one frame cell. -/
theorem cell_cap (ρ : Measure Incidence) (S₀ A₁ : Set Incidence) (hS₀ : MeasurableSet S₀)
    (hA₁S₀ : A₁ ⊆ S₀) (h a y₀ v₁ v₂ Λ ξ Bf : ℝ) (hξ : 0 < ξ) (hΛ : 1 ≤ Λ) (hsep : v₂ ≠ v₁)
    (hv₁ : |v₁| ≤ Λ + 1) (hv₂ : |v₂| ≤ Λ + 1)
    (hbox : ∀ p ∈ A₁, ∀ i, |frameOf v₁ v₂ (coreBase h a y₀ p) i| ≤ Bf)
    (hbase : ∀ c : Fin 2 → ℤ, ρ.restrict S₀
      {p | ∀ e, ⌊normalizedBase h ![a, y₀] p e / ξ⌋ = c e} ≤ ENNReal.ofReal (Λ * ξ ^ 2) * ρ S₀)
    (hfin : ρ S₀ ≠ ⊤) (c : Fin (gridSize Bf ξ) × Fin (gridSize Bf ξ)) :
    ρ (A₁ ∩ {p | coreCell h a y₀ v₁ v₂ Bf ξ p = c}) ≤
      ENNReal.ofReal (5 * (4 * Λ + 9) * (Λ * ξ ^ 2) * (ρ S₀).toReal) := by
  classical
  set g₀ := gridPos Bf ξ c.1
  set g₁ := gridPos Bf ξ c.2
  set c₀ : ℝ := g₀ + g₁ + ξ
  set c₁ : ℝ := v₁ * g₀ + v₂ * g₁
  set ℓ₁ : ℝ := 2 * (Λ + 1) * ξ
  set I : Finset (ℤ × ℤ) :=
    Finset.Icc (⌊c₀ / ξ⌋ - ⌈ξ / ξ⌉ - 1) (⌊c₀ / ξ⌋ + ⌈ξ / ξ⌉ + 1) ×ˢ
      Finset.Icc (⌊c₁ / ξ⌋ - ⌈ℓ₁ / ξ⌉ - 1) (⌊c₁ / ξ⌋ + ⌈ℓ₁ / ξ⌉ + 1)
  set T : ℤ × ℤ → Set Incidence := fun kj =>
    {p | ∀ e, ⌊normalizedBase h ![a, y₀] p e / ξ⌋ = (![kj.1, kj.2] : Fin 2 → ℤ) e}
  have hsub : A₁ ∩ {p | coreCell h a y₀ v₁ v₂ Bf ξ p = c} ⊆ ⋃ kj ∈ I, (S₀ ∩ T kj) := by
    rintro p ⟨hpA, hpc⟩
    have hspec := coreCell_spec (h := h) (a := a) (y₀ := y₀) (v₁ := v₁) (v₂ := v₂) hξ p
      (hbox p hpA)
    rw [show coreCell h a y₀ v₁ v₂ Bf ξ p = c from hpc] at hspec
    obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩ := hspec
    set u := coreBase h a y₀ p
    have ht := frameOf_time hsep u
    have hs := frameOf_space hsep u
    have hτ : |u 0 - c₀| ≤ ξ := by
      rw [abs_le]; constructor <;> linarith
    have hη : |u 1 - c₁| ≤ ℓ₁ := by
      have e : u 1 - c₁ = v₁ * (frameOf v₁ v₂ u 0 - g₀) + v₂ * (frameOf v₁ v₂ u 1 - g₁) := by
        rw [← hs]; ring
      rw [e]
      have hd0 : |frameOf v₁ v₂ u 0 - g₀| ≤ ξ := by rw [abs_le]; constructor <;> linarith
      have hd1 : |frameOf v₁ v₂ u 1 - g₁| ≤ ξ := by rw [abs_le]; constructor <;> linarith
      calc _ ≤ |v₁ * (frameOf v₁ v₂ u 0 - g₀)| + |v₂ * (frameOf v₁ v₂ u 1 - g₁)| :=
            abs_add_le _ _
        _ = |v₁| * |frameOf v₁ v₂ u 0 - g₀| + |v₂| * |frameOf v₁ v₂ u 1 - g₁| := by
            rw [abs_mul, abs_mul]
        _ ≤ (Λ + 1) * ξ + (Λ + 1) * ξ := by
            have hΛ1 : 0 ≤ Λ + 1 := by linarith
            gcongr
        _ = ℓ₁ := by ring
    have hk := floor_mem_Icc_of_close hξ hτ
    have hj := floor_mem_Icc_of_close hξ hη
    simp only [mem_iUnion, exists_prop]
    refine ⟨(⌊u 0 / ξ⌋, ⌊u 1 / ξ⌋), Finset.mem_product.mpr ⟨hk, hj⟩, hA₁S₀ hpA, ?_⟩
    intro e
    fin_cases e <;> rfl
  have hTm : ∀ kj, MeasurableSet (T kj) := by
    intro kj
    have hfl : Measurable fun p : Incidence => fun e => ⌊normalizedBase h ![a, y₀] p e / ξ⌋ := by
      apply measurable_pi_lambda
      intro e
      exact Int.measurable_floor.comp
        (((measurable_pi_apply e).comp (measurable_normalizedBase h ![a, y₀])).div_const ξ)
    have : T kj = (fun p : Incidence => fun e => ⌊normalizedBase h ![a, y₀] p e / ξ⌋) ⁻¹'
        {(![kj.1, kj.2] : Fin 2 → ℤ)} := by
      ext p
      simp only [T, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
      exact ⟨fun hp => funext hp, fun hp e => congrFun hp e⟩
    rw [this]
    exact hfl (measurableSet_singleton _)
  have hcard : ((I.card : ℕ) : ℝ) ≤ 5 * (4 * Λ + 9) := by
    rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
    have hξξ : ⌈ξ / ξ⌉ = 1 := by rw [div_self hξ.ne']; simp
    rw [hξξ]
    have hℓ : ℓ₁ / ξ = 2 * (Λ + 1) := by simp only [ℓ₁]; field_simp
    rw [hℓ]
    have hcl : (⌈2 * (Λ + 1)⌉ : ℝ) < 2 * (Λ + 1) + 1 := Int.ceil_lt_add_one _
    have hc0 : (0 : ℤ) ≤ ⌈2 * (Λ + 1)⌉ := Int.ceil_nonneg (by linarith)
    have e1 : (⌊c₀ / ξ⌋ + 1 + 1 + 1 - (⌊c₀ / ξ⌋ - 1 - 1)).toNat = 5 := by omega
    have e2 : ((⌊c₁ / ξ⌋ + ⌈2 * (Λ + 1)⌉ + 1 + 1 - (⌊c₁ / ξ⌋ - ⌈2 * (Λ + 1)⌉ - 1)).toNat : ℝ) =
        2 * (⌈2 * (Λ + 1)⌉ : ℝ) + 3 := by
      have : (⌊c₁ / ξ⌋ + ⌈2 * (Λ + 1)⌉ + 1 + 1 - (⌊c₁ / ξ⌋ - ⌈2 * (Λ + 1)⌉ - 1)) =
          2 * ⌈2 * (Λ + 1)⌉ + 3 := by ring
      rw [this]
      have h3 : (0 : ℤ) ≤ 2 * ⌈2 * (Λ + 1)⌉ + 3 := by omega
      rw [show (((2 * ⌈2 * (Λ + 1)⌉ + 3).toNat : ℕ) : ℝ) = ((2 * ⌈2 * (Λ + 1)⌉ + 3 : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg h3]
      push_cast; ring
    rw [Nat.cast_mul, e1, e2]
    push_cast
    nlinarith
  calc ρ (A₁ ∩ {p | coreCell h a y₀ v₁ v₂ Bf ξ p = c})
      ≤ ρ (⋃ kj ∈ I, (S₀ ∩ T kj)) := measure_mono hsub
    _ ≤ ∑ kj ∈ I, ρ (S₀ ∩ T kj) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _kj ∈ I, ENNReal.ofReal (Λ * ξ ^ 2) * ρ S₀ := by
        apply Finset.sum_le_sum
        intro kj _
        have h1 := hbase ![kj.1, kj.2]
        rw [Measure.restrict_apply (hTm kj)] at h1
        rw [inter_comm]
        exact h1
    _ = (I.card : ℝ≥0∞) * (ENNReal.ofReal (Λ * ξ ^ 2) * ρ S₀) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal ((I.card : ℝ) * (Λ * ξ ^ 2) * (ρ S₀).toReal) := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (I.card : ℝ) * (Λ * ξ ^ 2) by positivity),
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ (I.card : ℝ) by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hfin, mul_assoc]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
        apply mul_le_mul_of_nonneg_right hcard (by positivity)

end Submission.Obl.k4_scalar_grid_cartesian_field
