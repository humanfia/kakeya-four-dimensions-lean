import Submission.Obl.k4_scalar_guarded_tangent_preparation.ScalarCells
import Submission.Obl.k4_matching_cofinal_palette_selection.PaletteBox

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

/-- Three coarse cells suffice for a finer arbitrary-offset floor cell. -/
noncomputable def coarseBins (a A : ℝ) (e : ℤ) : Finset ℤ :=
  Finset.Icc ⌊a / A * (e : ℝ)⌋ (⌊a / A * (e : ℝ)⌋ + 2)

theorem coarseBins_card (a A : ℝ) (e : ℤ) : (coarseBins a A e).card = 3 := by
  simp only [coarseBins, Int.card_Icc]
  have h : ⌊a / A * (e : ℝ)⌋ + 2 + 1 - ⌊a / A * (e : ℝ)⌋ = (3 : ℤ) := by omega
  rw [h]
  rfl

theorem floor_mem_coarseBins {a A x : ℝ} (ha : 0 < a) (hA : a ≤ A) (e : ℤ)
    (hx : (⌊x / a⌋ : ℤ) = e) : (⌊x / A⌋ : ℤ) ∈ coarseBins a A e := by
  have hA0 : 0 < A := ha.trans_le hA
  have hratio : a / A ≤ 1 := (div_le_one hA0).2 hA
  have hfloor : ⌊a / A⌋₊ ≤ 1 := by simpa using Nat.floor_mono hratio
  have h := Submission.Obl.k4_matching_cofinal_palette_selection.floor_mul_mem_Icc
    (s := x) (w := a / A) (g := a⁻¹) (div_nonneg ha.le hA0.le)
    (by simpa only [div_eq_mul_inv] using hx)
  have heq : x * (a / A) * a⁻¹ = x / A := by field_simp
  rw [heq, Finset.mem_Icc] at h
  rw [coarseBins, Finset.mem_Icc]
  refine ⟨h.1, h.2.trans ?_⟩
  have hf : (⌊a / A⌋₊ : ℤ) ≤ 1 := by exact_mod_cast hfloor
  omega

/-- A rectangular coarse-grid cap yields every finer rectangular cap,
with a universal factor 27. The untouched event P can contain any
velocity-bin restriction, so the same readout also transfers joint caps. -/
theorem rectangular_cap_from_coarse
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    (Y : Ω → Fin 2 → ℝ) (X : Ω → ℝ) (P : Set Ω)
    {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : a ≤ A) (hB : b ≤ B)
    (C : ℝ≥0∞)
    (hcap : ∀ q : Fin 2 → ℤ, ∀ c : ℤ,
      ρ (P ∩ {z | (fun i => (⌊Y z i / A⌋ : ℤ)) = q ∧ (⌊X z / B⌋ : ℤ) = c}) ≤ C)
    (q : Fin 2 → ℤ) (c : ℤ) :
    ρ (P ∩ {z | (fun i => (⌊Y z i / a⌋ : ℤ)) = q ∧ (⌊X z / b⌋ : ℤ) = c}) ≤ 27 * C := by
  classical
  let s := (coarseBins a A (q 0) ×ˢ coarseBins a A (q 1)) ×ˢ coarseBins b B c
  let cell (j : (ℤ × ℤ) × ℤ) :=
    P ∩ {z | (fun i => (⌊Y z i / A⌋ : ℤ)) = ![j.1.1, j.1.2] ∧ (⌊X z / B⌋ : ℤ) = j.2}
  have hcover : P ∩ {z | (fun i => (⌊Y z i / a⌋ : ℤ)) = q ∧ (⌊X z / b⌋ : ℤ) = c} ⊆
      ⋃ j ∈ s, cell j := by
    rintro z ⟨hzP, hzY, hzX⟩
    let j := ((⌊Y z 0 / A⌋, ⌊Y z 1 / A⌋), ⌊X z / B⌋)
    have hj : j ∈ s := by
      simp only [s, j, Finset.mem_product]
      exact ⟨⟨floor_mem_coarseBins ha hA (q 0) (congrFun hzY 0),
        floor_mem_coarseBins ha hA (q 1) (congrFun hzY 1)⟩,
        floor_mem_coarseBins hb hB c hzX⟩
    refine mem_iUnion₂.mpr ⟨j, hj, hzP, ?_, rfl⟩
    ext i
    fin_cases i <;> rfl
  have hs : s.card = 27 := by simp only [s, Finset.card_product, coarseBins_card]
  calc
    _ ≤ ρ (⋃ j ∈ s, cell j) := measure_mono hcover
    _ ≤ ∑ j ∈ s, ρ (cell j) := measure_biUnion_finset_le s cell
    _ ≤ ∑ _j ∈ s, C := Finset.sum_le_sum (fun j _ => hcap ![j.1.1, j.1.2] j.2)
    _ = _ := by simp only [Finset.sum_const, hs, nsmul_eq_mul, Nat.cast_ofNat]

end Submission.Obl.k4_scalar_guarded_tangent_preparation
