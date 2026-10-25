-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CurrentOriginalRectangleCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.ResidualCaps
import Submission.Lib.K4AffineMeshCaps.Transport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalVerticalCounts

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Integrate actual pure joint-cell caps over an ordinary rectangle.
The original external velocity weight is retained, and the signal
profile is evaluated at the actual rectangle height. -/
theorem rectangle_profile_cap_of_pure_cells {Ω V : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 3 → ℝ) (signal : Ω → ℝ)
    (control : Ω → V) (v : V)
    {δ p q w C dimension : ℝ} (hδ : 0 < δ) (hw : 0 < w)
    (hδp : δ ≤ p) (hδq : δ ≤ q) (hC : 0 ≤ C)
    (weight : ENNReal)
    (hcap : ∀ (b : Fin 3 → ℤ) (j : ℤ),
      μ {z | (fun i => ⌊point z i/δ⌋)=b ∧ ⌊signal z/w⌋=j ∧ control z=v} ≤
        ENNReal.ofReal (C*δ^3*w^dimension)*weight)
    (t₀ : ℝ) (Y : Fin 2 → ℝ) (left : ℝ) :
    μ {z | point z 0∈Icc t₀ (t₀+p) ∧
      (∀ i : Fin 2, point z i.succ∈Icc (Y i) (Y i+q)) ∧
      signal z∈Icc left (left+w) ∧ control z=v} ≤
        ENNReal.ofReal (4200*C*p*q^2*w^dimension)*weight := by
  let E := {z | point z 0∈Icc t₀ (t₀+p) ∧
    (∀ i : Fin 2, point z i.succ∈Icc (Y i) (Y i+q)) ∧
    signal z∈Icc left (left+w) ∧ control z=v}
  have hbox : ∀ z∈E, point z∈
      Submission.Lib.K4MovingMeshBoxes.movingBox t₀ p Y 0 (fun _ => q) := by
    intro z hz
    refine ⟨?_,?_⟩
    · rw [abs_le]
      constructor <;> linarith [hz.1.1,hz.1.2]
    · intro i
      change |point z i.succ-(Y i+point z 0*0)| ≤ q
      rw [mul_zero,add_zero,abs_le]
      constructor <;> linarith [(hz.2.1 i).1,(hz.2.1 i).2]
  have hwindow : ∀ z∈E, |signal z-(0:ℝ)-left| ≤ w := by
    intro z hz
    rw [sub_zero,abs_le]
    constructor <;> linarith [hz.2.2.1.1,hz.2.2.1.2]
  have h := Submission.Obl.k4_wide_velocity_lists_scalar_preparation.measure_resolved_moving_slab
    μ point signal (fun _ => 0) (fun z => control z=v) E hδ hw hδp
    (by norm_num : (0:ℝ) ≤ 0) (mul_nonneg hC (Real.rpow_nonneg hw.le _))
    t₀ left Y 0 (fun _ => q) (by simp) (fun _ => hδq)
    (by intro i; simpa using hδ.le.trans hδq) hbox
    (fun z hz => hz.2.2.2) hwindow (by intro z hz y hy; simpa using hw.le) weight (by
      intro b j
      convert hcap b j using 1 <;> congr 1 <;> congr 1 <;> ring)
  convert h using 1 <;> congr 1 <;> congr 1 <;> ring

/-- The rectangle caps required by original coefficient cleanup follow
from the actual current pure cells. No fixed-time prior is assumed. -/
theorem original_rectangle_cap_of_pure_cells {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ × ℝ)) (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (c : Λ → Fin 7 → ℝ)
    {δ p q w C dimension : ℝ} (hδ : 0 < δ) (hw : 0 < w)
    (hδp : δ ≤ p) (hδq : δ ≤ q) (hC : 0 ≤ C)
    (π : (Fin 2 → ℤ) → ENNReal) (J : Fin 2 → ℤ)
    (hcap : ∀ (b : Fin 3 → ℤ) (j : ℤ),
      (μ.restrict E) {z | originalBaseCode c δ z=b ∧ ⌊zx (c z.1) z.2/w⌋=j ∧
        vbin p (c z.1)=J} ≤ ENNReal.ofReal (C*δ^3*w^dimension)*π J)
    (t₀ : ℝ) (Y : Fin 2 → ℝ) (left : ℝ) :
    μ {z | z∈E ∧ z.2∈Icc t₀ (t₀+p) ∧
      (∀ i, zy (c z.1) z.2 i∈Icc (Y i) (Y i+q)) ∧
      zx (c z.1) z.2∈Icc left (left+w) ∧ vbin p (c z.1)=J} ≤
        ENNReal.ofReal (4200*C*p*q^2*w^dimension)*π J := by
  have h := rectangle_profile_cap_of_pure_cells (μ.restrict E) (originalBaseCoordinates c)
    (fun z => zx (c z.1) z.2) (fun z => vbin p (c z.1)) J
    hδ hw hδp hδq hC (π J) hcap t₀ Y left
  rw [Measure.restrict_apply' hE] at h
  convert h using 1
  congr 1
  ext z
  simp only [mem_inter_iff,mem_ofPred_eq,originalBaseCoordinates,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two]
  constructor
  · rintro ⟨hz,ht,hy,hx,hv⟩
    refine ⟨⟨ht,?_,hx,hv⟩,hz⟩
    intro i
    fin_cases i <;> exact hy _
  · rintro ⟨⟨ht,hy,hx,hv⟩,hz⟩
    refine ⟨hz,ht,?_,hx,hv⟩
    intro i
    fin_cases i <;> exact hy _

/-- Summing bounded unit-height signal bins supplies the unchanged
original base cap used by physical-to-parameter cleanup. -/
theorem original_base_cap_of_pure_cells {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ × ℝ)) (E : Set (Λ × ℝ))
    (c : Λ → Fin 7 → ℝ) {p H C : ℝ} (hp : 0 < p) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hbound : ∀ᵐ z ∂(μ.restrict E), |zx (c z.1) z.2| ≤ H)
    (hcap : ∀ (b : Fin 3 → ℤ) (j : ℤ),
      (μ.restrict E) {z | originalBaseCode c p z=b ∧ ⌊zx (c z.1) z.2⌋=j} ≤
        ENNReal.ofReal (C*p^3)) (b : Fin 3 → ℤ) :
    (μ.restrict E) {z | originalBaseCode c p z=b} ≤
      ENNReal.ofReal ((4*H+2)*C*p^3) := by
  have hcode (z : Λ × ℝ) : Submission.Lib.K4AffineMeshCaps.baseMesh p
      (originalBaseCoordinates c z)=originalBaseCode c p z := rfl
  have h := Submission.Lib.K4AffineMeshCaps.base_cell_cap_of_bounded_signal
    (μ.restrict E) (originalBaseCoordinates c) (fun z => zx (c z.1) z.2) (fun _ => True)
    hp (by norm_num : (0:ℝ)<1) hH hC (hbound.mono (fun z hz _ => hz)) (by
      intro q j
      simpa only [div_one,and_true,hcode] using hcap q j) b
  simpa only [and_true,div_one,hcode] using h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
