-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CurrentOriginalFloorCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CurrentOriginalRectangleCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- The accepted bounded-signal base cap preserves a finite external
weight. This changes only its real-valued coefficient, never the measure. -/
theorem weighted_base_cap_of_bounded_signal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 3 → ℝ) (signal : Ω → ℝ) (condition : Ω → Prop)
    {δ a H C : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (weight : ENNReal) (hweight : weight≠∞)
    (hbound : ∀ᵐ z ∂μ, condition z → |signal z| ≤ H)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {z | (fun i => ⌊point z i/δ⌋)=q ∧ ⌊signal z/a⌋=j ∧ condition z} ≤
        ENNReal.ofReal (C*δ^3)*weight) (q : Fin 3 → ℤ) :
    μ {z | (fun i => ⌊point z i/δ⌋)=q ∧ condition z} ≤
      ENNReal.ofReal ((4*H/a+2)*C*δ^3)*weight := by
  have hC' : 0 ≤ C*weight.toReal := mul_nonneg hC ENNReal.toReal_nonneg
  have hnormalize (B : ℝ) (hB : 0 ≤ B) :
      ENNReal.ofReal (B*weight.toReal)=ENNReal.ofReal B*weight := by
    rw [ENNReal.ofReal_mul hB,ENNReal.ofReal_toReal hweight]
  have h := Submission.Lib.K4AffineMeshCaps.base_cell_cap_of_bounded_signal
    μ point signal condition hδ ha hH hC' hbound (by
      intro b j
      have he : ENNReal.ofReal ((C*weight.toReal)*δ^3)=ENNReal.ofReal (C*δ^3)*weight := by
        rw [show (C*weight.toReal)*δ^3=(C*δ^3)*weight.toReal by ring]
        exact hnormalize _ (by positivity)
      rw [he]
      exact hcap b j) q
  apply h.trans_eq
  rw [show (4*H/a+2)*(C*weight.toReal)*δ^3=((4*H/a+2)*C*δ^3)*weight.toReal by ring]
  exact hnormalize _ (by positivity)

/-- The accepted moving-box integration also keeps the finite external
weight, including the zero-weight case. -/
theorem weighted_box_cap_of_base_caps {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
    {δ p q C : ℝ} (hδ : 0 < δ) (hδp : δ ≤ p) (hδq : δ ≤ q) (hC : 0 ≤ C)
    (weight : ENNReal) (hweight : weight≠∞)
    (hcap : ∀ b : Fin 3 → ℤ,
      μ {z | (fun i => ⌊point z i/δ⌋)=b ∧ condition z} ≤
        ENNReal.ofReal (C*δ^3)*weight)
    (t₀ : ℝ) (Y : Fin 2 → ℝ) :
    μ {z | point z∈Submission.Lib.K4MovingMeshBoxes.movingBox t₀ p Y 0 (fun _ => q) ∧
      condition z} ≤ ENNReal.ofReal (600*C*p*q^2)*weight := by
  have hnormalize (B : ℝ) (hB : 0 ≤ B) :
      ENNReal.ofReal (B*weight.toReal)=ENNReal.ofReal B*weight := by
    rw [ENNReal.ofReal_mul hB,ENNReal.ofReal_toReal hweight]
  have h := Submission.Lib.K4MovingMeshBoxes.measure_movingBox_of_cell_cap
    μ point condition hδ hδp (by norm_num : (0:ℝ) ≤ 0)
    (mul_nonneg hC ENNReal.toReal_nonneg) t₀ Y 0 (fun _ => q) (by simp)
    (fun _ => hδq) (by intro i; simpa using hδ.le.trans hδq) (by
      intro b
      have he : ENNReal.ofReal ((C*weight.toReal)*δ^3)=ENNReal.ofReal (C*δ^3)*weight := by
        rw [show (C*weight.toReal)*δ^3=(C*δ^3)*weight.toReal by ring]
        exact hnormalize _ (by positivity)
      rw [he]
      exact hcap b)
  apply h.trans_eq
  change ENNReal.ofReal (600*(C*weight.toReal)*p*q*q)=_
  rw [show 600*(C*weight.toReal)*p*q*q=(600*C*p*q^2)*weight.toReal by ring]
  exact hnormalize _ (by have := hδ.le.trans hδp; positivity)

/-- Caps only at resolved heights up to one imply ALL rectangle caps
required by scalar cleanup. Bounded signal controls larger heights by
summing unit-height bins; the same original external weight survives. -/
theorem all_height_rectangle_caps_of_pure_cells {Ω V : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 3 → ℝ) (signal : Ω → ℝ)
    (control : Ω → V) (v : V)
    {δ p H C dimension : ℝ} (hδ : 0 < δ) (hδp : δ ≤ p) (hp1 : p ≤ 1)
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hd : 0 ≤ dimension)
    (weight : ENNReal) (hweight : weight≠∞)
    (hbound : ∀ᵐ z ∂μ, |signal z| ≤ H)
    (hcap : ∀ w : ℝ, p ≤ w → w ≤ 1 → ∀ (b : Fin 3 → ℤ) (j : ℤ),
      μ {z | (fun i => ⌊point z i/δ⌋)=b ∧ ⌊signal z/w⌋=j ∧ control z=v} ≤
        ENNReal.ofReal (C*δ^3*w^dimension)*weight) :
    ∀ (t₀ : ℝ) (Y : Fin 2 → ℝ) (left q w : ℝ), p ≤ q → p ≤ w →
      μ {z | point z 0∈Icc t₀ (t₀+p) ∧
        (∀ i : Fin 2, point z i.succ∈Icc (Y i) (Y i+q)) ∧
        signal z∈Icc left (left+w) ∧ control z=v} ≤
          ENNReal.ofReal ((4200*(4*H+3)*C)*p*q^2*w^dimension)*weight := by
  intro t₀ Y left q w hpq hpw
  have hp : 0 < p := hδ.trans_le hδp
  have hq : 0 < q := hp.trans_le hpq
  have hw : 0 < w := hp.trans_le hpw
  have hδq : δ ≤ q := hδp.trans hpq
  by_cases hw1 : w ≤ 1
  · apply (rectangle_profile_cap_of_pure_cells μ point signal control v hδ hw hδp hδq
      hC weight (hcap w hpw hw1) t₀ Y left).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hmult : 0 ≤ p*q^2*w^dimension := by positivity
    have hconst : 4200*C ≤ 4200*(4*H+3)*C := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hconst hmult]
  · have hw1' : 1 ≤ w := le_of_lt (lt_of_not_ge hw1)
    have hpow : 1 ≤ w^dimension := Real.one_le_rpow hw1' hd
    have hbase : ∀ b : Fin 3 → ℤ,
        μ {z | (fun i => ⌊point z i/δ⌋)=b ∧ control z=v} ≤
          ENNReal.ofReal (((4*H+2)*C)*δ^3)*weight := by
      intro b
      simpa only [div_one] using weighted_base_cap_of_bounded_signal μ point signal
        (fun z => control z=v) hδ (by norm_num : (0:ℝ)<1) hH hC weight hweight
        (hbound.mono (fun z hz _ => hz))
        (by intro b j; simpa only [Real.one_rpow,mul_one,div_one] using hcap 1 hp1 le_rfl b j) b
    have hbox := weighted_box_cap_of_base_caps μ point (fun z => control z=v) hδ hδp hδq
      (mul_nonneg (by positivity) hC) weight hweight hbase t₀ Y
    apply le_trans (b:=μ {z | point z∈
      Submission.Lib.K4MovingMeshBoxes.movingBox t₀ p Y 0 (fun _ => q) ∧ control z=v}) ?_
      (hbox.trans ?_)
    · apply measure_mono
      intro z hz
      refine ⟨⟨?_,?_⟩,hz.2.2.2⟩
      · rw [abs_le]
        constructor <;> linarith [hz.1.1,hz.1.2]
      · intro i
        change |point z i.succ-(Y i+point z 0*0)| ≤ q
        rw [mul_zero,add_zero,abs_le]
        constructor <;> linarith [(hz.2.1 i).1,(hz.2.1 i).2]
    · apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have hconst : 600*((4*H+2)*C) ≤ 4200*(4*H+3)*C := by nlinarith
      have hnonneg : 0 ≤ 4200*(4*H+3)*C*p*q^2 := by positivity
      calc
        _ ≤ 4200*(4*H+3)*C*p*q^2 := by nlinarith [mul_le_mul_of_nonneg_right hconst (by positivity : 0 ≤ p*q^2)]
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hpow hnonneg]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
