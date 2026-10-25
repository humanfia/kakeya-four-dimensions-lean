/- Adapted from this LOT tree, obligation o218, session x0764 (integrating x0760),
   commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8, ParameterJointCaps.lean. -/
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.NativeGroupBand
import Submission.Obl.k4_subcritical_endpoint_native_pairing.PhysicalBase
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set MeasureTheory

/-- The original physical joint ceilings give the static parameter ceilings
used in matching. The velocity palette is unchanged, and all hypotheses on
the retained law are only almost everywhere. -/
theorem static_parameter_joint_cap {α β : Type*} [MeasurableSpace α]
    (μ ρ : Measure (α × ℝ)) (hρ : ρ ≤ μ) (b : α → Fin 6 → ℝ)
    (velocity : α × ℝ → β) (v₀ : β) (palette : ENNReal)
    {δ δm w H C d vc : ℝ}
    (hδ : 0 < δ) (hδm : 0 < δm) (hw : 0 < w) (hH : 1 ≤ H)
    (hC : 0 ≤ C) (hsmall : 3 * H * δ ≤ δm) (hmesh : 3 * δ ≤ w)
    (hδmH : δm ≤ H) (hvc : |vc| ≤ H)
    (hgood : ∀ᵐ z ∂ρ, z.2 ∈ Icc (0 : ℝ) 1 ∧ |b z.1 0| ≤ H ∧
      |b z.1 3 - vc| ≤ δm ∧ |b z.1 4 + b z.1 0| ≤ δm ∧ velocity z = v₀)
    (hcap : ∀ (c : Fin 3 → ℤ) (j : ℤ),
      μ {z | (fun i => ⌊parameterPhysicalBase b z i / δ⌋) = c ∧
        ⌊(b z.1 2 + z.2 * b z.1 5) / w⌋ = j ∧ velocity z = v₀} ≤
          ENNReal.ofReal (C * δ ^ 3 * w ^ d) * palette)
    (c : Fin 3 → ℤ) (j : ℤ) :
    ρ {z | (fun i => ⌊(![z.2, b z.1 0, b z.1 1] : Fin 3 → ℝ) i / δm⌋) = c ∧
      ⌊(b z.1 2 + z.2 * b z.1 5) / w⌋ = j} ≤
        ENNReal.ofReal (4320 * C * H * δm ^ 3 * w ^ d) * palette := by
  classical
  let E : Set (α × ℝ) := {z |
    (fun i => ⌊(![z.2, b z.1 0, b z.1 1] : Fin 3 → ℝ) i / δm⌋) = c ∧
      ⌊(b z.1 2 + z.2 * b z.1 5) / w⌋ = j}
  let G : Set (α × ℝ) := {z | z.2 ∈ Icc (0 : ℝ) 1 ∧ |b z.1 0| ≤ H ∧
    |b z.1 3 - vc| ≤ δm ∧ |b z.1 4 + b z.1 0| ≤ δm ∧ velocity z = v₀}
  have hmass : ρ E = ρ (E ∩ G) := by
    apply measure_congr
    filter_upwards [hgood] with z hz
    exact propext (by simp only [mem_inter_iff]; exact ⟨fun he => ⟨he, hz⟩, And.left⟩)
  have hfloor {x s : ℝ} (hs : 0 < s) {n : ℤ} (hn : ⌊x / s⌋ = n) :
      |x - s * n| ≤ s := by
    simpa only [hn] using
      Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hs x
  have hbase (z : α × ℝ) (hz : z ∈ E ∩ G) :
      |z.2 - δm * c 0| ≤ δm ∧ |b z.1 0 - δm * c 1| ≤ δm ∧
        |b z.1 1 - δm * c 2| ≤ δm := by
    have h := congrFun hz.1.1
    exact ⟨hfloor hδm (by simpa using h 0), hfloor hδm (by simpa using h 1),
      hfloor hδm (by simpa using h 2)⟩
  rcases (E ∩ G).eq_empty_or_nonempty with hEmpty | ⟨z₀, hz₀⟩
  · change ρ E ≤ _
    rw [hmass, hEmpty, measure_empty]
    exact zero_le
  have hpc : |δm * (c 1 : ℝ)| ≤ 3 * H := by
    calc
      _ ≤ |b z₀.1 0 - δm * (c 1 : ℝ)| + |b z₀.1 0| := by
        simpa only [sub_zero, abs_sub_comm] using abs_sub_le (δm * (c 1 : ℝ)) (b z₀.1 0) 0
      _ ≤ δm + H := add_le_add (hbase z₀ hz₀).2.1 hz₀.2.2.1
      _ ≤ _ := by linarith
  have hδδm : δ ≤ δm := by nlinarith [mul_nonneg (sub_nonneg.mpr hH) hδ.le]
  have hband (z : α × ℝ) (hz : z ∈ E ∩ G) :
      |b z.1 2 + z.2 * b z.1 5 - w * j - z.2 * 0| ≤ 3 * w := by
    simpa only [mul_zero, sub_zero] using
      (hfloor hw hz.1.2).trans (by linarith : w ≤ 3 * w)
  have Hcap :=
    Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.original_native_affine_group_band_cap
      μ (E ∩ G) (fun z => b z.1) Prod.snd
      (fun z => if velocity z = v₀ then (0 : ℤ) else 1) 0
      δ w δm δm (3 * H) (δm * c 0) C d (w * j) 0 palette
      ![δm * c 1, δm * c 2, vc]
      hδ hw (by linarith) hC hδδm hsmall hmesh
      (by simpa using hpc) (by simpa using hvc.trans (by linarith : H ≤ 3 * H))
      (by simp; linarith)
      (fun z hz => ?_) (fun z hz => ?_)
      (fun z hz => (hbase z hz).2.1) (fun z hz => (hbase z hz).2.2)
      (fun z hz => hz.2.2.2.1) (fun z hz => hz.2.2.2.2.1)
      hband (fun z hz => by simp only [hz.2.2.2.2.2, ↓reduceIte]) (fun q n => ?_)
  · change ρ E ≤ _
    calc
      ρ E = ρ (E ∩ G) := hmass
      _ ≤ μ (E ∩ G) := hρ _
      _ ≤ _ := by convert Hcap using 1 <;> congr 2 <;> ring
  · have h := abs_le.mp (hbase z hz).1
    have hlo := (le_div_iff₀ hδm).mp (Int.floor_le (z.2 / δm))
    have heq := congrFun hz.1.1 0
    simp only [Matrix.cons_val_zero] at heq
    rw [heq] at hlo
    exact ⟨by linarith, by linarith [h.2]⟩
  · exact abs_le.mpr ⟨by linarith [hz.2.1.1], hz.2.1.2⟩
  · have heq : {z : α × ℝ |
        (fun e => ⌊Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.nativeHorizontalPoint
          (b z.1) z.2 e / δ⌋) = q ∧
          ⌊(b z.1 2 + z.2 * b z.1 5) / w⌋ = n ∧
          (if velocity z = v₀ then (0 : ℤ) else 1) = 0} =
        {z | (fun i => ⌊parameterPhysicalBase b z i / δ⌋) = q ∧
          ⌊(b z.1 2 + z.2 * b z.1 5) / w⌋ = n ∧ velocity z = v₀} := by
      ext z
      simp only [parameterPhysicalBase,
        Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.nativeHorizontalPoint]
      by_cases hv : velocity z = v₀ <;> simp [hv]
    rw [heq]
    exact hcap q n

end Submission.Obl.k4_subcritical_endpoint_native_pairing
