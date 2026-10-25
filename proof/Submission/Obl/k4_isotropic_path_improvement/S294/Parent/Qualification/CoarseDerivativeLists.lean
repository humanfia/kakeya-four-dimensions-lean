-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CoarseDerivativeLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Basic
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomEntryFloors

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set

noncomputable section

/-- The bounded original quadratic gives inexpensive derivative lists
at the coarse prefix of the scale grid. Only smaller widths require
the parameter-floor cleanup and its incidence palettes. -/
theorem exists_coarse_derivative_lists {Λ I : Type*}
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ)
    {H cutoff : ℝ} (hH : 0 ≤ H) (hcutoff : 0 < cutoff)
    (width : I → ℝ) (hwidth : ∀ i, cutoff ≤ width i)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    (hcoeff : ∀ z∈E, |c z.1 1| ≤ H ∧ |c z.1 2| ≤ H) :
    ∃ lists : I → ((Fin 4 → ℤ) × (Fin 2 → ℤ)) → Finset ℤ,
      (∀ i key, ((lists i key).card:ℝ) ≤ 6*H/cutoff+2) ∧
      ∀ i z, z∈E →
        ⌊(c z.1 1+2*c z.1 2*z.2)/width i⌋∈
          lists i (originalFineState c (width i) z,parameterCode (width i) (zv (c z.1))) := by
  let lists := fun i : I => fun _ : (Fin 4 → ℤ) × (Fin 2 → ℤ) =>
    Finset.Icc ⌊((0:ℝ)-3*H)/width i⌋ ⌊((0:ℝ)+3*H)/width i⌋
  refine ⟨lists,?_,?_⟩
  · intro i key
    have hw : 0 < width i := hcutoff.trans_le (hwidth i)
    calc
      _ ≤ 2*(3*H)/width i+2 := card_Icc_floor_le hw (by positivity)
      _ ≤ 6*H/cutoff+2 := by
        have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ 6*H) hcutoff (hwidth i)
        calc
          _ = 6*H/width i+2 := by ring
          _ ≤ _ := add_le_add h le_rfl
  · intro i z hz
    have ht' : |z.2| ≤ 1 := by rw [abs_of_nonneg (ht z hz).1]; exact (ht z hz).2
    apply floor_mem_Icc_of_abs_le (hcutoff.trans_le (hwidth i))
    rw [sub_zero]
    calc
      _ ≤ |c z.1 1| + 2 * |c z.1 2| * |z.2| := by
        simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using
          abs_add_le (c z.1 1) (2*c z.1 2*z.2)
      _ ≤ H+2*H*1 := add_le_add (hcoeff z hz).1
        (mul_le_mul (mul_le_mul_of_nonneg_left (hcoeff z hz).2 (by norm_num)) ht'
          (abs_nonneg _) (by positivity))
      _ = 3*H := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
