-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalDyadicPhysicalCensus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Lib.K4ClockIsotropicSupport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicOriginalPhysicalFloors

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set
open Submission.Lib.K4ParentSignalPreparation.Census

noncomputable section

/-- The actual anisotropic census of the original normalized signal
constructs the occupied physical-cell census at every tested dyadic
width. The accepted clock support bridge pays only a fixed envelope
power; the original source and its coordinates are unchanged. -/
theorem original_dyadic_physical_census {Λ : Type*}
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ)
    {ε K dimension : ℝ} (_hε : 0 < ε) (hK : 1 ≤ K)
    (hd : 0 ≤ dimension) (hd1 : dimension ≤ 1)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*p ≤ w →
        (occupied E (fun z => ![z.2,zy (c z.1) z.2 0,zy (c z.1) z.2 1])
          (fun z => zx (c z.1) z.2) p w).Finite ∧
        ((occupied E (fun z => ![z.2,zy (c z.1) z.2 0,zy (c z.1) z.2 1])
          (fun z => zx (c z.1) z.2) p w).ncard:ℝ) ≤ K/(p^3*w^dimension))
    (steps n L : ℕ) (hL : 0 < L) (hsteps : K^(100:ℕ) ≤ (2:ℝ)^steps)
    (hresolved : ε*(2:ℝ)^steps ≤ dyadicParameterWidth (n+L-1)) :
    ∀ i : Fin L,
      ((originalFineState c (dyadicParameterWidth (n+i.val))) '' E).Finite ∧
        (((originalFineState c (dyadicParameterWidth (n+i.val))) '' E).ncard:ℝ)*
          (dyadicParameterWidth (n+i.val))^((3:ℝ)+dimension) ≤ K^2*((2:ℝ)^steps)^3 := by
  intro i
  classical
  let width := dyadicParameterWidth (n+i.val)
  let fine := width/(2:ℝ)^steps
  have hwidth : 0 < width := dyadicParameterWidth_pos _
  have hwidth1 : width ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hD : 0 < (2:ℝ)^steps := by positivity
  have hD1 : 1 ≤ (2:ℝ)^steps := one_le_pow₀ (by norm_num)
  have hfine : 0 < fine := div_pos hwidth hD
  have heq : fine*(2:ℝ)^steps=width := div_mul_cancel₀ width hD.ne'
  have hεfine : ε ≤ fine := (le_div_iff₀ hD).mpr
    (hresolved.trans (dyadicParameterWidth_antitone (by omega)))
  have hfine1 : fine ≤ 1 :=
    (div_le_self hwidth.le hD1).trans hwidth1
  let base := fun z : Λ × ℝ => ![z.2,zy (c z.1) z.2 0,zy (c z.1) z.2 1]
  let signal := fun z : Λ × ℝ => zx (c z.1) z.2
  obtain ⟨F,hcard,hcover⟩ :=
    Submission.Lib.K4ClockIsotropicSupport.clock_isotropic_support_from_joint_census
      E base signal hfine hfine1 (by norm_num : (0:ℝ)<1) hK hK hd hd1 (by
        intro p w hp hp1 hw hw1 hscale
        exact hcensus p w (hεfine.trans hp) hp1 (hεfine.trans hw) hw1 (by simpa using hscale))
      steps hsteps (by rw [heq]; exact hwidth1)
  simp only [one_mul,heq] at hcover hcard
  let flatten := fun q : (Fin 3 → ℤ) × ℤ => (![q.1 0,q.2,q.1 1,q.1 2] : Fin 4 → ℤ)
  let cells := F.image flatten
  have hcover' : ∀ z∈E, originalFineState c width z∈cells := by
    intro z hz
    have h := Finset.mem_image_of_mem flatten (hcover z hz)
    convert h using 1
    funext j
    fin_cases j <;> rfl
  have hsub : originalFineState c width '' E ⊆ (cells:Set (Fin 4 → ℤ)) := by
    rintro q ⟨z,hz,rfl⟩
    exact hcover' z hz
  have hfinite := cells.finite_toSet.subset hsub
  refine ⟨hfinite,?_⟩
  calc
    _ ≤ (cells.card:ℝ)*width^((3:ℝ)+dimension) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hwidth.le _)
      exact_mod_cast Set.ncard_le_ncard hsub cells.finite_toSet
    _ ≤ (F.card:ℝ)*width^((3:ℝ)+dimension) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_image_le))
        (Real.rpow_nonneg hwidth.le _)
    _ ≤ _ := hcard

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
