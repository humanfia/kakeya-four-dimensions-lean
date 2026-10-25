-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.WorldSupportDyadicScales, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.SnapshotDyadicScales
import Submission.Lib.K4DyadicRowScales.Basic

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set

noncomputable section

/-- The actual MK4 mesh is a member of the original coefficient grid. -/
theorem mk4_mesh_dyadic (n : ℕ) :
    Submission.Lib.K4DyadicRowScales.mesh n=dyadicParameterWidth (3*n) := by
  simp only [Submission.Lib.K4DyadicRowScales.mesh,Submission.Lib.K4DyadicRowScales.unit,
    dyadicParameterWidth,inv_pow,←pow_mul,Nat.mul_comm n 3]

/-- The dyadic support widths are resolved above the physical fine
mesh and cover every real scalar query at cost two. Their minimum
width is at least rho*zeta/2. -/
theorem exists_world_support_dyadic_scales {ρ ζ : ℝ} (hρ : 0 < ρ)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (depth : ℕ) (hdepth : parameterLevel ζ ≤ depth) :
    ∃ (W : Finset ℝ) (fineSteps columnSteps : ℝ → ℕ),
      W.card ≤ parameterLevel ζ+1 ∧
      (∀ w∈W, w=(ρ*dyadicParameterWidth depth)*(2:ℝ)^(fineSteps w)) ∧
      (∀ w∈W, ρ=w*(2:ℝ)^(columnSteps w)) ∧
      (∀ w∈W, ρ*dyadicParameterWidth depth ≤ w) ∧
      (∀ w∈W, w ≤ ρ) ∧
      (∀ w∈W, ρ*ζ/2 ≤ w) ∧
      ∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∃ w∈W, w ≤ ρ*r ∧ ρ*r ≤ 2*w := by
  classical
  let W : Finset ℝ := (Finset.range (parameterLevel ζ+1)).image (fun i => ρ*dyadicParameterWidth i)
  have hchoose (w : ℝ) (hw : w∈W) :
      ∃ i, i < parameterLevel ζ+1 ∧ ρ*dyadicParameterWidth i=w := by
    obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hw
    exact ⟨i,Finset.mem_range.mp hi,heq⟩
  let index : ℝ → ℕ := fun w => if hw : w∈W then Classical.choose (hchoose w hw) else 0
  have hindex (w : ℝ) (hw : w∈W) :
      index w ≤ parameterLevel ζ ∧ ρ*dyadicParameterWidth (index w)=w := by
    dsimp only [index]
    rw [dite_eq_left hw]
    have hh := Classical.choose_spec (hchoose w hw)
    exact ⟨by omega,hh.2⟩
  have hmul (i j : ℕ) (hij : i ≤ j) :
      dyadicParameterWidth j*(2:ℝ)^(j-i)=dyadicParameterWidth i := by
    have he : (2:ℝ)^j=(2:ℝ)^i*(2:ℝ)^(j-i) := by
      rw [←pow_add,Nat.add_sub_of_le hij]
    dsimp only [dyadicParameterWidth]
    rw [he,mul_inv_rev,mul_right_comm,inv_mul_cancel₀ (by positivity),one_mul]
  refine ⟨W,(fun w => depth-index w),index,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (Finset.card_image_le).trans (by rw [Finset.card_range])
  · intro w hw
    change w=(ρ*dyadicParameterWidth depth)*(2:ℝ)^(depth-index w)
    calc
      w=ρ*dyadicParameterWidth (index w) := (hindex w hw).2.symm
      _=(ρ*dyadicParameterWidth depth)*(2:ℝ)^(depth-index w) := by
        rw [mul_assoc,hmul _ _ ((hindex w hw).1.trans hdepth)]
  · intro w hw
    change ρ=w*(2:ℝ)^(index w)
    have hh := hmul 0 (index w) (Nat.zero_le _)
    calc
      ρ=(ρ*dyadicParameterWidth (index w))*(2:ℝ)^(index w) := by
        simpa only [Nat.sub_zero,dyadicParameterWidth,pow_zero,inv_one,mul_one,mul_assoc] using
          (congrArg (ρ*·) hh).symm
      _=w*(2:ℝ)^(index w) := congrArg (·*(2:ℝ)^(index w)) (hindex w hw).2
  · intro w hw
    rw [←(hindex w hw).2]
    exact mul_le_mul_of_nonneg_left
      (dyadicParameterWidth_antitone ((hindex w hw).1.trans hdepth)) hρ.le
  · intro w hw
    rw [←(hindex w hw).2]
    have hh : dyadicParameterWidth (index w) ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hρ.le
  · intro w hw
    rw [←(hindex w hw).2]
    have hh := (parameterLevel_width ζ hζ hζ1).1.trans
      (dyadicParameterWidth_antitone (hindex w hw).1)
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hh hρ.le
  · intro r hr hr1
    have hr0 : 0 < r := hζ.trans_le hr
    have hi : parameterLevel r < parameterLevel ζ+1 := parameterLevel_below_floor hζ hr hr1
    refine ⟨ρ*dyadicParameterWidth (parameterLevel r),
      Finset.mem_image.mpr ⟨parameterLevel r,Finset.mem_range.mpr hi,rfl⟩,?_,?_⟩
    · exact mul_le_mul_of_nonneg_left (parameterLevel_width r hr0 hr1).2 hρ.le
    · have hh := mul_le_mul_of_nonneg_left (parameterLevel_width r hr0 hr1).1 hρ.le
      nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
