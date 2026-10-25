import Submission.Obl.k4_plank_projected_multiplicity.DirectionPacking
import Submission.Obl.k4_lower_of_discrete.Localization

namespace Submission.Obl.k4_plank_projected_multiplicity

noncomputable section

abbrev E4 := EuclideanSpace ℝ (Fin 4)

def spatialPart (v : E4) : E3 := WithLp.toLp 2 ![v 1, v 2, v 3]

def projectedPart (v : E4) : E2 := WithLp.toLp 2 ![v 1, v 2]

theorem norm_projectedPart_le (v : E4) : ‖projectedPart v‖ ≤ 2 * ‖v‖ := by
  have h := Submission.Obl.k4_scalar_coefficient_clustering.plane_norm_le_abs_add (projectedPart v)
  have h₁ : |v 1| ≤ ‖v‖ := PiLp.norm_apply_le v 1
  have h₂ : |v 2| ≤ ‖v‖ := PiLp.norm_apply_le v 2
  change ‖projectedPart v‖ ≤ |v 1| + |v 2| at h
  exact h.trans (by linarith)

theorem spatialPart_norm_sub {v w : E4} (hv : v 0 = 1) (hw : w 0 = 1) :
    ‖spatialPart v - spatialPart w‖ = ‖v - w‖ := by
  have hveq : v = Submission.Obl.k4_lower_of_discrete.slopeVec (spatialPart v) := by
    ext j
    fin_cases j <;> simp [Submission.Obl.k4_lower_of_discrete.slopeVec, spatialPart, hv]
  have hweq : w = Submission.Obl.k4_lower_of_discrete.slopeVec (spatialPart w) := by
    ext j
    fin_cases j <;> simp [Submission.Obl.k4_lower_of_discrete.slopeVec, spatialPart, hw]
  conv_rhs => rw [hveq, hweq]
  exact (Submission.Obl.k4_lower_of_discrete.norm_slopeVec_sub _ _).symm

theorem planarPart_smul (a : ℝ) (v : E3) : planarPart (a • v) = a • planarPart v := by
  ext j
  fin_cases j <;> rfl

theorem planarPart_spatialPart (v : E4) : planarPart (spatialPart v) = projectedPart v := rfl

theorem scaled_family_normalized {ι : Type*} (x v : ι → E4) {L R : ℝ}
    (hLp : 0 < L) (hLx : 2 * R ≤ L) (hLv : 4 ≤ L)
    (hx : ∀ i, ‖x i‖ ≤ R) (hv : ∀ i, ‖v i‖ ≤ 2) :
    (∀ i, ‖L⁻¹ • projectedPart (x i)‖ ≤ 1 ∧
      ‖planarPart (L⁻¹ • spatialPart (v i))‖ ≤ 1) ∧
      ∀ i, |(L⁻¹ • spatialPart (v i)) 2| ≤ (1 : ℝ) := by
  have hLi : 0 < L⁻¹ := inv_pos.mpr hLp
  have hbase (i : ι) : ‖L⁻¹ • projectedPart (x i)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hLi]
    calc
      L⁻¹ * ‖projectedPart (x i)‖ ≤ L⁻¹ * L :=
        mul_le_mul_of_nonneg_left ((norm_projectedPart_le _).trans (by nlinarith [hx i])) hLi.le
      _ = 1 := inv_mul_cancel₀ hLp.ne'
  refine ⟨fun i => ⟨hbase i, ?_⟩, ?_⟩
  · rw [planarPart_smul, planarPart_spatialPart, norm_smul, Real.norm_eq_abs, abs_of_pos hLi]
    calc
      L⁻¹ * ‖projectedPart (v i)‖ ≤ L⁻¹ * L :=
        mul_le_mul_of_nonneg_left ((norm_projectedPart_le _).trans (by nlinarith [hv i])) hLi.le
      _ = 1 := inv_mul_cancel₀ hLp.ne'
  · intro i
    change |L⁻¹ * v i 3| ≤ 1
    rw [abs_mul, abs_of_pos hLi]
    have hc : |v i 3| ≤ ‖v i‖ := PiLp.norm_apply_le (v i) 3
    calc
      L⁻¹ * |v i 3| ≤ L⁻¹ * L :=
        mul_le_mul_of_nonneg_left (by linarith [hv i]) hLi.le
      _ = 1 := inv_mul_cancel₀ hLp.ne'

theorem scaled_family_separated {ι : Type*} (v : ι → E4) {L δ : ℝ} (hLp : 0 < L)
    (hv : ∀ i, v i 0 = 1) (hsep : ∀ i j, i ≠ j → δ ≤ ‖v i - v j‖) :
    ∀ i j, i ≠ j → L⁻¹ * δ ≤ ‖L⁻¹ • spatialPart (v i) - L⁻¹ • spatialPart (v j)‖ := by
  intro i j hij
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hLp),
    spatialPart_norm_sub (hv i) (hv j)]
  exact mul_le_mul_of_nonneg_left (hsep i j hij) (inv_pos.mpr hLp).le

theorem scaled_projected_proximity (x v : E4) (x' v' : E4) {L δ t : ℝ}
    (hLp : 0 < L)
    (h₁ : |(x 1 + t * v 1) - (x' 1 + t * v' 1)| ≤ δ)
    (h₂ : |(x 2 + t * v 2) - (x' 2 + t * v' 2)| ≤ δ) :
    ‖(L⁻¹ • projectedPart x + t • planarPart (L⁻¹ • spatialPart v)) -
      (L⁻¹ • projectedPart x' + t • planarPart (L⁻¹ • spatialPart v'))‖ ≤ 2 * L⁻¹ * δ := by
  let z : E2 := WithLp.toLp 2 ![(x 1 + t * v 1) - (x' 1 + t * v' 1),
    (x 2 + t * v 2) - (x' 2 + t * v' 2)]
  have heq : (L⁻¹ • projectedPart x + t • planarPart (L⁻¹ • spatialPart v)) -
      (L⁻¹ • projectedPart x' + t • planarPart (L⁻¹ • spatialPart v')) = L⁻¹ • z := by
    ext j
    fin_cases j <;> dsimp [z, projectedPart, planarPart, spatialPart] <;> ring
  have hz : ‖z‖ ≤ 2 * δ := by
    have h := Submission.Obl.k4_scalar_coefficient_clustering.plane_norm_le_abs_add z
    change ‖z‖ ≤ |(x 1 + t * v 1) - (x' 1 + t * v' 1)| +
      |(x 2 + t * v 2) - (x' 2 + t * v' 2)| at h
    linarith
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hLp)]
  calc
    L⁻¹ * ‖z‖ ≤ L⁻¹ * (2 * δ) := mul_le_mul_of_nonneg_left hz (inv_pos.mpr hLp).le
    _ = 2 * L⁻¹ * δ := by ring

end

end Submission.Obl.k4_plank_projected_multiplicity
