/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/FiniteTrueLift.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftFit
import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftFormats
import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftBounds

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

open MeasureTheory

namespace Remainder

variable {p q : Data} {r h w : ℝ} (rem : Remainder p q r h w)

/-- A finite true child system lifts to a finite true original system with a
format exponent independent of slack tolerance and of its horizon. -/
theorem liftAtlas_trueAt (hp : p.Valid) (hr : 0 ≤ r) (hrL : r < p.L)
    {k M D : ℕ} {a : Atlas q k} (ha : a.TrueAt M D q.L) (hκ : 1 ≤ a.κ) :
    (rem.liftAtlas k a).TrueAt (rem.liftingExponent M) (max rem.D D) p.L := by
  have hN2 : 2 ≤ p.N (rem.φ k) := hp.1 _
  have hN1 : 1 ≤ p.N (rem.φ k) := le_trans (by norm_num) hN2
  have hM : M ≤ rem.liftingExponent M := by dsimp [liftingExponent]; omega
  have hpM : rem.M ≤ rem.liftingExponent M := by
    dsimp [liftingExponent, parameterExponent]
    omega
  have hpowM : p.N (rem.φ k) ^ M ≤ p.N (rem.φ k) ^ rem.liftingExponent M :=
    pow_le_pow_right₀ hN1 hM
  have hpowpM : p.N (rem.φ k) ^ rem.M ≤ p.N (rem.φ k) ^ rem.liftingExponent M :=
    pow_le_pow_right₀ hN1 hpM
  have hsum : p.N (rem.φ k) ^ rem.M + p.N (rem.φ k) ^ M ≤
      p.N (rem.φ k) ^ rem.liftingExponent M := by
    apply (sum_powers_le hN2 rem.M M).trans
    apply pow_le_pow_right₀ hN1
    dsimp [liftingExponent, parameterExponent]
    omega
  refine ⟨?_, rem.liftAtlas_separated ha.2.1, ?_, rem.liftAtlas_coverage hp ha hκ⟩
  · have hc := ha.1
    rw [rem.same_base k] at hc
    exact hc.trans hpowM
  · intro b
    obtain ⟨hcenter, hframe, hdeg, hcoeff⟩ := rem.liftAtlas_parameter_bounds hp hr ha b
    have hpar := (rem.parent_valid k).2.2 (rem.parentIndex k (a.γ b))
    have hchild := ha.2.2.1 b
    have hshape₀ := hpar.2.2.2.1
    have hshape₁ := hchild.2.2.2.1
    have hshape := frameSize_mul_time (le_trans zero_le_one hκ) hshape₀ hshape₁
    have hprod : (rem.parent k).κ * a.κ ≤ (rem.liftAtlas k a).κ := by
      change (rem.parent k).κ * a.κ ≤ 2 * (rem.parent k).κ * a.κ
      nlinarith [mul_nonneg (le_trans zero_le_one (rem.slack_one k)) (le_trans zero_le_one hκ)]
    refine ⟨rem.liftAtlas_determinant_ne_zero ha b, hcenter, hframe, ?_, hdeg, hcoeff,
      rem.liftAtlas_A_measurable ha b, rem.liftAtlas_F_measurable ha b, ?_, ?_, ?_,
      rem.liftAtlas_floor hp ha hκ b⟩
    · exact hshape.trans (div_le_div_of_nonneg_right hprod (by positivity))
    · intro i
      have hA : Submission.Obl.k4_dyadic_crop_worlds.BoolFormat
          (p.N (rem.φ k) ^ rem.M + q.N k ^ M) (max rem.D D)
          {z | (i, z) ∈ (rem.liftAtlas k a).A b} := rem.liftAtlas_assignment_format ha b i
      have hF : Submission.Obl.k4_dyadic_crop_worlds.BoolFormat (q.N k ^ M) D
          {z : Fin 7 → ℝ | ((i, fun j : Fin 6 => z j.castSucc), z 6) ∈ (rem.liftAtlas k a).F b} :=
        rem.liftAtlas_incidence_format ha b i
      rw [rem.same_base k] at hA hF
      exact ⟨hA.mono hsum le_rfl, hF.mono hpowM (le_max_right _ _)⟩
    · intro l hl
      rcases hpar with ⟨_, _, _, _, _, _, _, _, _, hfit, _⟩
      have hold := hfit l hl.1
      exact ⟨hold.1.trans hpowpM, fun i => (hold.2.1 i).trans hpowpM,
        fun t ht => rem.liftAtlas_fit hp hr hrL ha hκ b l hl t ht⟩
    · exact rem.liftAtlas_incidence hp ha hκ b

end Remainder

end Submission.Obl.k4_native_finite_terminal_atlas_lift
