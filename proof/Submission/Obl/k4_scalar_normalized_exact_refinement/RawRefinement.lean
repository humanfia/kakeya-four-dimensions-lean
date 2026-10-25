import Submission.Obl.k4_scalar_normalized_exact_refinement.RawConstruction

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set Filter
open k4_scalar_linear_critical_extremizers.Split

noncomputable section

namespace ChosenCharts

variable {p : Code} {r b h : ℝ} (a : ChosenCharts p r b h)

/-- The normalized code uses the entire assigned conditional priors, the
chosen incidences, and exactly the original assignment-budget weights. -/
theorem code_refinement (hp : Spec.RawScalar p) (M' D' : ℕ) (d' : ℝ) :
    Refinement p (a.code M' D' d') r b h := by
  refine ⟨a.φ, a.ε, a.B, a.T, a.γ, a.j, a.A, a.C, a.u, a.v, a.J, a.P, a.Λ, a.θ,
    a.φ_mono, a.ε_pos, a.ε_lim, a.B_pos, ?_, ?_, ?_⟩
  · exact fun k => ⟨rfl, a.data k⟩
  · intro k i
    refine ⟨a.θ_measurable k i, ?_, ?_, ?_, rfl, a.selected_law hp k i⟩
    · intro l
      exact normalizeLine_label ..
    · intro l t
      exact y_normalizeLine_at _ _ _ _ _ _ _ (a.dt_pos k).ne' l t
    · intro l t
      exact x_normalizeLine_at _ ((a.data k).2.2.2.2.2.1 i).2.2.2.2.2.1
        _ _ _ _ _ _ (a.dt_pos k).ne' l t
  · exact fun k => ⟨a.Z_pos hp k, fun _ => rfl⟩

end ChosenCharts

/-- Raw scalar normalization, with a literal refinement certificate. The
profile and angular clauses can be supplied after pure homogenization. -/
theorem raw_normalized_refinement (p : Code) (r b h d' : ℝ)
    (hp : Spec.RawScalar p) (hr : 0 ≤ r) (hrL : r < L p)
    (hd'0 : 0 ≤ d') (hd'1 : d' < 1) (hk : Known p r b h) :
    ∃ q : Code, Spec.RawScalar q ∧ L q = L p - r ∧ d q = d' ∧ S q = S p ∧
      U q = U p * (L p - r) / L p ∧ Refinement p q r b h := by
  classical
  obtain ⟨a⟩ := ChosenCharts.nonempty hp hk
  let count : ℝ := max (M p : ℝ) (a.B : ℝ) + 1
  let height : ℝ := (M p : ℝ) + 4 * h + 6 + ((a.B : ℝ) + 2)
  obtain ⟨M', hM'⟩ := exists_nat_gt (max count (max 4 height))
  have hcount : count ≤ M' := (le_max_left _ _).trans hM'.le
  have hfit : (4 : ℝ) ≤ M' := (le_max_left _ _).trans ((le_max_right _ _).trans hM'.le)
  have hheight : height ≤ M' := (le_max_right _ _).trans ((le_max_right _ _).trans hM'.le)
  let D' := 2 * max (D p) a.B + 1
  refine ⟨a.code M' D' d', a.code_raw hp hr hrL hd'0 hd'1 hcount hfit hheight
    (Nat.le_succ _) (Nat.succ_le_succ (Nat.zero_le _)), rfl, rfl, rfl, rfl,
    a.code_refinement hp M' D' d'⟩

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
