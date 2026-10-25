/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/ChosenNormalization.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrackedExactRefinement
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueChosenCharts
import Submission.Obl.k4_scalar_normalized_exact_refinement.RawRefinement
import Submission.Obl.k4_scalar_chart_normalization

/-! Normalize through an explicitly supplied atlas. The normalized exact
problem retains its full assignments and scalar maps through the tracked
subfamily. All raw normalization, profile and terminal-lifting estimates
are imported from gate-accepted scalar obligations. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_normalized_exact_refinement

noncomputable section

/-- A named witness with precisely the supplied chart data. Extracting an
arbitrary witness from the existential Refinement would lose this identity. -/
def chosen_refinement_witness {p : Code} {r b h : ℝ} (a : ChosenCharts p r b h)
    (hp : Spec.RawScalar p) (M' D' : ℕ) (d' : ℝ) :
    RefinementWitness p (a.code M' D' d') r b h where
  toRefinementData :=
    ⟨a.φ, a.ε, a.B, a.T, a.γ, a.j, a.A, a.C, a.u, a.v, a.J, a.P, a.Λ, a.θ⟩
  sample_strictMono := a.φ_mono
  loss_pos := a.ε_pos
  loss_tendsto := a.ε_lim
  exponent_one := a.B_pos
  charts k := ⟨rfl, a.data k⟩
  maps k i := by
    refine ⟨a.θ_measurable k i, ?_, ?_, ?_, rfl, a.selected_law hp k i⟩
    · intro l
      exact normalizeLine_label ..
    · intro l t
      exact y_normalizeLine_at _ _ _ _ _ _ _ (a.dt_pos k).ne' l t
    · intro l t
      exact x_normalizeLine_at _ ((a.data k).2.2.2.2.2.1 i).2.2.2.2.2.1
        _ _ _ _ _ _ (a.dt_pos k).ne' l t
  weights k := ⟨a.Z_pos hp k, fun _ => rfl⟩

theorem exists_chosen_raw_parameters {p : Code} {r b h : ℝ}
    (a : ChosenCharts p r b h) (hp : Spec.RawScalar p)
    (hr : 0 ≤ r) (hrL : r < L p) {d' : ℝ} (hd' : 0 ≤ d') (hd'1 : d' < 1) :
    ∃ M' D' : ℕ, Spec.RawScalar (a.code M' D' d') := by
  let count : ℝ := max (M p : ℝ) (a.B : ℝ) + 1
  let height : ℝ := (M p : ℝ) + 4 * h + 6 + ((a.B : ℝ) + 2)
  obtain ⟨M', hM'⟩ := exists_nat_gt (max count (max 4 height))
  have hcount : count ≤ M' := (le_max_left _ _).trans hM'.le
  have hfit : (4 : ℝ) ≤ M' := (le_max_left _ _).trans ((le_max_right _ _).trans hM'.le)
  have hheight : height ≤ M' := (le_max_right _ _).trans ((le_max_right _ _).trans hM'.le)
  refine ⟨M', 2 * max (D p) a.B + 1, ?_⟩
  exact a.code_raw hp hr hrL hd' hd'1 hcount hfit hheight
    (Nat.le_succ _) (Nat.succ_le_succ (Nat.zero_le _))

/-- The true-atlas prior floor belongs to the supplied assignments and
is inherited by every later tracked refinement. -/
theorem chosen_true_saturation {p : Code} {r b h : ℝ} (a : TrueChosenCharts p r b h)
    (hp : Exact p) (M' D' : ℕ) (d' : ℝ) :
    (chosen_refinement_witness a.toChosenCharts
      (specExact_of_exact hp).1 M' D' d').toRefinementData.Saturated r a.ε := by
  apply RefinementWitness.saturated_of_true_charts _ hp
  exact a.true_data

/-- Terminal lifting gives the horizon inequality for THIS actual
refinement, independently of how its atlas was supplied. -/
theorem horizon_le_refinement {p q : Code} {r b h : ℝ}
    (hp : Exact p) (hq : Exact q) (hr : 0 ≤ r) (hrL : r < L p)
    (hrb : r ≤ b) (hbL : b ≤ L p) (hh : 0 ≤ h)
    (hLq : L q = L p - r) (href : Refinement p q r b h) :
    Horizon p ≤ h + Horizon q := by
  have hI : Initial := Submission.k4_scalar_initial_true_horizon
  have hne : {a : ℝ | Cost q a}.Nonempty := ⟨L q, hI q hq⟩
  have hbdd : BddBelow {a : ℝ | Cost p a} := ⟨0, fun _ ha => ha.1⟩
  have hinf : Horizon p - h ≤ Horizon q := by
    apply le_csInf hne
    intro a ha
    have hlift : Cost p (h + a) := Submission.k4_scalar_true_terminal_lifting
      p q r b h a hp hq hr hrL hrb hbL hh hLq href ha
    have hbound : Horizon p ≤ h + a := csInf_le hbdd hlift
    linarith
  linarith

/-- Exact normalization through a GIVEN chosen atlas, with the original
assignment/map provenance, relative profiles and actual horizon bound. -/
theorem normalize_through_chosen_charts {p : Code} {r b h d' : ℝ}
    (hp : Exact p) (a : ChosenCharts p r b h)
    (hr : 0 ≤ r) (hrL : r < L p) (hrb : r ≤ b) (hbL : b ≤ L p)
    (hh : 0 ≤ h) (hd' : 0 ≤ d') (hd'1 : d' < 1)
    (htail : ∀ s, r ≤ s → s ≤ L p → f p (L p) - f p s ≤ d' * (L p - s)) :
    ∃ (M' D' : ℕ)
      (out : RetainedRefinement
        (chosen_refinement_witness a (specExact_of_exact hp).1 M' D' d')),
      Exact out.code ∧ L out.code = L p - r ∧ d out.code = d' ∧
      S out.code = S p ∧ U out.code = U p * (L p - r) / L p ∧
      Horizon p ≤ h + Horizon out.code ∧
      (∀ s, 0 ≤ s → s ≤ L out.code →
        f out.code (L out.code) - f out.code s ≤ f p (L p) - f p (r + s)) ∧
      (b = r → ∀ s, 0 ≤ s → s ≤ L out.code →
        f out.code s - f out.code 0 = f p (r + s) - f p r) := by
  obtain ⟨M', D', hraw⟩ := exists_chosen_raw_parameters a (specExact_of_exact hp).1 hr hrL hd' hd'1
  let w := chosen_refinement_witness a (specExact_of_exact hp).1 M' D' d'
  obtain ⟨out, hout, hL, hd, hS, hU, hrelative, hequal⟩ :=
    exists_exact_retained_refinement hp hraw w hr hrL hrb hbL rfl rfl rfl htail
  refine ⟨M', D', out, hout, hL, hd, hS, hU, ?_, hrelative, hequal⟩
  exact horizon_le_refinement hp hout hr hrL hrb hbL hh hL
    (refinement_iff_nonempty_witness.mpr ⟨out.witness⟩)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
