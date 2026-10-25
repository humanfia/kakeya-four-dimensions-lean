/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldSelectedNormal.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldOriginalCaps
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldGlobalFilling
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldResidualSelection
import Submission.Obl.k4_scalar_graph_residual_discovery.Jets.Restrict

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open WangZahlLot.Obl.wz_slab_local_linearity

namespace Zoom

/-- The final selected event is scalar-normal under its UNCHANGED full
coefficient-bin prior. Its density comes from the original mass floor and
the actual whole-state product loss. Support uses the ENTIRE global filling
law, and absolute/conditional caps use the original prior floors. -/
theorem scalarNormal_of_selected_original_world
    {μ : Measure ScalarIncidence} {θ : Measure ScalarLine} [IsFiniteMeasure θ]
    {R : Set ScalarIncidence} {ρ b ζ d H Hc Krow Hrow A : ℝ} {q : Fin 5 → ℤ}
    {n : ℕ} {K : ℕ → ℕ} {G : (Fin 3 → ℤ) → Fin 2 → ℝ}
    (sel : ResidualWorldSelection μ R ρ b q Hc Krow Hrow A ζ n K G)
    (caps : OriginalWorldCaps θ R ρ ζ d q)
    (filling : GlobalWorldFilling R ρ b ζ d)
    (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hd : 0 ≤ d) (hd₁ : d ≤ 1)
    (hH : 1 ≤ H) (hHrow : 0 ≤ Hrow)
    (hcoeff : ∀ p ∈ R, ∀ e, |p.1.2 e| ≤ H)
    (htime : ∀ p ∈ R, p.2 ∈ Icc (0 : ℝ) 1)
    {U δ P Kn δc : ℝ} (hU : 0 < U) (hδ : 0 < δ) (hP : 0 < P) (hKn : 1 ≤ Kn)
    (hμ : μ ≤ ENNReal.ofReal U • θ.prod volume)
    (hpositive : θ {l | cell ρ l.2 = q} ≠ 0)
    (hbefore : ENNReal.ofReal δ * θ {l | cell ρ l.2 = q} ≤ μ (R ∩ {p | cell ρ p.1.2 = q}))
    (hcost : (∏ i ∈ Finset.range n, ((4 : ℝ≥0∞) ^ 3 * K i)) ≤ ENNReal.ofReal P)
    (hmass_budget : U * P / δ ≤ Kn)
    (hrow_budget : Hrow ≤ Kn)
    (hRC_budget : 12 * worldRowConstant Hc Krow ^ 2 ≤ Kn)
    (hRes_budget : 6 * (A + Hrow + 5) ≤ Kn)
    (hAC_budget : 9 * caps.H ^ 2 * caps.A ^ 4 ≤ Kn)
    (hBC_budget : 9 * caps.H ^ 2 * caps.A ^ 4 / caps.η ≤ Kn)
    (hSS_budget : filling.supportBound Hrow ≤ Kn)
    (hcoarse : ∀ p ∈ R, cell ρ p.1.2 = q →
      |filling.row (assignedCell ρ b p) 1 - G (cell b (scalarPosition p)) 1| ≤ δc)
    (hSS_precision : ∀ v,
      2 * (δc + 4 * worldRowConstant Hc Krow ^ 2 * ρ) +
        (1 + |filling.row v 0| + |filling.row v 1|) * b / ρ ≤ ζ) :
    Jets.ScalarNormal (prior θ ρ q) (coeff ρ q) sel.event sel.F
      (fun r l => cell (caps.β r) l.2) Kn ζ d := by
  have hmass : ENNReal.ofReal (δ / P) * θ {l | cell ρ l.2 = q} ≤ μ sel.event := by
    have hcombined : ENNReal.ofReal δ * θ {l | cell ρ l.2 = q} ≤
        ENNReal.ofReal P * μ sel.event :=
      hbefore.trans (sel.mass.trans (mul_le_mul_of_nonneg_right hcost zero_le))
    have hdiv : (ENNReal.ofReal δ * θ {l | cell ρ l.2 = q}) / ENNReal.ofReal P ≤
        μ sel.event :=
      (ENNReal.div_le_iff' (ne_of_gt (ENNReal.ofReal_pos.mpr hP)) ENNReal.ofReal_ne_top).mpr hcombined
    rw [ENNReal.ofReal_div_of_pos hP]
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hbudget : U / (δ / P) ≤ Kn := by
    have heq : U / (δ / P) = U * P / δ := by field_simp [hδ.ne', hP.ne'] <;> ring
    rw [heq]
    exact hmass_budget
  have htime_abs (p : ScalarIncidence) (hp : p ∈ R) : |p.2| ≤ 1 := by
    rw [abs_of_nonneg (htime p hp).1]
    exact (htime p hp).2
  have hfinite : ((fun p => cell b (scalarPosition p)) '' sel.event).Finite := by
    apply (finite_original_physical_records R hH hb hcoeff htime_abs).subset
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, (sel.sub hp).1, rfl⟩
  have hcoarseF (p : ScalarIncidence) (hp : p ∈ sel.event) :
      |filling.row (assignedCell ρ b p) 1 - sel.F p.2| ≤
        δc + 4 * worldRowConstant Hc Krow ^ 2 * ρ :=
    (abs_sub_le _ (G (cell b (scalarPosition p)) 1) _).trans
      (add_le_add (hcoarse p (sel.sub hp).1 (sel.sub hp).2) (sel.row_close p hp))
  have hsupport := filling.support_on_world_subset hρ hb hbρ hζ hζ₁ hd q sel.event
    (fun p hp => (sel.sub hp).1) (fun p hp => (sel.sub hp).2) hfinite
    (fun p hp => htime_abs p (sel.sub hp).1) sel.F hHrow (fun p _ => sel.row_bound p.2)
    hcoarseF hSS_precision
  exact caps.normal_on_subset μ sel.measurable_event sel.sub hρ hζ hζ₁ hd hd₁
    hKn hU (div_pos hδ hP) hbudget hAC_budget hBC_budget hμ hpositive
    (fun p hp => htime p (sel.sub hp).1) hmass sel.F sel.measurable_F
    (fun p _ => (sel.row_bound p.2).trans hrow_budget)
    (fun t => Jets.intervalAD_mono_const hζ (hsupport t) hSS_budget)
    (fun p hp p' hp' => (sel.row_cmp p hp p' hp').trans
      (mul_le_mul_of_nonneg_right hRC_budget (by positivity)))
    (fun p hp p' hp' => (sel.residual_cmp p hp p' hp').trans
      (mul_le_mul_of_nonneg_right hRes_budget (by positivity)))

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
