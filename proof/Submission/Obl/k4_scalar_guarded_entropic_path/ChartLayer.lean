import Submission.Obl.k4_scalar_guarded_entropic_path.SubLayer
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.NarrowDeletion
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueLiftChains

/-! Keep the original full TRUE witnesses of wide rows. All deletions
are paid by the one current original-law submeasure. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)

noncomputable section

namespace Layer

def empty (w : ℕ) : Layer w :=
  mk 0 0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
    Fin.elim0 Fin.elim0 (fun _ _ => ∅)

def ofChart {p : Code} {B k : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag k) : Layer (p.1 k) :=
  mk Q.T Q.n Q.γ Q.j Q.A Q.C Q.u Q.v Q.J Q.P Q.Λ

/-- The tagged region of the unchanged full selected witnesses. -/
def region {w : ℕ} (F : Layer w) : Set (Fin w × Incidence) :=
  {z | ∃ i, F.world i = z.1 ∧ z.2 ∈ F.witness i}

end Layer

/-- A row outside the narrow event has the required full-block width
once its finite-stage allowance absorbs the width deficit. -/
theorem width_of_not_narrow {N H ε u J : ℝ} {T : ℕ} (hN : 0 < N)
    (hJ : 0 ≤ J) (hH : 2 * N ^ (ε + u) ≤ H)
    (hw : N ^ (-u) < 2 * N ^ ε * J * (2 : ℝ) ^ T) :
    (H * (2 : ℝ) ^ T)⁻¹ ≤ J := by
  have hA : 0 < N ^ u := Real.rpow_pos_of_pos hN _
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hq : 0 < (2 : ℝ) ^ T := by positivity
  have hm := mul_lt_mul_of_pos_left hw hA
  rw [Real.rpow_neg hN.le, mul_inv_cancel₀ hA.ne'] at hm
  have heq : N ^ u * (2 * N ^ ε * J * (2 : ℝ) ^ T) =
      (2 * N ^ (ε + u)) * (J * (2 : ℝ) ^ T) := by
    rw [Real.rpow_add hN]
    ring
  rw [heq] at hm
  have hbound := mul_le_mul_of_nonneg_right hH (mul_nonneg hJ hq.le)
  apply (inv_le_iff_one_le_mul₀ (mul_pos hH0 hq)).2
  nlinarith only [hm, hbound]

/-- Prune only row labels, preserving every original full assignment,
selected TRUE witness and its earlier mass floor. -/
theorem exists_wide_true_layer {p : Code} {B M k : ℕ} {r b h ε v H u : ℝ}
    (Q : ChartW p B r b h ε true k) (hN : 1 ≤ p.N k) (hBM : B ≤ M)
    (hεv : ε ≤ v) (hH : 2 * p.N k ^ (ε + u) ≤ H)
    (σ : Fin (p.1 k) → Measure Incidence) (hσ : ∀ g, σ g ≤ Split.mu p k g)
    (hcover : ∀ g, σ g {z | ∃ i, Q.γ i = g ∧ z ∈ Q.C i}ᶜ = 0)
    (hbad : ∀ g, σ g (WidthGeometry.narrowEvent (Layer.ofChart Q) ε u g) = 0)
    (hmass : ENNReal.ofReal (p.N k ^ (-v)) ≤
      ∑ g, ENNReal.ofReal (p.weight k g) * σ g Set.univ) :
    ∃ F : Layer (p.1 k), F.T = Q.T ∧
      Split.ChartData p M r b h v true k F.T F.n F.world F.block
        F.assignment F.witness F.u F.v F.width F.graph F.list ∧
      (∀ i, (H * (2 : ℝ) ^ F.T)⁻¹ ≤ F.width i) ∧
      (∀ g, σ g {z | ∃ i, F.world i = g ∧ z ∈ F.witness i}ᶜ = 0) := by
  classical
  let base := Layer.ofChart Q
  let keep : Fin base.n → Prop := fun i => (H * (2 : ℝ) ^ base.T)⁻¹ ≤ base.width i
  have hN0 : 0 < p.N k := lt_of_lt_of_le zero_lt_one hN
  have hc : Split.ChartData p M r b h v true k base.T base.n base.world base.block
      base.assignment base.witness base.u base.v base.width base.graph base.list :=
    Submission.Obl.k4_scalar_true_terminal_lifting.chartData_mono Q.hcd hN hBM le_rfl hεv
  have hcov : ∀ g, σ g {z | ∃ i, keep i ∧ base.world i = g ∧ z ∈ base.witness i}ᶜ = 0 := by
    intro g
    apply measure_mono_null _ (measure_union_null (hcover g) (hbad g))
    intro z hz
    by_cases hold : ∃ i, Q.γ i = g ∧ z ∈ Q.C i
    · by_cases hb : z ∈ WidthGeometry.narrowEvent base ε u g
      · exact Or.inr hb
      · have hw := WidthGeometry.cover_wide_of_not_mem hold hb
        obtain ⟨i, hi, hzi, hwi⟩ := hw
        have hJi : 0 ≤ base.width i := (Q.hcd.2.2.2.2.2.1 i).2.1.le
        exact (hz ⟨i, width_of_not_narrow hN0 hJi hH hwi, hi, hzi⟩).elim
    · exact Or.inl hold
  refine ⟨base.prune keep, rfl,
    Layer.chartData_prune_of_submeasure hc keep σ hσ hcov hmass, ?_, ?_⟩
  · intro i
    exact base.keptEmb_keep keep i
  · intro g
    simpa only [base.prune_witness_union keep] using hcov g

end

end Submission.Obl.k4_scalar_guarded_entropic_path
