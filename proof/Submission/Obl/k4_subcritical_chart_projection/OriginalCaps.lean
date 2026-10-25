import Submission.Obl.k4_subcritical_chart_projection.Model
import Submission.Obl.k4_horizontal_supercritical_three_projections.CellCaps
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Mass
import Submission.Obl.k4_critical_conditional_row_preparation.NativeJointCap

set_option linter.unusedVariables false

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory Filter
open scoped ENNReal BigOperators
open Submission.Obl.k4_horizontal_supercritical_three_projections

noncomputable section

/-- Only the literal joint caps of the original physical coordinates are
used in the corrected-chart Scalar application. -/
def OriginalJointCaps {α : Type} [MeasurableSpace α]
    (N K d M B : ℝ) (μ : Measure (α × ℝ)) (π : Measure ℝ)
    (b : α → Fin 6 → ℝ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ B → ∀ vbin : ℤ,
    DirectionCap μ b π K (N ^ (-M)) (N ^ (-M)) (N ^ (-s)) d vbin

theorem original_joint_caps_eventually {α : Type} [MeasurableSpace α]
    (m : Model α) (hN : ∀ k, 2 ≤ m.N k) (hcaps : m.Caps)
    {R M B : ℝ} (hR : 1 < R) (hMlo : R⁻¹ ≤ M) (hMhi : M ≤ R) (hB : B ≤ R) :
    ∀ᶠ k in atTop, OriginalJointCaps (m.N k) (m.K k) m.d M B (m.μ k) (m.π k) (m.b k) := by
  filter_upwards [hcaps R hR] with k hk
  intro s hs hsB vbin c j
  have hN₀ : 0 < m.N k := by linarith [hN k]
  have hh := (hk M s M hMlo hMhi hs (hsB.trans hB) hMlo hMhi).2.2 false c j vbin
  have hpow : m.N k ^ (-3 * M - m.d * s) =
      (m.N k ^ (-M)) ^ (3 : ℕ) * (m.N k ^ (-s)) ^ m.d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN₀.le, ← Real.rpow_mul hN₀.le,
      ← Real.rpow_add hN₀]
    congr 1
    ring
  change _ ≤ ENNReal.ofReal (m.K k * (m.N k ^ (-M)) ^ 3 * (m.N k ^ (-s)) ^ m.d) * _
  have hz (p : α × ℝ) : HorizontalModel.z m k (m.N k) M p =
      (fun e => ⌊(![p.2, m.b k p.1 0 + p.2 * m.b k p.1 3,
        m.b k p.1 1 + p.2 * m.b k p.1 4] : Fin 3 → ℝ) e / m.N k ^ (-M)⌋) := by
    funext e
    fin_cases e <;> rfl
  have hx (p : α × ℝ) : m.x k p.1 p.2 3 = m.b k p.1 2 + p.2 * m.b k p.1 5 := rfl
  simpa only [Bool.false_eq_true, ite_false, hz, hx, hpow, mul_assoc] using hh

def chartReference (π : Measure ℝ) (χ D a d : ℝ) (q : Fin 3 → ℤ) : ℝ :=
  (π (Ico ((q 0 : ℝ) * χ) (((q 0 : ℝ) + 1) * χ))).toReal * D ^ 2 * a ^ d

theorem chartReference_nonneg (π : Measure ℝ) {χ D a d : ℝ} (ha : 0 ≤ a)
    (q : Fin 3 → ℤ) : 0 ≤ chartReference π χ D a d q := by
  unfold chartReference
  positivity

/-- The given original floors already bound the entire reference budget.
No count of charts or fine velocity bins enters. -/
theorem Charts.reference_budget {α : Type} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} {ρ : Measure (α × ℝ)} {π : Measure ℝ} [IsFiniteMeasure π]
    {χ D a σ d H mass K : ℝ} {w : Fin 3 → ℝ}
    (C : Charts b ρ π χ D a σ d H mass w)
    (ha : 0 < a) (hH : 0 < H) (hK : 0 ≤ K) (hρ : ρ univ ≤ ENNReal.ofReal K) :
    ∑ c, chartReference π χ D a d (C.q c) ≤ H * K := by
  classical
  have hdisj : (↑(Finset.univ : Finset (Fin C.n)) : Set (Fin C.n)).PairwiseDisjoint
      (fun c => C.G c ×ˢ Icc (0 : ℝ) 1) := by
    intro c _ c' _ hne
    apply disjoint_left.mpr
    intro p hp hp'
    exact disjoint_left.mp (C.disjoint c c' hne) hp.1 hp'.1
  have hfloor (c : Fin C.n) :
      ENNReal.ofReal (chartReference π χ D a d (C.q c) / H) ≤
        ρ (C.G c ×ˢ Icc (0 : ℝ) 1) := by
    have heq : chartReference π χ D a d (C.q c) / H =
        (D ^ 2 * a ^ d / H) *
          (π (Ico ((C.q c 0 : ℝ) * χ) (((C.q c 0 : ℝ) + 1) * χ))).toReal := by
      unfold chartReference
      ring
    rw [heq, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal (measure_ne_top π _)]
    exact C.floor c
  simpa using
    (Parent.original_reference_budget ρ Finset.univ
      (fun c => C.G c ×ˢ Icc (0 : ℝ) 1)
      (fun c => chartReference π χ D a d (C.q c))
      hH hK (fun c _ => chartReference_nonneg π ha.le _)
      (fun c _ => (C.measurable c).prod measurableSet_Icc) hdisj
      (fun c _ => hfloor c) hρ)

end
end Submission.Obl.k4_subcritical_chart_projection
