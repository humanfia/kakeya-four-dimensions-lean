/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/OriginalGraphTube.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ComparisonIndexCaps

/-! A tube cap for a stable graph directly from original finite native-bin caps. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

theorem measurableSet_graph_tube {Ω : Type*} [MeasurableSpace Ω]
    (base : Ω → EuclideanSpace ℝ (Fin 3)) (hb : Measurable base)
    (signal : Ω → ℝ) (hs : Measurable signal)
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) {r E : ℝ}
    (hf : ContinuousOn f (closedBall 0 r)) :
    MeasurableSet {p | ‖base p‖ ≤ r ∧ ‖(signal p : ℂ) - f (base p)‖ ≤ E} := by
  let C : Set (EuclideanSpace ℝ (Fin 3) × ℝ) := closedBall 0 r ×ˢ univ
  have hc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 3) × ℝ => (p.2 : ℂ) - f p.1) C :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn.sub
      (hf.comp continuous_fst.continuousOn (fun p hp => hp.1))
  have hclosed := hc.preimage_isClosed_of_isClosed
    (isClosed_closedBall.prod isClosed_univ) (isClosed_closedBall : IsClosed (closedBall (0 : ℂ) E))
  have h := hclosed.measurableSet.preimage (hb.prodMk hs)
  have heq : {p | ‖base p‖ ≤ r ∧ ‖(signal p : ℂ) - f (base p)‖ ≤ E} =
      (fun p => (base p, signal p)) ⁻¹'
        (C ∩ (fun p : EuclideanSpace ℝ (Fin 3) × ℝ => (p.2 : ℂ) - f p.1) ⁻¹' closedBall 0 E) := by
    ext p
    simp [C, mem_closedBall_zero_iff]
  rw [heq]
  exact h

/-- Finite native-bin caps give the same original graph tube ceiling after summing
the exact cell volumes. There is no continuous base-density assumption. -/
theorem original_graph_tube_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ComparisonMesh μ) (signal : Ω → ℝ) (hs : Measurable signal)
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) (K : NNReal)
    (hf : LipschitzOnWith K f (closedBall 0 (1 / 2)))
    {a : ℝ} (ha : 0 < a) (hresolve : (K : ℝ) * M.diameter ≤ a)
    (hvolume : (∑ _q : Fin M.n, M.vol) ≤ 1)
    (A : ℝ≥0∞)
    (hcap : ∀ q j, μ {p | M.code p = q ∧ ⌊signal p / a⌋ = j} ≤ A * M.vol) :
    μ {p | ‖M.base p‖ ≤ 1 / 2 ∧ ‖(signal p : ℂ) - f (M.base p)‖ ≤ 2 * a} ≤ 14 * A := by
  let Tube := {p | ‖M.base p‖ ≤ 1 / 2 ∧ ‖(signal p : ℂ) - f (M.base p)‖ ≤ 2 * a}
  have hTube : MeasurableSet Tube :=
    measurableSet_graph_tube M.base M.measurable_base signal hs f hf.continuousOn
  let ρ := μ.restrict Tube
  let M' : ComparisonMesh ρ := M.mono Measure.restrict_le_self
  have hfit : ∀ᵐ p ∂ρ, ‖(signal p : ℂ) - f (M'.base p)‖ ≤ 2 * a := by
    filter_upwards [ae_restrict_mem hTube] with p hp
    exact hp.2
  have hcaps (q : Fin M.n) (j : ℤ) :
      ρ {p | M'.code p = q ∧ ⌊signal p / a⌋ = j} ≤ A * M'.vol := by
    exact (Measure.restrict_le_self _).trans (hcap q j)
  have hi (q : Fin M.n) : ρ {p | M.code p = q} ≤ 14 * A * M.vol := by
    have h := index_cell_cap_of_native_bins_radius ρ M' (fun _ => (0 : Fin 1)) signal
      (fun _ => f) K ha (by positivity : 0 ≤ 3 * a)
      (by change 2 * a + (K : ℝ) * M.diameter ≤ 3 * a; linarith)
      (fun _ => hf) hfit A hcaps q 0
    have hconst : 4 * (3 * a) / a + 2 = 14 := by field_simp; norm_num
    change ρ {p | M.code p = q ∧ (0 : Fin 1) = 0} ≤
      ENNReal.ofReal (4 * (3 * a) / a + 2) * A * M.vol at h
    simpa only [hconst, ENNReal.ofReal_ofNat, and_true] using h
  have hsum : (∑ q : Fin M.n, ρ {p | M.code p = q}) = ρ univ := by
    have h := congrArg (fun ν : Measure Ω => ν univ) M'.pieces_sum
    have h' : (∑ q : Fin M'.n, ρ {p | M'.code p = q}) = ρ univ := by
      simpa only [Measure.finsetSum_apply, ComparisonMesh.pieces, codePieces,
        Measure.restrict_apply_univ] using h
    exact h'
  calc
    μ Tube = ρ univ := by simp [ρ]
    _ = ∑ q : Fin M.n, ρ {p | M.code p = q} := hsum.symm
    _ ≤ ∑ _q : Fin M.n, 14 * A * M.vol := Finset.sum_le_sum fun q _ => hi q
    _ = (14 * A) * ∑ _q : Fin M.n, M.vol := (Finset.mul_sum _ _ _).symm
    _ ≤ (14 * A) * 1 := mul_le_mul' le_rfl hvolume
    _ = _ := mul_one _

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
