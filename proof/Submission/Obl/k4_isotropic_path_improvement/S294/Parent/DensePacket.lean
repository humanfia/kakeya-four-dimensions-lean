-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.DensePacket, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/DensePacket.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Selection of a dense old packet at any prescribed level of the
path, AFTER all global cuts, and the full-measure pointwise cut of its
current events (velocity and vertical-derivative bounds). Adapted in
spirit from `exists_dense_root_packet_source` (this LOT tree, o265, session
x1046, branch x0943, commit 177a30b2, Broad/Source/OriginalRootPacketSelection.lean),
generalized from level zero to any level through terminal ancestors.
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalPacketCutSelection
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PathBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.CountedPruning
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Frames

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

namespace DensePacket

open ParentSource ParentSource.Native

/-- **A dense old packet at any level.** Terminal events are covered by their
ancestors at the level; the full reference budget selects a packet. -/
theorem exists_dense_packet_at_level {d : ProblemData} (hd : d.Valid) {k m : ℕ}
    {p : PathData (d.W k)} {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (ℓ : ℕ) (hℓ : ℓ ≤ m - 1) (source : Fin (d.W k) → Set Ev)
    (hterm : ∀ w, source w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {dens : ℝ} (hdens : 0 < dens)
    (hmass : ENNReal.ofReal dens + ENNReal.ofReal dens ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (source w)) :
    ∃ old : Fin p.C, p.lev old = ℓ ∧ 0 < d.ω k (p.γ old) ∧ d.ν k (p.γ old) (p.A old) ≠ 0 ∧
      ENNReal.ofReal dens * (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T ℓ)⁻¹)) ≤
        ((d.ν k (p.γ old)).prod volume) (source (p.γ old) ∩ p.F old) := by
  classical
  let I := {b : Fin p.C // p.lev b = ℓ}
  have hcover (w : Fin (d.W k)) : source w ⊆ {z | ∃ b : I, p.γ b.1 = w ∧ z ∈ p.F b.1} := by
    intro z hz
    obtain ⟨bt, hbt, hbtw, hzbt⟩ := hterm w hz
    obtain ⟨hl, hg, hF⟩ := Broad.iterate_par_spec hp.toOriginal (m - 1 - ℓ) bt
      (by change m - 1 - ℓ ≤ p.lev bt; omega)
    refine ⟨⟨p.par^[m - 1 - ℓ] bt, ?_⟩, hg.trans hbtw, hF hzbt⟩
    change p.lev (p.par^[m - 1 - ℓ] bt) = p.lev bt - (m - 1 - ℓ) at hl
    rw [hl, hbt]
    omega
  obtain ⟨b, hw, hpos, hfloor⟩ := hp.exists_dense_original_packet_after_cuts
    (hd.weights k).2.2 (hd.weights k).1 (hd.weights k).2.1
    (fun b : I => b.1) Subtype.val_injective ℓ (fun b => b.2) source hcover
    (fun b => source (p.γ b.1) ∩ p.F b.1) (fun _ => subset_rfl) 0
    (fun _ => by simp only [zero_mul, add_zero]; exact le_rfl)
    hdens hmass (by positivity)
  exact ⟨b.1, b.2, hw, hpos, hfloor⟩

/-- The vertical derivative lower bound of the problem holds almost
everywhere on its events. -/
theorem deriv_lower_ae {d : ProblemData} (hd : d.Valid) (k : ℕ) (w : Fin (d.W k)) :
    ∀ᵐ z ∂(((d.ν k w).prod volume).restrict (d.E k w)),
      d.B k w / d.K k ≤ |MvPolynomial.eval (xp z.1 z.2) (MvPolynomial.pderiv 3 (d.P k w))| := by
  rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
  obtain ⟨M, D, hformat⟩ := hformat
  rcases (hformat k).2.2.2.1 w with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlow⟩
  exact hlow

/-- The pointwise good events of a world. -/
def pointwiseGood (d : ProblemData) (k : ℕ) (w : Fin (d.W k)) : Set Ev :=
  {z | ‖v z.1‖ ≤ d.K k ∧
    d.B k w / d.K k ≤ |MvPolynomial.eval (xp z.1 z.2) (MvPolynomial.pderiv 3 (d.P k w))|}

theorem measurableSet_pointwiseGood (d : ProblemData) (k : ℕ) (w : Fin (d.W k)) :
    MeasurableSet (pointwiseGood d k w) := by
  rw [pointwiseGood, Set.setOf_and]
  apply MeasurableSet.inter
  · apply measurableSet_le _ measurable_const
    have : Continuous fun z : Ev => v z.1 := by
      unfold v
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi; intro i
      fin_cases i <;> simp <;> fun_prop
    exact this.measurable.norm
  · apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Continuous.measurable
    apply (MvPolynomial.continuous_eval _).comp
    apply continuous_pi; intro i
    fin_cases i <;> simp [xp] <;> fun_prop

/-- **The pointwise cut has full measure** on any event set of the world. -/
theorem pointwise_cut_measure {d : ProblemData} (hd : d.Valid) (k : ℕ) (w : Fin (d.W k))
    (C0 : Set Ev) (hC0E : C0 ⊆ d.E k w) :
    ((d.ν k w).prod volume) (C0 ∩ pointwiseGood d k w) = ((d.ν k w).prod volume) C0 := by
  apply le_antisymm (measure_mono inter_subset_left)
  have hbad : ((d.ν k w).prod volume) (C0 \ pointwiseGood d k w) = 0 := by
    apply measure_mono_null (t := {z : Ev | ¬ ‖v z.1‖ ≤ d.K k} ∪
      (d.E k w ∩ {z | ¬ d.B k w / d.K k ≤
        |MvPolynomial.eval (xp z.1 z.2) (MvPolynomial.pderiv 3 (d.P k w))|}))
    · rintro z ⟨hz, hzg⟩
      simp only [pointwiseGood, mem_setOf_eq, not_and_or] at hzg
      rcases hzg with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hC0E hz, h⟩
    · apply measure_union_null
      · have hv : ∀ᵐ l ∂d.ν k w, ‖v l‖ ≤ d.K k := by
          filter_upwards [hd.native_bounds k w] with l hl
          have := hl 0 ⟨le_rfl, zero_le_one⟩
          exact le_trans (le_add_of_nonneg_left (norm_nonneg _)) this
        have hnull : d.ν k w {l | ¬ ‖v l‖ ≤ d.K k} = 0 := ae_iff.mp hv
        have hset : {z : Ev | ¬ ‖v z.1‖ ≤ d.K k} = {l | ¬ ‖v l‖ ≤ d.K k} ×ˢ univ := by
          ext z; simp
        rw [hset, Measure.prod_prod, hnull, zero_mul]
      · have hae := deriv_lower_ae hd k w
        rw [ae_iff, Measure.restrict_apply' (by
          rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
          obtain ⟨M, D, hformat⟩ := hformat
          exact ((hformat k).2.2.2.1 w).2.2.2.2.2.2.2.1)] at hae
        rw [inter_comm]
        exact hae
  calc ((d.ν k w).prod volume) C0
      ≤ ((d.ν k w).prod volume) ((C0 ∩ pointwiseGood d k w) ∪ (C0 \ pointwiseGood d k w)) :=
        measure_mono (fun z hz => by
          by_cases h : z ∈ pointwiseGood d k w
          · exact Or.inl ⟨hz, h⟩
          · exact Or.inr ⟨hz, h⟩)
    _ ≤ ((d.ν k w).prod volume) (C0 ∩ pointwiseGood d k w) +
        ((d.ν k w).prod volume) (C0 \ pointwiseGood d k w) := measure_union_le _ _
    _ = _ := by rw [hbad, add_zero]

end DensePacket

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
