-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/PrunedComparisonTable.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/PrunedComparisonTable.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SourceSheetFamilies
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.StoredWitnessPreparation
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ComparisonPreparation
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.RetainedPartnerLists

/-! Prepare the actual two original witness families and construct their comparison table. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set
open scoped ENNReal Classical

noncomputable section

/-- Original reference pruning either pays for an entire empty domain or yields
an actual comparison table with measurable indices into the old label families.
Its reference sum is bounded by the old family's weighted domain count. -/
theorem exists_pruned_comparison_table {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (M : ComparisonMesh μ)
    {D : ℕ} {d a B F T L : ℝ} (K : NNReal)
    (signal : Ω → ℝ) (hs : Measurable signal)
    (f₁ f₂ : OriginalSheetFamily μ D a K M.base signal)
    (ha : 0 < a) (hB : 0 < B) (hF : 0 < F) (hT : 0 < T) (hL : 14 * B * F ≤ L)
    (palette : ℝ≥0∞) (hp : palette ≠ 0) (hpt : palette ≠ ⊤)
    (hresolve : 2 * (K : ℝ) * M.diameter ≤ a / 2)
    (hvolume : (∑ _q : Fin M.n, M.vol) ≤ 1)
    (hnative : ∀ R : ℝ, a ≤ R → ∀ q j,
      μ {p | M.code p = q ∧ ⌊signal p / R⌋ = j} ≤
        (ENNReal.ofReal (B * T * (R / a) ^ d) * palette) * M.vol) :
    μ univ ≤ (f₁.n : ℝ≥0∞) * (ENNReal.ofReal (T / F) * palette) +
        (f₂.n : ℝ≥0∞) * (ENNReal.ofReal (T / F) * palette) ∨
    ∃ (τ : Measure Ω) (t : ComparisonTable Ω D d a L (6 * B)),
      τ ≤ μ ∧ τ univ ≠ 0 ∧
      μ univ ≤ τ univ + ((f₁.n : ℝ≥0∞) * (ENNReal.ofReal (T / F) * palette) +
        (f₂.n : ℝ≥0∞) * (ENNReal.ofReal (T / F) * palette)) ∧
      t.law = τ ∧
      t.referenceTotal ≤ (f₁.n : ℝ) * (T * palette.toReal) + (f₂.n : ℝ) * (T * palette.toReal) ∧
      QuarterListBound a L d t.f₁ t.f₂ ∧
      ∃ (idx₁ : Fin t.n₁ → Fin f₁.n) (idx₂ : Fin t.n₂ → Fin f₂.n),
        Function.Injective idx₁ ∧ Function.Injective idx₂ ∧
        (∀ i, ENNReal.ofReal (T / F) * palette ≤ μ (f₁.witness (idx₁ i))) ∧
        (∀ j, ENNReal.ofReal (T / F) * palette ≤ μ (f₂.witness (idx₂ j))) ∧
        (∀ i, t.f₁ i = f₁.f (idx₁ i)) ∧ (∀ j, t.f₂ j = f₂.f (idx₂ j)) ∧
        ∀ᵐ p ∂τ, idx₁ (t.i₁ p) = f₁.index p ∧ idx₂ (t.i₂ p) = f₂.index p := by
  let fs : Fin 2 → OriginalSheetFamily μ D a K M.base signal := ![f₁, f₂]
  obtain ⟨τ, hτ, hmass, hcases⟩ := prepare_original_witness_families μ
    (fun r => (fs r).n) (fun r => (fs r).witness) (fun r => (fs r).measurable_witness)
    (fun r => (fs r).disjoint_witness) (fun r => (fs r).index) (fun r => (fs r).measurable_index)
    (fun r => (fs r).assigned) (fun _ _ => ENNReal.ofReal (T / F) * palette)
  have hmass' : μ univ ≤ τ univ + ((f₁.n : ℝ≥0∞) * (ENNReal.ofReal (T / F) * palette) +
      (f₂.n : ℝ≥0∞) * (ENNReal.ofReal (T / F) * palette)) := by
    simpa [fs, Fin.sum_univ_two, nsmul_eq_mul] using hmass
  by_cases hzero : τ univ = 0
  · left
    simpa only [hzero, zero_add] using hmass'
  · right
    obtain ⟨n', idx, current, hinj, hnum, hmeas, hfloor, hfloorOld, hcurrent⟩ := hcases.resolve_left hzero
    let t : ComparisonTable Ω D d a L (6 * B) := tableOfOriginalFamilies μ τ hτ M
      (current 0) (current 1) (hmeas 0) (hmeas 1) signal hs
      (fun i => f₁.f (idx 0 i)) (fun j => f₂.f (idx 1 j))
      (fun i => f₁.sheet _) (fun j => f₂.sheet _) K
      (fun i => f₁.lipschitz _) (fun j => f₂.lipschitz _)
      ha hB hF hT hL palette hp hpt hresolve hvolume
      (fun i => f₁.witness (idx 0 i)) (fun j => f₂.witness (idx 1 j))
      (fun i => f₁.measurable_witness _) (fun j => f₂.measurable_witness _)
      (fun i j hij => f₁.disjoint_witness (fun h => hij (hinj 0 h)))
      (fun i j hij => f₂.disjoint_witness (fun h => hij (hinj 1 h)))
      (fun i => hfloorOld 0 i) (fun j => hfloorOld 1 j)
      (fun i p hpw => ⟨(f₁.source_norm _ p hpw).trans (by norm_num), f₁.fit _ p hpw⟩)
      (fun j p hpw => ⟨(f₂.source_norm _ p hpw).trans (by norm_num), f₂.fit _ p hpw⟩)
      (by
        filter_upwards [hcurrent 0, hcurrent 1] with p h₀ h₁
        exact ⟨h₀.2, h₁.2⟩) hnative
    have hR : 0 ≤ T * palette.toReal := mul_nonneg hT.le ENNReal.toReal_nonneg
    have hnum₁ : n' 0 ≤ f₁.n := hnum 0
    have hnum₂ : n' 1 ≤ f₂.n := hnum 1
    have hreference : t.referenceTotal ≤
        (f₁.n : ℝ) * (T * palette.toReal) + (f₂.n : ℝ) * (T * palette.toReal) := by
      change (∑ _i : Fin (n' 0), T * palette.toReal) + (∑ _j : Fin (n' 1), T * palette.toReal) ≤ _
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      exact add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnum₁) hR)
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnum₂) hR)
    have hquarter : QuarterListBound a L d t.f₁ t.f₂ := by
      intro R hRa
      have hRpos : 0 < R := ha.trans_le hRa
      have hsmall : (K : ℝ) * M.diameter ≤ R := by linarith only [hresolve, hRa, ha]
      have hcount {n : ℕ} (W : Fin n → Set Ω) (hW : ∀ i, MeasurableSet (W i))
          (hdisj : Pairwise (fun i j => Disjoint (W i) (W j)))
          (f : Fin n → EuclideanSpace ℂ (Fin 3) → ℂ)
          (hfl : ∀ i, ENNReal.ofReal (T / F) * palette ≤ μ (W i))
          (hfit : ∀ i p, p ∈ W i → ‖(signal p : ℂ) - f i (emb (M.base p))‖ ≤ a / 4)
          (ref : EuclideanSpace ℂ (Fin 3) → ℂ)
          (hlip : LipschitzOnWith K (fun x => ref (emb x)) (closedBall 0 (1 / 2))) :
          ((Finset.univ.filter fun i : Fin n => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
            ‖f i (emb x) - ref (emb x)‖ ≤ R).card : ℝ) ≤ L * (R / a) ^ d := by
        have h := stored_quarter_sheet_count μ M W hW hdisj signal hs
          (fun i x => f i (emb x)) (fun x => ref (emb x)) K hlip ha hRa hB hF hT palette hp hpt
          hsmall hvolume hfl (fun i p hpw => (hfit i p hpw).trans (by linarith only [ha]))
          (hnative R hRa)
        exact h.trans (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (by positivity) _))
      constructor
      · intro i
        exact hcount (fun j => f₂.witness (idx 1 j)) (fun j => f₂.measurable_witness _)
          (fun j j' hj => f₂.disjoint_witness (fun h => hj (hinj 1 h)))
          (fun j => f₂.f (idx 1 j)) (fun j => hfloorOld 1 j)
          (fun j p hpw => f₂.fit _ p hpw) (f₁.f (idx 0 i)) (f₁.lipschitz _)
      · intro j
        exact hcount (fun i => f₁.witness (idx 0 i)) (fun i => f₁.measurable_witness _)
          (fun i i' hi => f₁.disjoint_witness (fun h => hi (hinj 0 h)))
          (fun i => f₁.f (idx 0 i)) (fun i => hfloorOld 0 i)
          (fun i p hpw => f₁.fit _ p hpw) (f₂.f (idx 1 j)) (f₂.lipschitz _)
    refine ⟨τ, t, hτ, hzero, hmass', rfl, hreference, hquarter, idx 0, idx 1, hinj 0, hinj 1,
      (fun i => hfloorOld 0 i), (fun j => hfloorOld 1 j),
      (fun _ => rfl), (fun _ => rfl), ?_⟩
    filter_upwards [hcurrent 0, hcurrent 1] with p h₀ h₁
    exact ⟨h₀.1, h₁.1⟩

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
