-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.HeightPruning.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory
open scoped ENNReal

/-- An upper bound for height mass on intervals controls all compact samples by
the lengths of their convex hulls. -/
theorem compact_height_mass_bound {μ : Measure ℝ} {L : ℝ≥0∞}
    (hμ : ∀ l u : ℝ, μ (Icc l u) ≤ L * ENNReal.ofReal (u - l))
    {S : Set ℝ} (hS : IsCompact S) :
    μ S ≤ L * ENNReal.ofReal (sSup S - sInf S) :=
  (measure_mono (subset_Icc_csInf_csSup hS.bddBelow hS.bddAbove)).trans (hμ _ _)

/-- Discarding compact samples whose spans are shorter than `a` costs at most
their number times `L*a`. The retained indices have quantitatively long hulls. -/
theorem discard_short_height_samples {I : Type*} [Fintype I]
    {μ : Measure ℝ} {L : ℝ≥0∞} {a : ℝ} (S : I → Set ℝ)
    (hS : ∀ i, IsCompact (S i))
    (hμ : ∀ l u : ℝ, μ (Icc l u) ≤ L * ENNReal.ofReal (u - l))
    {D : Set ℝ} (hcover : D ⊆ ⋃ i, S i) :
    μ (D \ ⋃ i : {i // a ≤ sSup (S i) - sInf (S i)}, S i.1) ≤
      (Fintype.card I : ℝ≥0∞) * L * ENNReal.ofReal a := by
  classical
  let bad : I → Set ℝ := fun i =>
    if a ≤ sSup (S i) - sInf (S i) then ∅ else S i
  have hsub : (D \ ⋃ i : {i // a ≤ sSup (S i) - sInf (S i)}, S i.1) ⊆
      ⋃ i, bad i := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hz.1)
    have hshort : ¬ a ≤ sSup (S i) - sInf (S i) := by
      intro hlong
      exact hz.2 (mem_iUnion.mpr ⟨⟨i, hlong⟩, hi⟩)
    exact mem_iUnion.mpr ⟨i, by simpa [bad, hshort] using hi⟩
  have hbad : ∀ i, μ (bad i) ≤ L * ENNReal.ofReal a := by
    intro i
    by_cases hi : a ≤ sSup (S i) - sInf (S i)
    · simp [bad, hi]
    · simp only [bad, if_neg hi]
      exact (compact_height_mass_bound hμ (hS i)).trans
        (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (le_of_lt (not_le.mp hi))))
  calc
    μ (D \ ⋃ i : {i // a ≤ sSup (S i) - sInf (S i)}, S i.1)
        ≤ μ (⋃ i, bad i) := measure_mono hsub
    _ ≤ ∑ i, μ (bad i) := measure_iUnion_fintype_le μ bad
    _ ≤ ∑ _i : I, L * ENNReal.ofReal a := Finset.sum_le_sum (fun i _ => hbad i)
    _ = (Fintype.card I : ℝ≥0∞) * L * ENNReal.ofReal a := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem long_height_sample_nonempty {S : Set ℝ} {a : ℝ}
    (ha : 0 < a) (h : a ≤ sSup S - sInf S) : S.Nonempty := by
  by_contra hne
  have he := not_nonempty_iff_eq_empty.mp hne
  simp only [he, Real.sSup_empty, Real.sInf_empty, sub_self] at h
  exact (not_le.mpr ha) h

/-- Errors from finitely many height selections add, even when their retained
sets and their boundaries overlap. -/
theorem measure_simultaneous_height_selection {K : Type*} [Fintype K]
    (μ : Measure ℝ) (D : Set ℝ) (U : K → Set ℝ) (e : K → ℝ≥0∞)
    (herr : ∀ k, μ (D \ U k) ≤ e k) :
    μ D ≤ μ (D ∩ ⋂ k, U k) + ∑ k, e k := by
  classical
  have hsub : D ⊆ (D ∩ ⋂ k, U k) ∪ ⋃ k, D \ U k := by
    intro z hz
    by_cases hgood : z ∈ ⋂ k, U k
    · exact Or.inl ⟨hz, hgood⟩
    · right
      simp only [mem_iInter] at hgood
      push Not at hgood
      obtain ⟨k, hk⟩ := hgood
      exact mem_iUnion.mpr ⟨k, hz, hk⟩
  calc
    μ D ≤ μ ((D ∩ ⋂ k, U k) ∪ ⋃ k, D \ U k) := measure_mono hsub
    _ ≤ μ (D ∩ ⋂ k, U k) + μ (⋃ k, D \ U k) := measure_union_le _ _
    _ ≤ μ (D ∩ ⋂ k, U k) + ∑ k, μ (D \ U k) :=
      add_le_add le_rfl (measure_iUnion_fintype_le μ _)
    _ ≤ μ (D ∩ ⋂ k, U k) + ∑ k, e k :=
      add_le_add le_rfl (Finset.sum_le_sum (fun k _ => herr k))

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
