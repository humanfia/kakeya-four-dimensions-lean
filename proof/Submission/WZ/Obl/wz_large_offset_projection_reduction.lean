-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_large_offset_projection_reduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_extreme_offset_fibre_estimate
import Submission.WZ.Obl.wz_compact_offset_normalization
import Submission.WZ.Obl.wz_small_twist_projection_estimate
import Submission.WZ.Obl.wz_intermediate_twist_normalization

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_large_offset_projection_reduction

abbrev Space := LeanEval.Analysis.WangZahlKakeya.Space

abbrev Tube (δ : ℝ) (x v : Space) : Set Space :=
  Metric.thickening δ (segment ℝ x (x + v))

abbrev FamilyHyp (η δ : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1) ∧
  (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) ∧
  (∀ i j, i ≠ j →
    MeasureTheory.volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1/2 : ENNReal) * MeasureTheory.volume (Tube δ (x i) (v i))) ∧
  (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ Tube δ (x i) (v i)) ∧
  ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤
    Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i))

abbrev ConvexCount (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
      ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * MeasureTheory.volume W

abbrev SlopeHyp (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 →
    1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧
      |deriv (deriv f) z| ≤ (1/100 : ℝ)

abbrev Projection (f : ℝ → ℝ) (E : Set Space) : Set (ℝ × ℝ) :=
  (fun p : Space => (p 0 + f (p 2) * p 1, p 2)) '' E

abbrev Estimate (R : ℝ → ℝ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
  ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) →
  ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    FamilyHyp η δ n x v Y → (∀ i, (1/2 : ℝ) ≤ |v i 2|) →
    ConvexCount η δ n x v → ∀ f : ℝ → ℝ, SlopeHyp f → R δ (f 0) →
      ENNReal.ofReal (δ ^ ε) ≤ MeasureTheory.volume (Projection f (⋃ i, Y i))

/-- Increasing the permitted error exponent weakens both family assumptions. -/
theorem hypotheses_mono {δ η η' : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    (hH : FamilyHyp η δ n x v Y) (hF : ConvexCount η δ n x v) :
    FamilyHyp η' δ n x v Y ∧ ConvexCount η' δ n x v := by
  have hmass : δ ^ η' ≤ δ ^ η :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη
  have hcount : δ ^ (-η) ≤ δ ^ (-η') :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη)
  constructor
  · rcases hH with ⟨hn, hv, hball, hsep, hmeas, hsub, hdense⟩
    refine ⟨hn, hv, hball, hsep, hmeas, hsub, le_trans ?_ hdense⟩
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmass (Nat.cast_nonneg n)) (sq_nonneg δ)
  · intro W hW
    refine le_trans (hF W hW) ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg n))) _

end WangZahlLot.Obl.wz_large_offset_projection_reduction

open WangZahlLot.Obl.wz_large_offset_projection_reduction

theorem WangZahlLot.wz_large_offset_projection_reduction : (fun T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop) (F : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) (N : (ℝ → ℝ) → Prop) (P : (ℝ → ℝ) → Set LeanEval.Analysis.WangZahlKakeya.Space → Set (ℝ × ℝ)) => (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y → (∀ i, (1/2 : ℝ) ≤ |v i 2|) → F η δ n x v → ∀ f : ℝ → ℝ, N f → |f 0| ≤ 1 → ENNReal.ofReal (δ ^ ε) ≤ MeasureTheory.volume (P f (⋃ i, Y i))) → (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y → (∀ i, (1/2 : ℝ) ≤ |v i 2|) → F η δ n x v → ∀ f : ℝ → ℝ, N f → 1 < |f 0| → ENNReal.ofReal (δ ^ ε) ≤ MeasureTheory.volume (P f (⋃ i, Y i)))) (fun η δ n x v Y => 0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, T δ (x i) (v i) ⊆ Metric.ball 0 1) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) ∧ (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ T δ (x i) (v i)) ∧ ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i))) (fun η δ n x v => ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * MeasureTheory.volume W) (fun f : ℝ → ℝ => ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → 1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ)) (fun (f : ℝ → ℝ) (E : Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun p : LeanEval.Analysis.WangZahlKakeya.Space => (p 0 + f (p 2) * p 1, p 2)) '' E)) (fun (δ : ℝ) (x v : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening δ (segment ℝ x (x + v))) := by
  change Estimate (fun _ c => |c| ≤ 1) → Estimate (fun _ c => 1 < |c|)
  intro hB ε hε
  have hcompact : Estimate (fun _ c => 1 < |c| ∧ |c| ≤ 100) :=
    WangZahlLot.wz_compact_offset_normalization hB
  have hlinear : Estimate (fun δ c =>
      100 < |c| ∧ 1 ≤ δ * c ^ 2 ∧ |c| < 2 + 6 / δ) :=
    WangZahlLot.wz_small_twist_projection_estimate
  have htwist : Estimate (fun δ c => 100 < |c| ∧ δ * c ^ 2 < 1) :=
    WangZahlLot.wz_intermediate_twist_normalization hB
  obtain ⟨ηb, hηb, db, hdb, hb⟩ := hcompact ε hε
  obtain ⟨ηl, hηl, dl, hdl, hl⟩ := hlinear ε hε
  obtain ⟨ηt, hηt, dt, hdt, ht⟩ := htwist ε hε
  let η := min ε (min ηb (min ηl ηt))
  let d0 := min db (min dl dt)
  have hη : 0 < η := lt_min hε (lt_min hηb (lt_min hηl hηt))
  have hd0 : 0 < d0 := lt_min hdb (lt_min hdl hdt)
  have hηε : η ≤ ε := min_le_left _ _
  have hηb' : η ≤ ηb := (min_le_right _ _).trans (min_le_left _ _)
  have hηl' : η ≤ ηl :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηt' : η ≤ ηt :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨η, hη, d0, hd0, ?_⟩
  intro δ hδ hδd hδsmall n x v Y hH htrans hF f hf hoff
  have hδ1 : δ ≤ 1 := le_trans hδsmall (by norm_num)
  by_cases hextreme : 2 + 6 / δ ≤ |f 0|
  · exact WangZahlLot.wz_extreme_offset_fibre_estimate ε η δ hδ hδ1 hηε
      n x v Y hH htrans f hf hextreme
  have hnotextreme : |f 0| < 2 + 6 / δ := lt_of_not_ge hextreme
  by_cases hbound : |f 0| ≤ 100
  · obtain ⟨hHb, hFb⟩ := hypotheses_mono hδ hδ1 hηb' hH hF
    exact hb δ hδ (hδd.trans (min_le_left _ _)) hδsmall
      n x v Y hHb htrans hFb f hf ⟨hoff, hbound⟩
  have hlarge : 100 < |f 0| := lt_of_not_ge hbound
  by_cases hsmalltwist : 1 ≤ δ * (f 0) ^ 2
  · obtain ⟨hHl, hFl⟩ := hypotheses_mono hδ hδ1 hηl' hH hF
    have hδl : δ ≤ dl :=
      hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
    exact hl δ hδ hδl hδsmall n x v Y hHl htrans hFl f hf
      ⟨hlarge, hsmalltwist, hnotextreme⟩
  · obtain ⟨hHt, hFt⟩ := hypotheses_mono hδ hδ1 hηt' hH hF
    have hδt : δ ≤ dt :=
      hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
    exact ht δ hδ hδt hδsmall n x v Y hHt htrans hFt f hf
      ⟨hlarge, lt_of_not_ge hsmalltwist⟩
