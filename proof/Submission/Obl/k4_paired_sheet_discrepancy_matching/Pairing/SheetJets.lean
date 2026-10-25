/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/SheetJets.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/SheetJets.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Mathlib
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.Interface
import Submission.Obl.k4_algebraic_real_jet_comparison.DirectionalComparison

/-! Finite real jets of degree-two matching sheets: linearity, finite-jet norm control,
jet upper bounds and the extension of real half-ball bounds to the real unit ball.
Everything is derived from the accepted o149 helpers. -/

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open Set Metric
open Submission.Obl.k4_algebraic_real_jet_comparison
  (HasSheetRelation realEmbedding exists_sheet_directional_comparison
    exists_sheet_norm_constant_two exists_sheet_difference_degree contDiffOn_real_line)

/-- A real-on-real holomorphic algebraic sheet of degree at most two on the matching domain. -/
def IsMatchSheet (φ : EuclideanSpace ℂ (Fin 3) → ℂ) : Prop :=
  HasSheetRelation 3 2 φ ∧ DifferentiableOn ℂ φ (ball 0 4) ∧
    ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (φ (emb x)).im = 0

/-- The real directional jet of a sheet at the center of the matching domain. -/
noncomputable def sheetJet (φ : EuclideanSpace ℂ (Fin 3) → ℂ) (v : EuclideanSpace ℝ (Fin 3))
    (j : ℕ) : ℝ :=
  iteratedDeriv j (fun t : ℝ => (φ (realEmbedding 3 0 + (t : ℂ) • realEmbedding 3 v)).re) 0

lemma realEmbedding_eq_emb (x : EuclideanSpace ℝ (Fin 3)) : realEmbedding 3 x = emb x := rfl

lemma norm_emb (x : EuclideanSpace ℝ (Fin 3)) : ‖emb x‖ = ‖x‖ :=
  (realEmbedding 3).norm_map x

lemma sheetJet_sub {φ ψ : EuclideanSpace ℂ (Fin 3) → ℂ}
    (hφ : DifferentiableOn ℂ φ (ball 0 4)) (hψ : DifferentiableOn ℂ ψ (ball 0 4))
    (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ ≤ 1) (j : ℕ) :
    iteratedDeriv j (fun t : ℝ => ((fun z => φ z - ψ z)
      (realEmbedding 3 0 + (t : ℂ) • realEmbedding 3 v)).re) 0 =
      sheetJet φ v j - sheetJet ψ v j := by
  have ha : ‖realEmbedding 3 (0 : EuclideanSpace ℝ (Fin 3))‖ ≤ (3 : ℝ) / 4 := by
    simp only [map_zero, norm_zero]; norm_num
  have hv' : ‖realEmbedding 3 v‖ ≤ 1 := by simpa only [LinearIsometry.norm_map] using hv
  have hmem : Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hF := (contDiffOn_real_line hφ (realEmbedding 3 0) (realEmbedding 3 v) ha hv'
    (j : WithTop ℕ∞)).contDiffAt hmem
  have hG := (contDiffOn_real_line hψ (realEmbedding 3 0) (realEmbedding 3 v) ha hv'
    (j : WithTop ℕ∞)).contDiffAt hmem
  have hfun : (fun t : ℝ => ((fun z => φ z - ψ z)
      (realEmbedding 3 0 + (t : ℂ) • realEmbedding 3 v)).re) =
      (fun t : ℝ => (φ (realEmbedding 3 0 + (t : ℂ) • realEmbedding 3 v)).re) -
      (fun t : ℝ => (ψ (realEmbedding 3 0 + (t : ℂ) • realEmbedding 3 v)).re) := by
    funext t
    simp only [Pi.sub_apply, Complex.sub_re]
  rw [hfun, iteratedDeriv_sub hF hG]
  rfl

/-- Uniform finite-jet constants for degree-two matching sheets. -/
theorem exists_match_jet_constants :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ c : ℝ, 0 < c ∧ ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), V.Nonempty ∧
      (∀ v ∈ V, ‖v‖ = 1) ∧ ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ φ ψ : EuclideanSpace ℂ (Fin 3) → ℂ, IsMatchSheet φ → IsMatchSheet ψ →
        (∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
          ∃ v ∈ V, ∃ j < q, c * ‖φ (emb y) - ψ (emb y)‖ ≤ |sheetJet φ v j - sheetJet ψ v j|) ∧
        (∀ A : ℝ, 0 < A → (∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
            ‖φ (emb y) - ψ (emb y)‖ ≤ A) →
          ∀ v ∈ V, ∀ j : ℕ, |sheetJet φ v j - sheetJet ψ v j| ≤ B j * A) ∧
        (∀ A : ℝ, 0 < A → (∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
            ‖φ (emb y) - ψ (emb y)‖ ≤ A) →
          ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 → ‖φ (emb y) - ψ (emb y)‖ ≤ C₂ * A) := by
  obtain ⟨E, hE⟩ := exists_sheet_difference_degree 3 2
  obtain ⟨q, hq, c, hc, V, hVne, hV, B, hB, hcomp⟩ := exists_sheet_directional_comparison E
  obtain ⟨C₂, hC₂, hext⟩ := exists_sheet_norm_constant_two 3 E
  refine ⟨q, hq, c, hc, V, hVne, hV, B, hB, C₂, hC₂, ?_⟩
  intro φ ψ hφ hψ
  obtain ⟨hφrel, hφd, hφr⟩ := hφ
  obtain ⟨hψrel, hψd, hψr⟩ := hψ
  set h : EuclideanSpace ℂ (Fin 3) → ℂ := fun z => φ z - ψ z with hh
  have hrel : HasSheetRelation 3 E h := hE φ ψ hφrel hψrel
  have hd : DifferentiableOn ℂ h (ball 0 4) := hφd.sub hψd
  have hreal : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (h (realEmbedding 3 x)).im = 0 := by
    intro x hx
    simp only [hh, Complex.sub_im, realEmbedding_eq_emb, hφr x hx, hψr x hx, sub_zero]
  obtain ⟨hup, hlow⟩ := hcomp h hrel hd hreal
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨v, hv, j, hj, hle⟩ := hlow 0 y (by simp only [norm_zero]; norm_num) hy
    refine ⟨v, hv, j, hj, ?_⟩
    rw [← sheetJet_sub hφd hψd v (hV v hv).le j]
    simpa only [realEmbedding_eq_emb] using hle
  · intro A hA hbase v hv j
    have := hup A hA (fun y hy => by simpa only [realEmbedding_eq_emb] using hbase y hy)
      0 v (by simp only [norm_zero]; norm_num) (hV v hv).le j
    rw [← sheetJet_sub hφd hψd v (hV v hv).le j]
    exact this
  · intro A hA hbase y hy
    have := hext h hrel hd A hA (fun x hx => hbase x hx) (emb y)
      (by rw [norm_emb]; linarith)
    exact this

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
