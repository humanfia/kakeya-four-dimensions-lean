-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/GroupSheetFits.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.SampleSheetFamily

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets
section
variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
  {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
  {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {κ : ℝ} {C : ℕ}
  {lev : Fin C → ℕ} {par : Fin C → Fin C} {γ : Fin C → Fin W} {j : Fin C → ℕ}
  {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
  {R : Fin C → MvPolynomial (Fin 4) ℝ} {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
  {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)}

variable {Mpr Dpr Mg Dg : ℕ} {d₁ ρ gain τ ε : ℝ} {n : ℕ} {old : Fin n → Fin C}
  {R' : Fin n → MvPolynomial (Fin 4) ℝ} {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))}
  {V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {q : ℝ} {i : ℕ} {h : ℝ} {s₀ K : ℕ}

/-- The concrete candidate and old certificates supply the roots and every
whole-subblock fit needed by group recovery, in the common group coordinates. -/
theorem sample_entry_group_sheet_data {Csheet : ℕ} {Abound Ufine δfine : ℝ}
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (e : Entry n s₀ K) (G : Group C s₀ K) (heG : entryGroup old e = G) (hA : 0 < Abound)
    (hside : side s₀ * (κ + 2) ≤ (Abound ^ (-(Csheet : ℝ)) / 128) / 2)
    (cov : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcov : ∀ p ∈ cov, p.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e ∧
      p.2 ∈ subBlock (T i) s₀ (j G.1) G.2.1)
    (pfine pold : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (flat oldFlat : Bool) (Fs F0 : RealSheet 2) (σfine σold : ℝ)
    (hcFine : PacketLineSheetCertificate Csheet Abound Ufine δfine (T i) (j G.1) s₀ G.2.1
      (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R' e.1) (boxOf K G.2.2.1)
      (memE old R' A' j c u Q R (T i) s₀ K e) pfine.1 pfine.2 flat Fs σfine)
    (hcOld : PacketLineSheetCertificate Csheet Abound κ (δ Nk (r i)) (T i) (j G.1) s₀ G.2.1
      (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R G.1) (boxOf K G.2.2.1)
      (groupLineMembers old R' A' j c u Q R (T i) G) pold.1 pold.2 oldFlat F0 σold) :
    let lbase := fun l t => groupBase (T i) (j G.1) (c G.1) (u G.1) (Q G.1)
      (subBoxCenter s₀ G.2.1 (boxOf K G.2.2.1)) (Abound ^ (-(Csheet : ℝ)) / 128)
      (obs (B (γ G.1)) (δ Nk L) (l, t))
    let sc := selectedSlopeFactor flat (B (γ G.1)) * |σfine|
    (∀ l t, ‖lbase l t‖ ≤ (1 : ℝ) / 2 →
      let w := (Fs.f (emb (lbase l t))).re / B (γ G.1)
      eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (selectedSheetTest flat (R' e.1)) = 0 ∧
      if decide (0 ≤ σfine) then
        19 / 20 * sc ≤ eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ)
          (pderiv 3 (selectedSheetTest flat (R' e.1))) ∧
        eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ)
          (pderiv 3 (selectedSheetTest flat (R' e.1))) ≤ 21 / 20 * sc
      else
        19 / 20 * sc ≤ -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ)
          (pderiv 3 (selectedSheetTest flat (R' e.1))) ∧
        -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ)
          (pderiv 3 (selectedSheetTest flat (R' e.1))) ≤ 21 / 20 * sc) ∧
    (∀ p ∈ cov, ∀ t ∈ subBlock (T i) s₀ (j G.1) G.2.1,
      ‖lbase p.1 t‖ ≤ (1 : ℝ) / 2 ∧
      |B (γ G.1) * gx p.1 t 3 - (Fs.f (emb (lbase p.1 t))).re| ≤
        Ufine * δfine * Abound ^ ((Csheet : ℝ) + 1) ∧
      |B (γ G.1) * gx p.1 t 3 - (F0.f (emb (lbase p.1 t))).re| ≤
        κ * δ Nk (r i) * Abound ^ ((Csheet : ℝ) + 1)) := by
  obtain ⟨heold, hejj, hebox, _⟩ := entryGroup_parts old heG
  have hlv : lev G.1 = i := by
    rw [← heold]
    exact (hsi.2.2.2.2.2.2.2.1 e.1).1
  have hchart := (hpath.2.2.2.2.2.2.2 G.1).2.2
  rw [hlv] at hchart
  have hB : 0 < B (γ G.1) := (hsi.1.2.2.2 (γ G.1)).2.1
  have hradius : 0 < Abound ^ (-(Csheet : ℝ)) / 128 := by positivity
  refine ⟨?_, ?_⟩
  · intro l t hhalf
    exact hcFine.physical_roots hA hchart.1 hB (δ Nk L) l t hhalf
  · intro p hp t ht
    obtain ⟨hmem, _⟩ := hcov p hp
    obtain ⟨hA', hbox⟩ := memE_subset_inBox old R' A' j c u Q R (T i) s₀ K hmem
    have hA'A : A' e.1 ⊆ A (old e.1) := by
      obtain ⟨_, _, _, _, _, hs, _⟩ := hsi.2.2.2.2.2.2.2.1 e.1
      exact hs
    have hpA : p.1 ∈ A G.1 := by rw [← heold]; exact hA'A hA'
    rw [heold, hejj, hebox] at hbox
    refine ⟨groupBase_mem_halfBall (s₀ := s₀) (jj := G.2.1) (k := boxOf K G.2.2.1)
      (p := (p.1, t)) hchart hradius hside hpA hbox ht (B (γ G.1)) (δ Nk L), ?_, ?_⟩
    · exact hcFine.fit_at_observation (B (γ G.1)) (δ Nk L) hmem ht
    · exact hcOld.fit_at_observation (B (γ G.1)) (δ Nk L) ⟨e, heG, hmem⟩ ht

end
end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
