import Submission.Obl.k4_clean_cover_graph_atlas.PacketSheetFamily
import Submission.Obl.k4_clean_cover_graph_atlas.SampleInput

namespace Submission.Obl.k4_clean_cover_graph_atlas
open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The four coordinates shared by entries of one group. -/
theorem entryGroup_parts {n C s₀ K : ℕ} (old : Fin n → Fin C) {e : Entry n s₀ K}
    {G : Group C s₀ K} (he : entryGroup old e = G) :
    old e.1 = G.1 ∧ e.2.1 = G.2.1 ∧ e.2.2.1 = G.2.2.1 ∧ e.2.2.2.2 = G.2.2.2 := by
  exact ⟨congrArg Prod.fst he, congrArg (fun G => G.2.1) he,
    congrArg (fun G => G.2.2.1) he, congrArg (fun G => G.2.2.2) he⟩

/-- Every line assigned to an entry of the group, including entries later discarded. -/
def groupLineMembers {n C s₀ K : ℕ} (old : Fin n → Fin C)
    (R' : Fin n → MvPolynomial (Fin 4) ℝ) (A' : Fin n → Set (ℕ × (Fin 6 → ℝ)))
    (j : Fin C → ℕ) (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C → MvPolynomial (Fin 4) ℝ)
    (Ti : ℕ) (G : Group C s₀ K) : Set (ℕ × (Fin 6 → ℝ)) :=
  {l | ∃ e : Entry n s₀ K, entryGroup old e = G ∧ l ∈ memE old R' A' j c u Q R Ti s₀ K e}

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

/-- A candidate entry of the actual finite sample has one comparison sheet,
selected from any retained incidence of that entry. -/
theorem candidate_sheet_of_sampleInput {Csheet : ℕ} (hsheets : PacketSheetFamilyAt Csheet)
    (hNk : 0 < Nk)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (e : Entry n s₀ K) {Abound : ℝ} (hAbound : 2 ≤ Abound)
    (hUA : 4 * Nk ^ (4 * ρ * gain * L + 4 * ε) ≤ Abound) (hκA : κ + 1 ≤ Abound)
    (hδ1 : δ Nk (r i + h * L) ≤ 1)
    (hcoeff : ∀ d,
      |(qbPoly (normPoly (T i) (j (old e.1)) (c (old e.1)) (u (old e.1)) (Q (old e.1))
          (B (γ (old e.1))) (R' e.1)) *
        qbPoly (normPoly (T i) (j (old e.1)) (c (old e.1)) (u (old e.1)) (Q (old e.1))
          (B (γ (old e.1))) (R' e.1)) -
        MvPolynomial.C (2 * qc (normPoly (T i) (j (old e.1)) (c (old e.1)) (u (old e.1))
          (Q (old e.1)) (B (γ (old e.1))) (R' e.1))) *
        qcPoly (normPoly (T i) (j (old e.1)) (c (old e.1)) (u (old e.1)) (Q (old e.1))
          (B (γ (old e.1))) (R' e.1))).coeff d| ≤ Abound)
    (hside : side s₀ * (κ + 2) ≤ (Abound ^ (-(Csheet : ℝ)) / 128) / 2)
    (p0 : (ℕ × (Fin 6 → ℝ)) × ℝ) (hpV : p0 ∈ V e.1)
    (hpm : p0.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e)
    (hpt : p0.2 ∈ subBlock (T i) s₀ (j (old e.1)) e.2.1) :
    ∃ (flat : Bool) (Fs : RealSheet 2) (sanchor : ℝ),
      PacketLineSheetCertificate Csheet Abound (Nk ^ (4 * ρ * gain * L + 4 * ε))
        (δ Nk (r i + h * L)) (T i) (j (old e.1)) s₀ e.2.1 (c (old e.1)) (u (old e.1))
        (Q (old e.1)) (B (γ (old e.1))) (R' e.1) (boxOf K e.2.2.1)
        (memE old R' A' j c u Q R (T i) s₀ K e) p0.1 p0.2 flat Fs sanchor := by
  obtain ⟨hscalar, _, _, _, _, _, _, hentry, _⟩ := hsi
  obtain ⟨hlv, _, hdeg, _, _, hA'A, _, htests, _, hVsub, _⟩ := hentry e.1
  have hchart := (hpath.2.2.2.2.2.2.2 (old e.1)).2.2
  rw [hlv] at hchart
  have hB : 0 < B (γ (old e.1)) := (hscalar.2.2.2 (γ (old e.1))).2.1
  apply hsheets hchart hB (R' e.1) hdeg hAbound (Real.rpow_pos_of_pos hNk _) hUA hκA
    (gδ_pos Nk _) hδ1 hcoeff (boxOf K e.2.2.1) e.2.1.isLt hside
    (memE old R' A' j c u Q R (T i) s₀ K e) ?_ ?_ p0.1 p0.2 hpm hpt
    (hVsub hpV).2.2.2 ?_
  · intro l hl
    obtain ⟨hlA, hlbox⟩ := memE_subset_inBox old R' A' j c u Q R (T i) s₀ K hl
    exact ⟨hA'A hlA, hlbox⟩
  · intro l hl t ht
    have htest := htests l hl.1 t ht
    exact ⟨htest.1, htest.2.1⟩
  · intro l hl
    exact hl.2.2.1.trans hpm.2.2.1.symm

/-- One old reference sheet fits every entry of its group. Its anchor is one actual
retained incidence, and its branch is the group's true-polynomial midpoint bit. -/
theorem old_reference_sheet_of_sampleInput {Csheet : ℕ} (hsheets : PacketSheetFamilyAt Csheet)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (G : Group C s₀ K) {Abound : ℝ} (hAbound : 2 ≤ Abound)
    (hκ4A : 4 * κ ≤ Abound) (hκA : κ + 1 ≤ Abound) (hδ1 : δ Nk (r i) ≤ 1)
    (hcoeff : ∀ d,
      |(qbPoly (normPoly (T i) (j G.1) (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R G.1)) *
        qbPoly (normPoly (T i) (j G.1) (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R G.1)) -
        MvPolynomial.C (2 * qc (normPoly (T i) (j G.1) (c G.1) (u G.1) (Q G.1)
          (B (γ G.1)) (R G.1))) *
        qcPoly (normPoly (T i) (j G.1) (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R G.1))).coeff d| ≤ Abound)
    (hside : side s₀ * (κ + 2) ≤ (Abound ^ (-(Csheet : ℝ)) / 128) / 2)
    (e0 : Entry n s₀ K) (he0 : entryGroup old e0 = G)
    (p0 : (ℕ × (Fin 6 → ℝ)) × ℝ) (hpV : p0 ∈ V e0.1)
    (hpm : p0.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e0)
    (hpt : p0.2 ∈ subBlock (T i) s₀ (j G.1) G.2.1) :
    ∃ (flat : Bool) (Fs : RealSheet 2) (sanchor : ℝ),
      PacketLineSheetCertificate Csheet Abound κ (δ Nk (r i)) (T i) (j G.1) s₀ G.2.1
        (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R G.1) (boxOf K G.2.2.1)
        (groupLineMembers old R' A' j c u Q R (T i) G) p0.1 p0.2 flat Fs sanchor := by
  obtain ⟨hscalar, _, _, _, _, _, _, hentry, _⟩ := hsi
  have he0old := (entryGroup_parts old he0).1
  have hlv : lev G.1 = i := by rw [← he0old]; exact (hentry e0.1).1
  have hchart := (hpath.2.2.2.2.2.2.2 G.1).2.2
  rw [hlv] at hchart
  have hchart_keep := hchart
  obtain ⟨_, _, _, _, hdeg, _, _, _, _, hAtests, hFsub, _⟩ := hchart
  have hB : 0 < B (γ G.1) := (hscalar.2.2.2 (γ G.1)).2.1
  have hκ : 0 < κ := lt_of_lt_of_le zero_lt_one hpath.1
  let S := groupLineMembers old R' A' j c u Q R (T i) G
  have hS (l : ℕ × (Fin 6 → ℝ)) (hl : l ∈ S) :
      l ∈ A G.1 ∧ inBox s₀ (boxOf K G.2.2.1) (zc (Q G.1) (c G.1) (u G.1) l
        (subMid (T i) s₀ (j G.1) G.2.1)) := by
    obtain ⟨e, heG, hmem⟩ := hl
    obtain ⟨heold, hejj, hek, _⟩ := entryGroup_parts old heG
    obtain ⟨_, _, _, _, _, hA'A, _⟩ := hentry e.1
    obtain ⟨hA', hbox⟩ := memE_subset_inBox old R' A' j c u Q R (T i) s₀ K hmem
    constructor
    · rw [← heold]
      exact hA'A hA'
    · simpa only [heold, hejj, hek] using hbox
  have hbits (l : ℕ × (Fin 6 → ℝ)) (hl : l ∈ S) :
      decide (0 ≤ eval (gx l (subMid (T i) s₀ (j G.1) G.2.1)) (pderiv 3 (R G.1))) = G.2.2.2 := by
    obtain ⟨e, heG, hmem⟩ := hl
    obtain ⟨heold, hejj, _, hetrue⟩ := entryGroup_parts old heG
    have hb := hmem.2.2.2
    change decide (0 ≤ eval (gx l (subMid (T i) s₀ (j (old e.1)) e.2.1))
      (pderiv 3 (R (old e.1)))) = e.2.2.2.2 at hb
    simpa only [heold, hejj, hetrue] using hb
  have hpS : p0.1 ∈ S := ⟨e0, he0, hpm⟩
  have hpF : p0 ∈ F G.1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hVsub, _⟩ := hentry e0.1
    rw [← he0old]
    exact (hVsub hpV).1
  apply hsheets hchart_keep hB (R G.1) hdeg hAbound hκ hκ4A hκA (gδ_pos Nk _) hδ1 hcoeff
    (boxOf K G.2.2.1) G.2.1.isLt hside S hS ?_ p0.1 p0.2 hpS hpt
    (hFsub p0 hpF).2.2.2 ?_
  · intro l hl t ht
    have hh := (hAtests l (hS l hl).1).2.2 t ht
    exact ⟨hh.2.1, hh.2.2.1⟩
  · intro l hl
    exact (hbits l hl).trans (hbits p0.1 hpS).symm

end
end Submission.Obl.k4_clean_cover_graph_atlas
