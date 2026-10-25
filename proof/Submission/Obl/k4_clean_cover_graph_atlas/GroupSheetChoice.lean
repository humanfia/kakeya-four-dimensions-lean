import Submission.Obl.k4_clean_cover_graph_atlas.SampleSheetFamily

namespace Submission.Obl.k4_clean_cover_graph_atlas
open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- Discriminant of a hidden test in its old packet's normalized coordinates. -/
noncomputable def packetDiscriminant (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  let Pb := normPoly T j c u Q B P
  qbPoly Pb * qbPoly Pb - MvPolynomial.C (2 * qc Pb) * qcPoly Pb

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

/-- Choose the candidate sheets of all active entries and one common old
reference sheet of their group. Every choice has an actual retained anchor. -/
theorem exists_sample_group_sheets {Csheet : ℕ} (hsheets : PacketSheetFamilyAt Csheet)
    (hNk : 0 < Nk)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (G : Group C s₀ K) (act : Finset (Entry n s₀ K)) (hact : act.Nonempty)
    (hgroup : ∀ e ∈ act, entryGroup old e = G)
    (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcov : ∀ e ∈ act, ∀ p ∈ cov e, p ∈ V e.1 ∧
      p.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e ∧ p.2 ∈ subBlock (T i) s₀ (j G.1) G.2.1)
    (hnonempty : ∀ e ∈ act, (cov e).Nonempty)
    {Abound : ℝ} (hAbound : 2 ≤ Abound)
    (hUA : 4 * Nk ^ (4 * ρ * gain * L + 4 * ε) ≤ Abound)
    (hκ4A : 4 * κ ≤ Abound) (hκA : κ + 1 ≤ Abound)
    (hδfine1 : δ Nk (r i + h * L) ≤ 1) (hδold1 : δ Nk (r i) ≤ 1)
    (hdiscFine : ∀ e ∈ act, ∀ d,
      |(packetDiscriminant (T i) (j G.1) (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R' e.1)).coeff d| ≤ Abound)
    (hdiscOld : ∀ d,
      |(packetDiscriminant (T i) (j G.1) (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R G.1)).coeff d| ≤ Abound)
    (hside : side s₀ * (κ + 2) ≤ (Abound ^ (-(Csheet : ℝ)) / 128) / 2) :
    ∃ (anchor : Entry n s₀ K → (ℕ × (Fin 6 → ℝ)) × ℝ)
      (flat : Entry n s₀ K → Bool) (Fs : Entry n s₀ K → RealSheet 2)
      (σfine : Entry n s₀ K → ℝ) (pold : (ℕ × (Fin 6 → ℝ)) × ℝ)
      (oldFlat : Bool) (F0 : RealSheet 2) (σold : ℝ),
      (∀ e ∈ act, anchor e ∈ cov e ∧
        PacketLineSheetCertificate Csheet Abound (Nk ^ (4 * ρ * gain * L + 4 * ε))
          (δ Nk (r i + h * L)) (T i) (j G.1) s₀ G.2.1 (c G.1) (u G.1) (Q G.1) (B (γ G.1))
          (R' e.1) (boxOf K G.2.2.1) (memE old R' A' j c u Q R (T i) s₀ K e)
          (anchor e).1 (anchor e).2 (flat e) (Fs e) (σfine e)) ∧
      PacketLineSheetCertificate Csheet Abound κ (δ Nk (r i)) (T i) (j G.1) s₀ G.2.1
        (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R G.1) (boxOf K G.2.2.1)
        (groupLineMembers old R' A' j c u Q R (T i) G) pold.1 pold.2 oldFlat F0 σold := by
  classical
  obtain ⟨e0, he0⟩ := hact
  obtain ⟨pold, hpold⟩ := hnonempty e0 he0
  obtain ⟨hpV, hpm, hpt⟩ := hcov e0 he0 pold hpold
  obtain ⟨oldFlat, F0, σold, hcOld⟩ := old_reference_sheet_of_sampleInput hsheets hsi hpath G
    hAbound hκ4A hκA hδold1 hdiscOld hside e0 (hgroup e0 he0) pold hpV hpm hpt
  let fallback : RealSheet 2 := localPolynomialSheet (D := 2) 0 (by simp) 0 8 (by norm_num)
  have hchoices (e : Entry n s₀ K) :
      ∃ (p0 : (ℕ × (Fin 6 → ℝ)) × ℝ) (flat : Bool) (Fs : RealSheet 2) (σfine : ℝ),
        e ∈ act → p0 ∈ cov e ∧
          PacketLineSheetCertificate Csheet Abound (Nk ^ (4 * ρ * gain * L + 4 * ε))
            (δ Nk (r i + h * L)) (T i) (j G.1) s₀ G.2.1 (c G.1) (u G.1) (Q G.1) (B (γ G.1))
            (R' e.1) (boxOf K G.2.2.1) (memE old R' A' j c u Q R (T i) s₀ K e)
            p0.1 p0.2 flat Fs σfine := by
    by_cases he : e ∈ act
    · obtain ⟨p0, hp0⟩ := hnonempty e he
      obtain ⟨hpV, hpm, hpt⟩ := hcov e he p0 hp0
      obtain ⟨heold, hejj, hebox, _⟩ := entryGroup_parts old (hgroup e he)
      have hpt' : p0.2 ∈ subBlock (T i) s₀ (j (old e.1)) e.2.1 := by
        simpa only [heold, hejj] using hpt
      obtain ⟨flat, Fs, σfine, hc⟩ := candidate_sheet_of_sampleInput hsheets hNk hsi hpath e
        hAbound hUA hκA hδfine1 (by simpa only [heold, packetDiscriminant] using hdiscFine e he) hside p0 hpV hpm hpt'
      refine ⟨p0, flat, Fs, σfine, fun _ => ⟨hp0, ?_⟩⟩
      simpa only [heold, hejj, hebox] using hc
    · exact ⟨pold, false, fallback, 1, fun hh => False.elim (he hh)⟩
  choose anchor flat Fs σfine hcert using hchoices
  exact ⟨anchor, flat, Fs, σfine, pold, oldFlat, F0, σold, hcert, hcOld⟩

end
end Submission.Obl.k4_clean_cover_graph_atlas
