import Submission.Obl.k4_clean_cover_graph_atlas.GroupSheetFits
import Submission.Obl.k4_clean_cover_graph_atlas.GroupSheetChoice
import Submission.Obl.k4_clean_cover_graph_atlas.EntryAssembly
import Submission.Obl.k4_clean_cover_graph_atlas.SelectedTestBounds

namespace Submission.Obl.k4_clean_cover_graph_atlas
open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The sheet fields consumed by the entry assembly, together with explicit
original-polynomial bounds for its selected physical tests and scales. -/
structure EntrySheetProperties {W C n Ti s₀ K : ℕ} (γ : Fin C → Fin W) (B : Fin W → ℝ)
    (j : Fin C → ℕ) (old : Fin n → Fin C)
    (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lb : Group C s₀ K → (ℕ × (Fin 6 → ℝ)) → ℝ → Real3)
    (H Abound ηfine ηold : ℝ)
    (Fe : Entry n s₀ K → RealSheet 2) (F0 : Group C s₀ K → RealSheet 2)
    (Pe : Entry n s₀ K → MvPolynomial (Fin 4) ℝ) (se : Entry n s₀ K → ℝ)
    (pe : Entry n s₀ K → Bool) : Prop where
  degree_scale : ∀ e, (cov e).Nonempty → (Pe e).totalDegree ≤ 2 ∧ 0 < se e
  roots : ∀ e, (cov e).Nonempty → ∀ l t, ‖lb (entryGroup old e) l t‖ ≤ (1 : ℝ) / 2 →
    let w := ((Fe e).f (emb (lb (entryGroup old e) l t))).re / B (γ (old e.1))
    eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (Pe e) = 0 ∧
    if pe e then
      19 / 20 * se e ≤ eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Pe e)) ∧
      eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Pe e)) ≤ 21 / 20 * se e
    else
      19 / 20 * se e ≤ -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Pe e)) ∧
      -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Pe e)) ≤ 21 / 20 * se e
  fit_times : ∀ e, ∀ p ∈ cov e, ∀ t,
    t = groupStart j Ti (entryGroup old e) ∨
      t = (groupStart j Ti (entryGroup old e) + groupEnd j Ti (entryGroup old e)) / 2 ∨
      t = groupEnd j Ti (entryGroup old e) →
    ‖lb (entryGroup old e) p.1 t‖ ≤ (1 : ℝ) / 2 ∧
      |B (γ (old e.1)) * gx p.1 t 3 - ((Fe e).f (emb (lb (entryGroup old e) p.1 t))).re| ≤ ηfine
  fit_points : ∀ e, ∀ p ∈ cov e,
    ‖lb (entryGroup old e) p.1 p.2‖ ≤ (1 : ℝ) / 2 ∧
      |B (γ (old e.1)) * gx p.1 p.2 3 - ((Fe e).f (emb (lb (entryGroup old e) p.1 p.2))).re| ≤ ηfine ∧
      |B (γ (old e.1)) * gx p.1 p.2 3 - ((F0 (entryGroup old e)).f (emb (lb (entryGroup old e) p.1 p.2))).re| ≤ ηold
  coefficients : ∀ e, (cov e).Nonempty → ∀ d,
    |(Pe e).coeff d| ≤ 2 * H ∧ |(pderiv (3 : Fin 4) (Pe e)).coeff d| ≤ 4 * H
  scales : ∀ e, (cov e).Nonempty → se e ≤ B (γ (old e.1)) * Abound + 4 * H ∧
    |qc (Pe e)| ≤ 8 * H ∧
    (se e)⁻¹ ≤ Abound / B (γ (old e.1)) + Abound ^ (20 : ℕ) / B (γ (old e.1)) ^ 2

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

/-- Construct all sheet fields of the actual finite sample. Inactive entries
and groups receive a fixed polynomial graph; every active choice has an original anchor. -/
theorem exists_sample_entry_sheets {Csheet : ℕ} (hsheets : PacketSheetFamilyAt Csheet)
    (hNk : 0 < Nk)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcov : ∀ e, ∀ p ∈ cov e, p ∈ V e.1 ∧
      p.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e ∧ p.2 ∈ subBlock (T i) s₀ (j (old e.1)) e.2.1)
    {Abound : ℝ} (hAbound : 2 ≤ Abound)
    (hUA : 4 * Nk ^ (4 * ρ * gain * L + 4 * ε) ≤ Abound)
    (hκ4A : 4 * κ ≤ Abound) (hκA : κ + 1 ≤ Abound)
    (hδfine1 : δ Nk (r i + h * L) ≤ 1) (hδold1 : δ Nk (r i) ≤ 1)
    (hdiscFine : ∀ e, (cov e).Nonempty → ∀ d,
      |(packetDiscriminant (T i) (j (old e.1)) (c (old e.1)) (u (old e.1)) (Q (old e.1))
        (B (γ (old e.1))) (R' e.1)).coeff d| ≤ Abound)
    (hdiscOld : ∀ G : Group C s₀ K, (∃ e, (cov e).Nonempty ∧ entryGroup old e = G) → ∀ d,
      |(packetDiscriminant (T i) (j G.1) (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R G.1)).coeff d| ≤ Abound)
    (hside : side s₀ * (κ + 2) ≤ (Abound ^ (-(Csheet : ℝ)) / 128) / 2) :
    let lb := fun (G : Group C s₀ K) l t => groupBase (T i) (j G.1) (c G.1) (u G.1) (Q G.1)
      (subBoxCenter s₀ G.2.1 (boxOf K G.2.2.1)) (Abound ^ (-(Csheet : ℝ)) / 128)
      (obs (B (γ G.1)) (δ Nk L) (l, t))
    ∃ (Fe : Entry n s₀ K → RealSheet 2) (F0 : Group C s₀ K → RealSheet 2)
      (Pe : Entry n s₀ K → MvPolynomial (Fin 4) ℝ) (se : Entry n s₀ K → ℝ)
      (pe : Entry n s₀ K → Bool),
      EntrySheetProperties (Ti := T i) γ B j old cov lb (Nk ^ Mg) Abound
        ((Nk ^ (4 * ρ * gain * L + 4 * ε)) * δ Nk (r i + h * L) * Abound ^ ((Csheet : ℝ) + 1))
        (κ * δ Nk (r i) * Abound ^ ((Csheet : ℝ) + 1)) Fe F0 Pe se pe := by
  classical
  let fallback : RealSheet 2 := localPolynomialSheet (D := 2) 0 (by simp) 0 8 (by norm_num)
  let pzero : (ℕ × (Fin 6 → ℝ)) × ℝ := ((0, 0), 0)
  have fineChoices (e : Entry n s₀ K) :
      ∃ (p0 : (ℕ × (Fin 6 → ℝ)) × ℝ) (flat : Bool) (Fs : RealSheet 2) (σfine : ℝ),
        (cov e).Nonempty → PacketLineSheetCertificate Csheet Abound (Nk ^ (4 * ρ * gain * L + 4 * ε))
          (δ Nk (r i + h * L)) (T i) (j (old e.1)) s₀ e.2.1 (c (old e.1)) (u (old e.1))
          (Q (old e.1)) (B (γ (old e.1))) (R' e.1) (boxOf K e.2.2.1)
          (memE old R' A' j c u Q R (T i) s₀ K e) p0.1 p0.2 flat Fs σfine := by
    by_cases he : (cov e).Nonempty
    · obtain ⟨p0, hp0⟩ := he
      obtain ⟨hpV, hpm, hpt⟩ := hcov e p0 hp0
      obtain ⟨flat, Fs, σfine, hc⟩ := candidate_sheet_of_sampleInput hsheets hNk hsi hpath e
        hAbound hUA hκA hδfine1 (hdiscFine e ⟨p0, hp0⟩) hside p0 hpV hpm hpt
      exact ⟨p0, flat, Fs, σfine, fun _ => hc⟩
    · exact ⟨pzero, false, fallback, 1, fun hh => False.elim (he hh)⟩
  choose anchor flat Fe σfine hcFine using fineChoices
  have oldChoices (G : Group C s₀ K) :
      ∃ (p0 : (ℕ × (Fin 6 → ℝ)) × ℝ) (oldFlat : Bool) (F0 : RealSheet 2) (σold : ℝ),
        (∃ e, (cov e).Nonempty ∧ entryGroup old e = G) →
          PacketLineSheetCertificate Csheet Abound κ (δ Nk (r i)) (T i) (j G.1) s₀ G.2.1
            (c G.1) (u G.1) (Q G.1) (B (γ G.1)) (R G.1) (boxOf K G.2.2.1)
            (groupLineMembers old R' A' j c u Q R (T i) G) p0.1 p0.2 oldFlat F0 σold := by
    by_cases hg : ∃ e, (cov e).Nonempty ∧ entryGroup old e = G
    · obtain ⟨e, hne, heG⟩ := hg
      obtain ⟨p0, hp0⟩ := hne
      obtain ⟨hpV, hpm, hpt⟩ := hcov e p0 hp0
      obtain ⟨heold, hejj, _, _⟩ := entryGroup_parts old heG
      rw [heold, hejj] at hpt
      obtain ⟨oldFlat, F0, σold, hc⟩ := old_reference_sheet_of_sampleInput hsheets hsi hpath G
        hAbound hκ4A hκA hδold1 (hdiscOld G ⟨e, ⟨p0, hp0⟩, heG⟩) hside e heG p0 hpV hpm hpt
      exact ⟨p0, oldFlat, F0, σold, fun _ => hc⟩
    · exact ⟨pzero, false, fallback, 1, fun hh => False.elim (hg hh)⟩
  choose oldAnchor oldFlat F0 σold hcOld using oldChoices
  let Pe := fun e : Entry n s₀ K => selectedSheetTest (flat e) (R' e.1)
  let se := fun e : Entry n s₀ K => selectedSlopeFactor (flat e) (B (γ (old e.1))) * |σfine e|
  let pe := fun e : Entry n s₀ K => decide (0 ≤ σfine e)
  have hApos : 0 < Abound := by linarith
  have hentry := hsi.2.2.2.2.2.2.2.1
  have hdata (e : Entry n s₀ K) (hne : (cov e).Nonempty) :=
    sample_entry_group_sheet_data hsi hpath e (entryGroup old e) rfl hApos hside (cov e)
      (fun p hp => (hcov e p hp).2) (anchor e) (oldAnchor (entryGroup old e))
      (flat e) (oldFlat (entryGroup old e)) (Fe e) (F0 (entryGroup old e)) (σfine e) (σold (entryGroup old e))
      (by simpa only [entryGroup] using hcFine e hne) (hcOld (entryGroup old e) ⟨e, hne, rfl⟩)
  refine ⟨Fe, F0, Pe, se, pe, ?_⟩
  constructor
  · intro e hne
    obtain ⟨_, _, hdeg, hcoef, _⟩ := hentry e.1
    exact ⟨(selectedSheetTest_original_bounds (flat e) (R' e.1) hdeg (by positivity) hcoef).1,
      (hcFine e hne).2.2.2.2.1⟩
  · intro e hne l t hhalf
    exact (hdata e hne).1 l t hhalf
  · intro e p hp t ht
    have horder : groupStart j (T i) (entryGroup old e) ≤ groupEnd j (T i) (entryGroup old e) := by
      unfold groupStart groupEnd
      apply div_le_div_of_nonneg_right (by linarith) (by positivity)
    have htime : t ∈ subBlock (T i) s₀ (j (old e.1)) e.2.1 := by
      change t ∈ Icc (groupStart j (T i) (entryGroup old e)) (groupEnd j (T i) (entryGroup old e))
      rcases ht with rfl | rfl | rfl <;> constructor <;> linarith
    have hh := (hdata e ⟨p, hp⟩).2 p hp t htime
    exact ⟨hh.1, hh.2.1⟩
  · intro e p hp
    exact (hdata e ⟨p, hp⟩).2 p hp p.2 (hcov e p hp).2.2
  · intro e hne d
    obtain ⟨_, _, hdeg, hcoef, _⟩ := hentry e.1
    exact (selectedSheetTest_original_bounds (flat e) (R' e.1) hdeg (by positivity) hcoef).2.1 d
  · intro e hne
    obtain ⟨_, _, hdeg, hcoef, _⟩ := hentry e.1
    have hB : 0 < B (γ (old e.1)) := (hsi.1.2.2.2 (γ (old e.1))).2.1
    have hs := (hcFine e hne).2.2.2.2
    refine ⟨physical_initial_scale_upper hdeg hB (by positivity) hcoef hs.2.1, ?_, hs.2.2⟩
    exact (selectedSheetTest_original_bounds (flat e) (R' e.1) hdeg (by positivity) hcoef).2.2

end
end Submission.Obl.k4_clean_cover_graph_atlas
