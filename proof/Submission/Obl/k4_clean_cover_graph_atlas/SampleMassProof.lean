import Submission.Obl.k4_clean_cover_graph_atlas.SampleMassData
import Submission.Obl.k4_clean_cover_graph_atlas.SamplePruning
import Submission.Obl.k4_clean_cover_graph_atlas.SampleCapSums
import Submission.Obl.k4_clean_cover_graph_atlas.SampleWeightedCap

namespace Submission.Obl.k4_clean_cover_graph_atlas
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


open Classical in
/-- Construct the complete original-law mass data for one finite sample. The
covered entries keep their original world weights, and the common cap sum is
charged to the full old packet budget. -/
theorem sampleInput_mass_data
    (hNk : 1 ≤ Nk) (hL : 0 < L) (hgain : 0 < gain)
    (hd₁ : 0 ≤ d₁) (hd₁1 : d₁ ≤ 1) (hρ : 0 ≤ ρ) (hδ₀ : 0 ≤ δ₀)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hδρ : δ₀ ≤ ρ * gain)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hlin : ∀ q, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L)
    {Abound : ℝ} {Cs : ℕ} (hA : 0 < Abound)
    (hs : (2 : ℝ) ^ s₀ ≤ 2 * (256 * (κ + 2) * Abound ^ (Cs : ℝ)))
    (hKlo : κ * (2 : ℝ) ^ s₀ ≤ K) (hKhi : (K : ℝ) ≤ κ * (2 : ℝ) ^ s₀ + 1)
    (hlight : 4 * Nk ^ (-ε - τ) ≤ Nk ^ (-ε) / 64) :
    let ob := fun G : Group C s₀ K => groupBase (T i) (j G.1) (c G.1) (u G.1) (Q G.1)
      (subBoxCenter s₀ G.2.1 (boxOf K G.2.2.1)) (sheetRadius Abound Cs)
    ∃ (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (H : Group C s₀ K → ℝ),
      (∀ G, 0 < H G) ∧
      (∀ e, MeasurableSet (cov e)) ∧
      (∀ e, ∀ p ∈ cov e, p ∈ V e.1 ∧
        p.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e ∧
        p.2 ∈ subBlock (T i) s₀ (j (old e.1)) e.2.1) ∧
      (∀ e e', e ≠ e' → γ (old e.1) = γ (old e'.1) → Disjoint (cov e) (cov e')) ∧
      (∀ e, (cov e).Nonempty →
        (ENNReal.ofReal (ω (γ (old e.1))) • ((ν (γ (old e.1))).prod volume).restrict (cov e)).map
          (ob (entryGroup old e) ∘ obs (B (γ (old e.1))) (δ Nk L)) ≤
            ENNReal.ofReal (H (entryGroup old e)) • volume) ∧
      (∀ e, (cov e).Nonempty →
        ENNReal.ofReal (H (entryGroup old e) * groupFloor Nk (slackTot ρ gain L ε σ τ)) ≤
          ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e)) ∧
      ENNReal.ofReal (Nk ^ (-ε) / 4) ≤
        (∑ e, ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e)) ∧
      (∑ e, if (cov e).Nonempty then ENNReal.ofReal (H (entryGroup old e)) else 0) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (23 : ℕ) *
          Nk ^ (((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ) + 6 * σ)) := by
  classical
  dsimp only
  obtain ⟨cov, hcovm, hcov, hdisj, hheavy, htotal⟩ :=
    sampleInput_pruned_entries hNk hsi hpath hKlo hlight
  obtain ⟨H, hH, hHeq, hsum⟩ := sampleInput_common_caps_sum hNk hL hgain hd₁ hd₁1
    hρ hδ₀ hε hsi hpath hlin hA hs hKhi cov (fun e he => (hheavy e he).1)
  refine ⟨cov, H, hH, hcovm, hcov, hdisj, ?_, ?_, htotal, hsum⟩
  · intro e he
    rw [hHeq e he]
    have hQ : (Q (old e.1)).det ≠ 0 := ((hpath.2.2.2.2.2.2.2 (old e.1)).2.2).1
    have hr : 0 < sheetRadius Abound Cs := by unfold sheetRadius; positivity
    exact sampleInput_weighted_candidate_group_cap hNk hsi e.1 c u Q hQ
      (subBoxCenter s₀ e.2.1 (boxOf K e.2.2.1)) hr
      (fun p hp => (hcov e p hp).1)
  · intro e he
    rw [hHeq e he]
    exact sampleInput_heavy_entry_floor hNk hL hgain hd₁ hd₁1 hρ hδ₀ hε hσ hτ hδρ
      hsi hpath hlin hA hs hKhi e.1 (hheavy e he).1
      (((ν (γ (old e.1))).prod volume) (cov e)) (hheavy e he).2

end

/-- The concrete cap, pruning and floor construction supplies the complete
backend consumed by the uniform finite-sample construction. -/
theorem sampleMassBackend : SampleMassBackend := by
  classical
  intro Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg i h n old R' A' V q
    κ₁ s Mp Dp σ nw κ par c u Q R lst
    hNk hL hgain hd₁ hd₁1 hρ hδ₀ hε hσ hτ hδρ hsi hpath hlin
    Aval Cs s₀ K hA hs hKlo hKhi hlight
  have hs' : (2 : ℝ) ^ s₀ ≤ 2 * (256 * (κ + 2) * Aval ^ (Cs : ℝ)) := by
    convert hs using 1 <;> ring
  obtain ⟨cov, H, hH, hmeas, hsupp, hdisj, hcap, hfloor, hmass, hcaps⟩ :=
    sampleInput_mass_data hNk hL hgain hd₁ hd₁1 hρ hδ₀ hε hσ hτ.le hδρ hsi hpath hlin
      hA hs' hKlo hKhi hlight
  refine ⟨cov, H, hmeas, hsupp, hdisj, hH, ?_, hfloor, hmass, ?_⟩
  · simpa only [sampleGroupBase] using hcap
  · simpa only [capLoss] using hcaps

end Submission.Obl.k4_clean_cover_graph_atlas
