import Submission.Obl.k4_clean_cover_graph_atlas.GroupCoords
import Submission.Obl.k4_clean_cover_graph_atlas.SampleParams
import Submission.Obl.k4_clean_cover_graph_atlas.SampleDomains

/-!
# The original-law mass backend of one sample

`SampleMassBackend` is the original-law input of the concrete sample assembly, at every actual
sample (sample input, path, near-linear profile), every common sheet scale `A > 0`, sheet exponent
`Cs`, sub-block exponent `s₀` with `2^s₀ ≤ 512 (κ+2) A^Cs`, box range `K` with
`κ 2^s₀ ≤ K ≤ κ 2^s₀ + 1`, and the light tail `4 N^(-ε-τ) ≤ N^(-ε)/64`. It supplies covered incidences of
the entries and a positive cap for each group such that:

1. the covered sets are measurable, consist of witness incidences on member lines of the entry in
   its sub-block, and are disjoint within a world;
2. every active covered set has weighted original group-base law at most `H G · volume`, read
   through the terminal observation in the group coordinates of radius `sheetRadius A Cs`;
3. every active covered set has weighted mass at least `H G · groupFloor N (slackTot …)`;
4. the retained total weighted mass is at least `N^(-ε)/4`;
5. the caps of the active entries sum to at most `2²³ N^(loss + 6σ)`,
   `loss = (12 ρ gain + 5 δ₀) L + 12 ε + τ`.

`preparedSampleCore_of_massBackend` (`SampleConstruction.lean`) derives `PreparedSampleCore`
from it.
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface

/-- The group coordinates of a group at a sample, with sheet scale `A` and exponent `Cs`. -/
noncomputable def sampleGroupBase {C : ℕ} (T : ℕ) (j : Fin C → ℕ)
    (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (s₀ K : ℕ) (A : ℝ) (Cs : ℕ) (G : Group C s₀ K) :
    EuclideanSpace ℝ (Fin 3) × ℤ → EuclideanSpace ℝ (Fin 3) :=
  groupBase T (j G.1) (c G.1) (u G.1) (Q G.1) (subBoxCenter s₀ G.2.1 (boxOf K G.2.2.1))
    (sheetRadius A Cs)

/-- The exponent of the total cap budget. -/
noncomputable def capLoss (ρ gain L δ₀ ε τ σ : ℝ) : ℝ :=
  ((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ) + 6 * σ

open Classical in
/-- **The original-law mass backend of one sample.** -/
def SampleMassBackend : Prop :=
  ∀ {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ} {Mpr Dpr : ℕ}
    {d₁ ρ gain δ₀ τ ε : ℝ} {m : ℕ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {A : Fin C → Set (ℕ × (Fin 6 → ℝ))} {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Mg Dg : ℕ} {i : ℕ} {h : ℝ} {n : ℕ} {old : Fin n → Fin C}
    {R' : Fin n → MvPolynomial (Fin 4) ℝ} {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))}
    {V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {q : ℝ}
    {κ₁ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ} {σ : ℝ} {nw : ℕ → ℝ} {κ : ℝ} {par : Fin C → Fin C}
    {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)},
    1 ≤ Nk → 0 < L → 0 < gain → 0 ≤ d₁ → d₁ ≤ 1 → 0 ≤ ρ → 0 ≤ δ₀ → 0 ≤ ε → 0 ≤ σ → 0 < τ →
    δ₀ ≤ ρ * gain →
    SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q →
    path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
    (∀ q' : ℝ, 0 ≤ q' → q' ≤ L → |f q' - f 0 - d₁ * q'| ≤ δ₀ * L) →
    ∀ (Aval : ℝ) (Cs s₀ K : ℕ), 0 < Aval →
      (2 : ℝ) ^ s₀ ≤ 512 * (κ + 2) * Aval ^ (Cs : ℝ) →
      κ * (2 : ℝ) ^ s₀ ≤ K → (K : ℝ) ≤ κ * (2 : ℝ) ^ s₀ + 1 →
      4 * Nk ^ (-ε - τ) ≤ Nk ^ (-ε) / 64 →
    ∃ (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (H : Group C s₀ K → ℝ),
      (∀ e, MeasurableSet (cov e)) ∧
      (∀ e, ∀ p ∈ cov e, p ∈ V e.1 ∧
        p.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e ∧
        p.2 ∈ subBlock (T i) s₀ (j (old e.1)) e.2.1) ∧
      (∀ e e', e ≠ e' → γ (old e.1) = γ (old e'.1) → Disjoint (cov e) (cov e')) ∧
      (∀ G, 0 < H G) ∧
      (∀ e, (cov e).Nonempty →
        (ENNReal.ofReal (ω (γ (old e.1))) • ((ν (γ (old e.1))).prod volume).restrict (cov e)).map
          (sampleGroupBase (T i) j c u Q s₀ K Aval Cs (entryGroup old e) ∘
            obs (B (γ (old e.1))) (δ Nk L)) ≤
          ENNReal.ofReal (H (entryGroup old e)) • volume) ∧
      (∀ e, (cov e).Nonempty →
        ENNReal.ofReal (H (entryGroup old e) * groupFloor Nk (slackTot ρ gain L ε σ τ)) ≤
          ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e)) ∧
      ENNReal.ofReal (Nk ^ (-ε) / 4) ≤
        ∑ e, ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e) ∧
      (∑ e, if (cov e).Nonempty then ENNReal.ofReal (H (entryGroup old e)) else 0) ≤
        ENNReal.ofReal (2 ^ 23 * Nk ^ capLoss ρ gain L δ₀ ε τ σ)

end Submission.Obl.k4_clean_cover_graph_atlas
