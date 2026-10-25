import Submission.Obl.k4_quadratic_atlas_normalization.Endpoints
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

-- Adapted from this LOT obligation o115, session x0385, commit 59dde9c,
-- Submission/Obl/k4_quadratic_atlas_normalization/Interface.lean.
-- Renamed the expression aliases to the checked Interface.lean from x0398.

/-!
# Per-sample interface and the glue of o115

`KnownAt` and `RoughAt` are one sample of `knownSys` and `roughSys`. `RoughAtSel P` is a
rough sample whose charts with `P (B, R)` carry at least half of the selected mass.
`curv R` is the constant hidden curvature `∂₃∂₃R`, and `lowCase` is the curvature split of
the final normalization step, with threshold `B² N^(-8a) / δ(N,L)`.

`LowStep` and `HighStep` say that late rough samples of one curvature case normalize to known
samples at the fixed depths `L - 4a` and `L - 12a`, with output format fixed before the
output slack. `statement_of_steps` proves the frozen statement from them: every rough sample
has a curvature case carrying half its mass, one case occurs cofinally at every slack
(monotonicity in the slack), and its depth is used for every output slack.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_quadratic_atlas_normalization

open MeasureTheory Filter

/-- The constant hidden curvature `∂₃∂₃R` of a test of degree at most two. -/
noncomputable def curv (R : MvPolynomial (Fin 4) ℝ) : ℝ :=
  MvPolynomial.eval 0 (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))

/-- The low-curvature case of the final normalization. -/
def lowCase (Nk L a Bv : ℝ) (R : MvPolynomial (Fin 4) ℝ) : Prop :=
  |curv R| ≤ Bv ^ 2 * Nk ^ (-(8 * a)) / δ Nk L

/-- One sample of a known atlas system. -/
def KnownAt (Nk : ℝ) (Wk : ℕ) (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure Line)
    (Ek : Fin Wk → Set Incidence) (Bk : Fin Wk → ℝ) (Lobs r h : ℝ) (M D : ℕ) (ε : ℝ) : Prop :=
  ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ Nk ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin C' → Fin Wk) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ) (A : Fin C' → Set Line) (F : Fin C' → Set Incidence) (lst : Fin Wk → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C')), (2 : ℝ) ^ T ≤ Nk ^ (h + ε) ∧ (C' : ℝ) ≤ Nk ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ γ₁ o, ((lst γ₁ o).card : ℝ) ≤ κ) ∧ (∀ b, chart Nk M D κ T ((j b : ℕ) : ℝ) r (Bk (γ b)) (Ek (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (∀ p ∈ F b, b ∈ lst (γ b) (obs (Bk (γ b)) (δ Nk Lobs) p))) ∧ ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ωk (γ b)) * ((νk (γ b)).prod MeasureTheory.volume) (F b)

/-- One sample of a rough atlas system. -/
def RoughAt (Nk : ℝ) (Wk : ℕ) (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure Line)
    (Ek : Fin Wk → Set Incidence) (Bk : Fin Wk → ℝ) (L a h : ℝ) (M D : ℕ) (ε : ℝ) : Prop :=
  ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ Nk ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin C' → Fin Wk) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ) (A : Fin C' → Set Line) (F : Fin C' → Set Incidence) (lst : Fin Wk → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C')), (2 : ℝ) ^ T ≤ Nk ^ (h + ε) ∧ (C' : ℝ) ≤ Nk ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ γ₁ o, ((lst γ₁ o).card : ℝ) ≤ κ) ∧ (∀ b, rough Nk M D κ T ((j b : ℕ) : ℝ) L a (Bk (γ b)) (Ek (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (∀ p ∈ F b, b ∈ lst (γ b) (obs (Bk (γ b)) (δ Nk L) p))) ∧ ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ωk (γ b)) * ((νk (γ b)).prod MeasureTheory.volume) (F b)

/-- A rough sample whose charts with `P (B, R)` carry at least half of the selected mass. -/
def RoughAtSel (P : ℝ → MvPolynomial (Fin 4) ℝ → Prop) (Nk : ℝ) (Wk : ℕ)
    (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure Line) (Ek : Fin Wk → Set Incidence) (Bk : Fin Wk → ℝ)
    (L a h : ℝ) (M D : ℕ) (ε : ℝ) : Prop :=
  ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ Nk ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin C' → Fin Wk) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ) (A : Fin C' → Set Line) (F : Fin C' → Set Incidence) (lst : Fin Wk → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C')), (2 : ℝ) ^ T ≤ Nk ^ (h + ε) ∧ (C' : ℝ) ≤ Nk ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ γ₁ o, ((lst γ₁ o).card : ℝ) ≤ κ) ∧ (∀ b, rough Nk M D κ T ((j b : ℕ) : ℝ) L a (Bk (γ b)) (Ek (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (∀ p ∈ F b, b ∈ lst (γ b) (obs (Bk (γ b)) (δ Nk L) p))) ∧ ENNReal.ofReal (κ⁻¹ / 2) ≤ ∑ b, ENNReal.ofReal (ωk (γ b)) * ((νk (γ b)).prod MeasureTheory.volume) (F b ∩ {_p | P (Bk (γ b)) (R b)})

theorem knownSys_iff {N : ℕ → ℝ} {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure Line} {E : (k : ℕ) → Fin (W k) → Set Incidence}
    {B : (k : ℕ) → Fin (W k) → ℝ} {Lobs r h : ℝ} :
    knownSys N W ω ν E B Lobs r h ↔ ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      KnownAt (N k) (W k) (ω k) (ν k) (E k) (B k) Lobs r h M D ε :=
  Iff.rfl

theorem roughSys_iff {N : ℕ → ℝ} {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure Line} {E : (k : ℕ) → Fin (W k) → Set Incidence}
    {B : (k : ℕ) → Fin (W k) → ℝ} {L a h : ℝ} :
    roughSys N W ω ν E B L a h ↔ ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      RoughAt (N k) (W k) (ω k) (ν k) (E k) (B k) L a h M D ε :=
  Iff.rfl

/-- The low-curvature step: late low samples normalize at depth `L - 4a`. -/
def LowStep (L a h : ℝ) (M D Mb : ℕ) : Prop :=
  ∃ M' D' : ℕ, ∀ ε : ℝ, 0 < ε → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℝ,
    ∀ (Nk : ℝ) (Wk : ℕ) (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure Line)
      (Ek : Fin Wk → Set Incidence) (Bk : Fin Wk → ℝ),
      N₀ ≤ Nk → 2 ≤ Nk → (∀ γ, 0 ≤ ωk γ) → (∑ γ, ωk γ) = 1 →
      (∀ γ, IsProbabilityMeasure (νk γ)) →
      (∀ γ, 0 < Bk γ ∧ Bk γ ≤ Nk ^ Mb ∧ (Bk γ)⁻¹ ≤ Nk ^ Mb) →
      RoughAtSel (fun Bv R => lowCase Nk L a Bv R) Nk Wk ωk νk Ek Bk L a h M D ε₀ →
      KnownAt Nk Wk ωk νk Ek Bk L (L - 4 * a) h M' D' ε

/-- The high-curvature step: late high samples normalize at depth `L - 12a`. -/
def HighStep (L a h : ℝ) (M D Mb : ℕ) : Prop :=
  ∃ M' D' : ℕ, ∀ ε : ℝ, 0 < ε → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℝ,
    ∀ (Nk : ℝ) (Wk : ℕ) (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure Line)
      (Ek : Fin Wk → Set Incidence) (Bk : Fin Wk → ℝ),
      N₀ ≤ Nk → 2 ≤ Nk → (∀ γ, 0 ≤ ωk γ) → (∑ γ, ωk γ) = 1 →
      (∀ γ, IsProbabilityMeasure (νk γ)) →
      (∀ γ, 0 < Bk γ ∧ Bk γ ≤ Nk ^ Mb ∧ (Bk γ)⁻¹ ≤ Nk ^ Mb) →
      RoughAtSel (fun Bv R => ¬ lowCase Nk L a Bv R) Nk Wk ωk νk Ek Bk L a h M D ε₀ →
      KnownAt Nk Wk ωk νk Ek Bk L (L - 12 * a) h M' D' ε

/-- Half of a mass bound passes to one of two summands. -/
theorem half_le_or_half_le {X Y : ENNReal} {m : ℝ} (hm : 0 ≤ m)
    (h : ENNReal.ofReal m ≤ X + Y) :
    ENNReal.ofReal (m / 2) ≤ X ∨ ENNReal.ofReal (m / 2) ≤ Y := by
  by_contra hcon
  push Not at hcon
  have hsum : ENNReal.ofReal (m / 2) + ENNReal.ofReal (m / 2) = ENNReal.ofReal m := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have := ENNReal.add_lt_add hcon.1 hcon.2
  rw [hsum] at this
  exact (lt_irrefl _ (this.trans_le h))

/-- Every rough sample has a curvature case carrying half of its selected mass. -/
theorem roughAt_split (P : ℝ → MvPolynomial (Fin 4) ℝ → Prop) {Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Line} {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
    {L a h : ℝ} {M D : ℕ} {ε : ℝ} (hR : RoughAt Nk Wk ωk νk Ek Bk L a h M D ε) :
    RoughAtSel P Nk Wk ωk νk Ek Bk L a h M D ε ∨
      RoughAtSel (fun Bv R => ¬ P Bv R) Nk Wk ωk νk Ek Bk L a h M D ε := by
  obtain ⟨κ, hκ1, hκε, T, C', γ, j, c, u, Q, R, A, F, lst, hT, hC, hdisj, hlst, hch, hmass⟩ := hR
  have hle : ∑ b, ENNReal.ofReal (ωk (γ b)) * ((νk (γ b)).prod volume) (F b) ≤
      (∑ b, ENNReal.ofReal (ωk (γ b)) *
        ((νk (γ b)).prod volume) (F b ∩ {_p | P (Bk (γ b)) (R b)})) +
      ∑ b, ENNReal.ofReal (ωk (γ b)) *
        ((νk (γ b)).prod volume) (F b ∩ {_p | ¬ P (Bk (γ b)) (R b)}) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← mul_add]
    gcongr
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro p hp
    by_cases hP : P (Bk (γ b)) (R b)
    · exact Or.inl ⟨hp, hP⟩
    · exact Or.inr ⟨hp, hP⟩
  rcases half_le_or_half_le (inv_nonneg.mpr (zero_le_one.trans hκ1)) (hmass.trans hle) with h | h
  · exact Or.inl ⟨κ, hκ1, hκε, T, C', γ, j, c, u, Q, R, A, F, lst, hT, hC, hdisj, hlst, hch, h⟩
  · exact Or.inr ⟨κ, hκ1, hκε, T, C', γ, j, c, u, Q, R, A, F, lst, hT, hC, hdisj, hlst, hch, h⟩

/-- A rough sample at a smaller slack is one at a larger slack. -/
theorem RoughAtSel.mono {P : ℝ → MvPolynomial (Fin 4) ℝ → Prop} {Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Line} {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
    {L a h : ℝ} {M D : ℕ} {ε ε' : ℝ} (hN : 1 ≤ Nk) (hεε' : ε ≤ ε')
    (hR : RoughAtSel P Nk Wk ωk νk Ek Bk L a h M D ε) :
    RoughAtSel P Nk Wk ωk νk Ek Bk L a h M D ε' := by
  obtain ⟨κ, hκ1, hκε, T, C', γ, j, c, u, Q, R, A, F, lst, hT, hC, hdisj, hlst, hch, hmass⟩ := hR
  exact ⟨κ, hκ1, hκε.trans (Real.rpow_le_rpow_of_exponent_le hN hεε'), T, C', γ, j, c, u, Q, R,
    A, F, lst, hT.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), hC, hdisj, hlst,
    hch, hmass⟩

/-- The frozen statement from the two curvature steps. -/
theorem statement_of_steps
    (hlow : ∀ (L a h : ℝ) (M D Mb : ℕ), 0 < L → 0 < a → 20 * a < L → LowStep L a h M D Mb)
    (hhigh : ∀ (L a h : ℝ) (M D Mb : ℕ), 0 < L → 0 < a → 20 * a < L → HighStep L a h M D Mb) :
    AtlasNormalization := by
  intro N W ω ν E B L a h hN2 hNt hL ha h20 hω0 hω1 hν hB hR
  obtain ⟨Mb, hMb⟩ := hB
  obtain ⟨M, D, hR⟩ := roughSys_iff.mp hR
  have hN1 : ∀ k, (1 : ℝ) ≤ N k := fun k => le_trans (by norm_num) (hN2 k)
  have hsplit : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      RoughAtSel (fun Bv R => lowCase (N k) L a Bv R) (N k) (W k) (ω k) (ν k) (E k) (B k)
        L a h M D ε ∨
      RoughAtSel (fun Bv R => ¬ lowCase (N k) L a Bv R) (N k) (W k) (ω k) (ν k) (E k) (B k)
        L a h M D ε :=
    fun ε hε => (hR ε hε).mono fun k hk => roughAt_split _ hk
  rcases frequently_binary_choice
      (fun ε k => RoughAtSel (fun Bv R => lowCase (N k) L a Bv R) (N k) (W k) (ω k) (ν k)
        (E k) (B k) L a h M D ε)
      (fun ε k => RoughAtSel (fun Bv R => ¬ lowCase (N k) L a Bv R) (N k) (W k) (ω k) (ν k)
        (E k) (B k) L a h M D ε)
      (fun ε ε' _ hεε' k hk => RoughAtSel.mono (hN1 k) hεε' hk)
      (fun ε ε' _ hεε' k hk => RoughAtSel.mono (hN1 k) hεε' hk) hsplit with hc | hc
  · refine ⟨L - 4 * a, by linarith, by linarith, by linarith, ?_⟩
    obtain ⟨M', D', hstep⟩ := hlow L a h M D Mb hL ha h20
    refine knownSys_iff.mpr ⟨M', D', fun ε hε => ?_⟩
    obtain ⟨ε₀, hε₀, N₀, hN₀⟩ := hstep ε hε
    exact ((hc ε₀ hε₀).and_eventually (hNt.eventually_ge_atTop N₀)).mono fun k hk =>
      hN₀ (N k) (W k) (ω k) (ν k) (E k) (B k) hk.2 (hN2 k) (hω0 k) (hω1 k) (hν k)
        (hMb k) hk.1
  · refine ⟨L - 12 * a, by linarith, by linarith, by linarith, ?_⟩
    obtain ⟨M', D', hstep⟩ := hhigh L a h M D Mb hL ha h20
    refine knownSys_iff.mpr ⟨M', D', fun ε hε => ?_⟩
    obtain ⟨ε₀, hε₀, N₀, hN₀⟩ := hstep ε hε
    exact ((hc ε₀ hε₀).and_eventually (hNt.eventually_ge_atTop N₀)).mono fun k hk =>
      hN₀ (N k) (W k) (ω k) (ν k) (E k) (B k) hk.2 (hN2 k) (hω0 k) (hω1 k) (hν k)
        (hMb k) hk.1

end Submission.Obl.k4_quadratic_atlas_normalization
