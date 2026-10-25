-- Adapted from this LOT tree, o210, session x0795, commit f6d85510,
-- Submission/Obl/k4_clean_cover_graph_atlas/SampleInput.lean. Earlier provenance is retained below.
-- The path interface drops only its unused zero-narrowness estimate.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.SampleCore
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.DepthMenu
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.FiniteOuter

/-!
Finite input consumed by the shared per-sample analytic construction.
Adapted from this LOT tree o194/x0672, commit6b3385a5,
Submission/Obl/k4_greedy_cover_graph_atlas/SampleInput.lean.
The CleanBody bridge and predicate comparison below are new here.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
open MeasureTheory MvPolynomial Set

/-- The finite input at one sample: scalar data, the greedy data with witness sets inside the
old packets' incidences, half the greedy floors and total, the depth-`q` observation cap, the
absolute continuity of the terminal observation laws, and the bracketing of `q`. -/
def SampleInput (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (B : Fin W → ℝ) (f : ℝ → ℝ) (Mpr Dpr : ℕ) (d₁ ρ gain δ₀ τ ε : ℝ) (m : ℕ) (r : ℕ → ℝ)
    (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (Mg Dg : ℕ) (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C)
    (R' : Fin n → MvPolynomial (Fin 4) ℝ) (A' : Fin n → Set (ℕ × (Fin 6 → ℝ)))
    (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (q : ℝ) : Prop :=
  ScalarData Nk Mpr Dpr W ω ν E B ∧
  i < m ∧ gain ≤ h ∧ h ≤ 1 / 8 ∧ (∃ z : ℕ, h = gain + (z : ℝ) * (ρ * gain)) ∧
  r i + 2 * h * L ≤ L ∧ (n : ℝ) ≤ Nk ^ Mg ∧
  (∀ a, lev (old a) = i ∧ 0 < ν (γ (old a)) (A (old a)) ∧
    (R' a).totalDegree ≤ 2 ∧ (∀ e, |(R' a).coeff e| ≤ Nk ^ Mg) ∧
    MeasurableSet (A' a) ∧ A' a ⊆ A (old a) ∧
    (∀ q, fmt 6 (Nk ^ Mg) Dg {z | (q, z) ∈ A' a}) ∧
    (∀ l ∈ A' a,
      ∀ t ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i) (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i),
        |MvPolynomial.eval (x l t) (R' a)| ≤
          Nk ^ (4 * ρ * gain * L + 4 * ε) * δ Nk (r i + h * L) ∧
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R' a))| ≤
          Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ∧
        |MvPolynomial.eval (x l t)
          (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (R' a)))| ≤
          Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ^ 2 / δ Nk (r i + h * L)) ∧
    MeasurableSet (V a) ∧
    V a ⊆ {p | p ∈ F (old a) ∧ p.1 ∈ A' a ∧
      p.2 ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i) (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i) ∧
      B (γ (old a)) / Nk ^ (4 * ρ * gain * L + 4 * ε) ≤
        |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (R' a))|} ∧
    ENNReal.ofReal (Nk ^ (-((d₁ * h + 4 * ρ * gain) * L) - 4 * ε) / (2 * (2 : ℝ) ^ T i)) *
      ν (γ (old a)) (A (old a)) ≤ ((ν (γ (old a))).prod volume) (V a) ∧
    (((ν (γ (old a))).prod volume).restrict (V a)).map (obs (B (γ (old a))) (δ Nk q)) ≤
      ENNReal.ofReal (Nk ^ (-f q + τ)) • (volume.prod Measure.count) ∧
    (((ν (γ (old a))).prod volume).restrict (V a)).map (obs (B (γ (old a))) (δ Nk L)) ≪
      (volume.prod Measure.count)) ∧
  (∀ a a', a ≠ a' → old a = old a' → Disjoint (A' a) (A' a')) ∧
  (∀ b : Fin C, ((Finset.univ.filter (fun a => old a = b)).card : ℝ) ≤
    Nk ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε)) ∧
  (∀ a a', a ≠ a' → γ (old a) = γ (old a') → Disjoint (V a) (V a')) ∧
  ENNReal.ofReal (Nk ^ (-ε) / 2) ≤
    ∑ a, ENNReal.ofReal (ω (γ (old a))) * ((ν (γ (old a))).prod volume) (V a) ∧
  0 ≤ q ∧ q ≤ L ∧ r i + h * L - 3 * δ₀ * L ≤ q ∧ q ≤ r i + h * L

/-- **o210's input.** The cleaned cover of split s075 is a sample input at its menu depth. -/
theorem sampleInput_of_cleanCover
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ} {Mpr Dpr : ℕ}
    {d₁ ρ gain δ₀ τ ε : ℝ} {m : ℕ} {s r : ℕ → ℝ} {T : ℕ → ℕ} {κ : ℝ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {A : Fin C → Set (ℕ × (Fin 6 → ℝ))} {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {Mg Dg : ℕ}
    (hscalar : ScalarData Nk Mpr Dpr W ω ν E B) (hL : 0 < L) (hgain : 0 < gain)
    (hρ4 : ρ ≤ 1 / 4) (hδ₀ : 0 ≤ δ₀) (hδρ : δ₀ ≤ ρ * gain)
    (hlevels : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L ∧ 0 < r i)
    (hclean : CleanCover Nk L W ω ν B f d₁ ρ gain δ₀ m s r T κ C lev γ j Q A F Mg Dg τ ε) :
    ∃ (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
      (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
      SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
        i h n old R' A' V (menuDepth L (s i) h δ₀) := by
  obtain ⟨i, h, n, old, R', A', V, U, hi, hgh, hh1, hz, hmargin, hn, hentry, hU, hA'disj,
    hcount, hVdisj, htotal⟩ := hclean
  have hh : 0 < h := lt_of_lt_of_le hgain hgh
  have hδh : δ₀ ≤ h / 4 := by nlinarith
  obtain ⟨hnear, hri⟩ := hlevels i hi
  obtain ⟨-, hqhi, hqlo⟩ := menuDepth_candidate_spec hL hh hδ₀ hδh hri hnear hmargin
  obtain ⟨hq0, hqL⟩ := menuDepth_mem (s := s i) (h := h) (δ₀ := δ₀) hL.le
  refine ⟨i, h, n, old, R', A', V, hscalar, hi, hgh, hh1, hz, hmargin, hn, ?_, hA'disj, hcount,
    hVdisj, htotal, hq0, hqL, hqlo, hqhi⟩
  intro a
  obtain ⟨hlv, hνA, hdeg, hcoef, hA'm, hA'A, hfmt, htests, hVm, hVsub, hfloor, -, hcapq, hcapL⟩ :=
    hentry a
  refine ⟨hlv, hνA, hdeg, hcoef, hA'm, hA'A, hfmt, htests, hVm, ?_, hfloor, hcapq,
    Measure.absolutelyContinuous_of_le_smul hcapL⟩
  intro p hp
  obtain ⟨hpU, hpA', hpt, hder⟩ := hVsub hp
  exact ⟨(hU (old a)).2.1 hpU, hpA', hpt, hder⟩

/-- Keep the chosen cleaned-cover witnesses when passing to the analytic input. -/
theorem sampleInput_of_cleanBody
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ} {Mpr Dpr : ℕ}
    {d₁ ρ gain δ₀ τ ε : ℝ} {m : ℕ} {s r : ℕ → ℝ} {T : ℕ → ℕ} {κ : ℝ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {A : Fin C → Set (ℕ × (Fin 6 → ℝ))} {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {Mg Dg : ℕ}
    {i : ℕ} {h : ℝ} {n : ℕ} {old : Fin n → Fin C} {R' : Fin n → MvPolynomial (Fin 4) ℝ}
    {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))} {V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {U : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hscalar : ScalarData Nk Mpr Dpr W ω ν E B) (hL : 0 < L) (hgain : 0 < gain)
    (hρ4 : ρ ≤ 1 / 4) (hδ₀ : 0 ≤ δ₀) (hδρ : δ₀ ≤ ρ * gain)
    (hlevels : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L ∧ 0 < r i)
    (hclean : CleanBody Nk L W ω ν B f d₁ ρ gain δ₀ m s r T κ C lev γ j Q A F Mg Dg τ ε
      i h n old R' A' V U) :
    SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V (menuDepth L (s i) h δ₀) := by
  obtain ⟨hi, hgh, hh1, hz, hmargin, hn, hentry, hU, hA'disj, hcount, hVdisj, htotal⟩ := hclean
  have hh : 0 < h := lt_of_lt_of_le hgain hgh
  have hδh : δ₀ ≤ h / 4 := by nlinarith
  obtain ⟨hnear, hri⟩ := hlevels i hi
  obtain ⟨-, hqhi, hqlo⟩ := menuDepth_candidate_spec hL hh hδ₀ hδh hri hnear hmargin
  obtain ⟨hq0, hqL⟩ := menuDepth_mem (s := s i) (h := h) (δ₀ := δ₀) hL.le
  refine ⟨hscalar, hi, hgh, hh1, hz, hmargin, hn, ?_, hA'disj, hcount,
    hVdisj, htotal, hq0, hqL, hqlo, hqhi⟩
  intro a
  obtain ⟨hlv, hνA, hdeg, hcoef, hA'm, hA'A, hfmt, htests, hVm, hVsub, hfloor, -, hcapq, hcapL⟩ :=
    hentry a
  refine ⟨hlv, hνA, hdeg, hcoef, hA'm, hA'A, hfmt, htests, hVm, ?_, hfloor, hcapq,
    Measure.absolutelyContinuous_of_le_smul hcapL⟩
  intro p hp
  obtain ⟨hpU, hpA', hpt, hder⟩ := hVsub hp
  exact ⟨(hU (old a)).2.1 hpU, hpA', hpt, hder⟩

/-- **The per-sample analytic statement** (finite, no sequences). From the analytic hypotheses
it fixes `θ` and a slack ratio `ϖ`; for every `ρ ≤ min ϖ (1/4)` with `d₁ + ρ < 1`, every scale,
level schedule, gain and input exponents, an exponent `Mc`; for every allowance `β` and input
bounds `ε₀ ≤ β/2`, `σ₀ ≤ β/4`, `τ` with `ε₀ + σ₀ + τ ≤ ϖ · gain · L`, a threshold `N₀`; for every
`Nk ≥ N₀`, near-linear profile, `ε ≤ ε₀`, `σ ≤ σ₀`, path with slack `σ` and sample input, the core
output. Both `Core` (o173, and o194 through `Preparation`) and o210's `FiniteConstruction`
follow from it. -/
def PreparedSampleCore : Prop :=
  localGraph → stableSheets → algebraicRemez →
  ∀ d₁ κ₁ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
  ∃ θ ϖ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧ 0 < ϖ ∧
  ∀ ρ : ℝ, 0 < ρ → ρ ≤ ϖ → ρ ≤ 1 / 4 → d₁ + ρ < 1 →
  ∀ (L : ℝ) (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), 0 < L →
    (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) →
    0 < gain → gain ≤ 1 / 8 → 0 < δ₀ → δ₀ ≤ ρ * gain →
  ∀ Mp Dp Mg Dg Mpr Dpr : ℕ, ∃ Mc : ℕ,
  ∀ β ε₀ σ₀ τ : ℝ, 0 < β → β ≤ 1 → 0 < ε₀ → ε₀ ≤ β / 2 → 0 < σ₀ → σ₀ ≤ β / 4 → 0 < τ →
    ε₀ + σ₀ + τ ≤ ϖ * gain * L →
  ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ Nk : ℝ, N₀ ≤ Nk →
  ∀ (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ) (f : ℝ → ℝ),
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
  ∀ ε σ : ℝ, 0 < ε → ε ≤ ε₀ → 0 < σ → σ ≤ σ₀ →
  ∀ r T nw κ C lev par γ j c u Q R A F lst,
    path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
  ∀ (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
    (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (q : ℝ),
    SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q →
  ∃ s₀ K' : ℕ,
    (2 : ℝ) ^ (T i + s₀) ≤ (2 : ℝ) ^ T i * Nk ^ (κ₁ * ((θ / 4) * gain) * L / 2) ∧
    (2 : ℝ) ^ s₀ ≤ Nk ^ Mc ∧ (K' : ℝ) ≤ Nk ^ Mc ∧
    CoreOutput Nk L W ω ν E B (r i) h θ β Mc γ j c u Q R old R' A' (T i) s₀ K'


/-- The shared per-sample interface implies the exact cleaned-body interface. -/
theorem sampleCore_of_preparedSampleCore (hsc : PreparedSampleCore) : SampleCore := by
  intro hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  obtain ⟨θ, ϖ, hθ, hθ4, hϖ, hrest⟩ := hsc hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  refine ⟨θ, min ϖ (1 / 4), hθ, hθ4, lt_min hϖ (by norm_num), ?_⟩
  intro ρ hρ hρϖ hdρ L m s gain δ₀ hL hgrid hgain hgain1 hδ₀ hδρ Mp Dp Mg Dg Mpr Dpr
  have hρϖ' : ρ ≤ ϖ := hρϖ.trans (min_le_left _ _)
  have hρ4 : ρ ≤ 1 / 4 := hρϖ.trans (min_le_right _ _)
  obtain ⟨Mc, hMc⟩ := hrest ρ hρ hρϖ' hρ4 hdρ L m s gain δ₀ hL hgrid hgain hgain1 hδ₀ hδρ
    Mp Dp Mg Dg Mpr Dpr
  refine ⟨Mc, ?_⟩
  intro β τ ε₀ σ₀ hβ hβ1 hτ hε₀ hε₀β hσ₀ hσ₀β hsum
  have hsum' : ε₀ + σ₀ + τ ≤ ϖ * gain * L := hsum.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hgain.le) hL.le)
  obtain ⟨N₀, hN₀2, hN₀⟩ := hMc β ε₀ σ₀ τ hβ hβ1 hε₀ hε₀β hσ₀ (by linarith) hτ hsum'
  refine ⟨N₀, hN₀2, ?_⟩
  intro Nk hNk W ω ν E B f hscalar hlin ε σ hε hεε₀ hσ hσσ₀
    r T nw κ C lev par γ j c u Q R A F lst hpath i h n old R' A' V U hbody
  have hlevels : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L ∧ 0 < r i :=
    fun i hi => ⟨(hpath.2.2.2.2.1 i hi).1, (hpath.2.2.2.2.1 i hi).2.1⟩
  exact hN₀ Nk hNk W ω ν E B f hlin ε σ hε hεε₀ hσ hσσ₀
    r T nw κ C lev par γ j c u Q R A F lst hpath i h n old R' A' V _
    (sampleInput_of_cleanBody hscalar hL hgain hρ4 hδ₀.le hδρ hlevels hbody)

/-- Shared analytic construction closes the frozen finite theorem through the checked assembly. -/
theorem finiteConstruction_of_preparedSampleCore (hsc : PreparedSampleCore) : FiniteConstruction :=
  finiteConstruction_of_sampleCore (sampleCore_of_preparedSampleCore hsc)

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
