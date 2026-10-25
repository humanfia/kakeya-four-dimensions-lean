-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0812 f7bed5fb, x0891 a669339c, x0923 e8a77b3e, x0807 989bea46 (SourceParentPalette: x0812's version); namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceBuildShare

/-!
# The prepared set of one sample (structural part)

`selection_construct` chains the window parent (`window_parent_original`), the label groups at
the intermediate level (`q_level_groups`) and the end labels with their state codes
(`end_state_codes`) for a share-masked residual `S0`, without any numerical choice: the window
schedule, the group constants, the localization constants and the mesh are parameters with
their abstract conditions. It returns the window, the parent `b₀`, its retained set `S1` with
its floors and numerator, and the retained subset `S2 ⊆ S1` whose end histories carry at most
`81 K^C` state codes each, together with the deleted mass `S1 \ S2`.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_finite_forest_width_selection
open Submission.Obl.k4_stable_native_signal_oscillation Submission.Lib.K4XInterface
open scoped Classical

noncomputable section

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- **The prepared set of one sample (structural part).** -/
theorem selection_construct (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1)
    (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1) (hNk : 1 < Nk) (hm : 0 < m)
    {Mc : ℕ} {d₁ ρ gain ε : ℝ} {H : Fin W → Set Incidence}
    (hno : ¬MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world p.bin
      p.velocity p.frame p.assigned H)
    (hHT : ∀ w, H w ⊆ TerminalInc W p.C m p.lev p.world p.counted w)
    (S0 : Fin W → Set Incidence) (hS0 : ∀ w, MeasurableSet (S0 w) ∧ S0 w ⊆ H w)
    {Z : ℝ} (hZ : 0 < Z)
    (hS0mass : ENNReal.ofReal Z ≤ ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (S0 w))
    -- the window schedule
    (level qlev : ℕ → ℕ) (hlevel : Monotone level) (hle : ∀ i, level i ≤ m - 1)
    (J : ℕ) (hJ : 0 < J)
    (hq1 : ∀ i < J, level i ≤ qlev i) (hq2 : ∀ i < J, qlev i ≤ level (i + 1))
    -- the original velocity codes
    (δv Rv : ℝ) (hδv : 0 < δv) (hRv : 0 ≤ Rv)
    (hvel : ∀ w, ∀ᵐ l ∂(ν w), |l.2 3| ≤ Rv ∧ |l.2 4| ≤ Rv)
    -- the groups at the intermediate levels
    {A Cg : ℕ} (hC : GroupsProp A Cg) (hB : ∀ w, 0 < B w)
    {τQ : ℝ} (hτQ : 0 < τQ)
    (g : Fin W → ℝ → Observation → ENNReal) (rq : ℕ → ℝ) {τ hgd : ℝ}
    (hg : ∀ w, ∀ i < J, Measurable (g w (rq i)))
    (hlaw : ∀ w, ∀ i < J, (((ν w).prod volume).restrict (E w)).map
      (obs (B w) (δ Nk (rq i))) = (volume.prod Measure.count).withDensity (g w (rq i)))
    (hmask : ∀ w, ∀ i < J, ∀ x ∈ H w,
      g w (rq i) (obs (B w) (δ Nk (rq i)) x) ≤ ENNReal.ofReal (Nk ^ (-f (rq i) + τ)))
    (hhgd : 0 ≤ hgd) (hratio : ∀ i < J, δ Nk (p.r (qlev i)) ≤ 2 * Nk ^ hgd * δ Nk (rq i))
    (hprofq : ∀ i < J, f (p.r (qlev i)) - 2 * (δ₀ * L) ≤ f (rq i))
    (ha1 : ∀ i < J, δ Nk (p.r (qlev i)) ≤ δ Nk (p.r (level i)))
    {K : ℝ} (hK2 : 2 ≤ K) (hK7 : 7 * p.κ ≤ K)
    (hKbig : p.κ * (4 * Nk ^ hgd + 2) * Nk ^ (τ + 2 * (δ₀ * L)) *
      (16 * (1 + (7 * p.κ) ^ 2)) ≤ K * τQ)
    -- the end labels
    {hl Hx mesh : ℝ} (hgain : gain ≤ hl) (hupper : hl ≤ 1 / 8)
    (hroom : ∀ i < J, p.r (level (i + 1)) + 2 * hl * L ≤ L) (hbias : 2 * p.κ ≤ Nk ^ Mc)
    (hH1 : 1 ≤ Hx) (hκH : 6 * p.κ ≤ Hx)
    (hrow : 12 * p.κ / (Nk ^ (ρ * hl * L + ε) * Nk ^ (-hl * L)) ≤ Hx)
    (hmesh : 0 < mesh)
    (hd' : ∀ i < J, 16 * Hx ^ 4 * (((2 : ℝ) ^ p.T (level (i + 1)))⁻¹ /
      ((2 : ℝ) ^ p.T (level i))⁻¹) ≤ mesh)
    (hsmall : ∀ i < J, K ^ Cg * (δ Nk (p.r (qlev i)) / δ Nk (p.r (level i)) +
        16 * Hx ^ 4 * (((2 : ℝ) ^ p.T (level (i + 1)))⁻¹ / ((2 : ℝ) ^ p.T (qlev i))⁻¹)) +
      16 * Hx ^ 4 * (((2 : ℝ) ^ p.T (level (i + 1)))⁻¹ / ((2 : ℝ) ^ p.T (level i))⁻¹) ≤
        mesh) :
    ∃ i < J, ∃ (b₀ : Fin p.C) (S1 S2 : Set Incidence),
      p.lev b₀ = level i ∧ MeasurableSet S1 ∧ MeasurableSet S2 ∧ S2 ⊆ S1 ∧
      S1 ⊆ S0 (p.world b₀) ∩ {x | p.history m (level i) (p.world b₀, x) = some b₀} ∧
      0 < ((ν (p.world b₀)).prod volume).real S1 ∧
      Z / (8 * m) * ((ν (p.world b₀)).prod volume).real (p.packet b₀) ≤
        ((ν (p.world b₀)).prod volume).real S1 ∧
      ((ν (p.world b₀)).prod volume).real (S0 (p.world b₀) ∩
          {x | p.history m (level i) (p.world b₀, x) = some b₀}) ≤
        8 * ((ν (p.world b₀)).prod volume).real S1 ∧
      (∀ (h : Option (Fin p.C)) (z : Fin 2 → ℤ),
        ((ν (p.world b₀)).prod volume).real (S1 ∩
          {x | p.history m (level (i + 1)) (p.world b₀, x) = h ∧
            worldBin δv (p.world b₀, x) = z}) ≤
        winBase Rv δv J ^ (1 / 2 : ℝ) * ((ν (p.world b₀)).prod volume).real (S0 (p.world b₀) ∩
            {x | p.history m (level i) (p.world b₀, x) = some b₀} ∩
            {x | p.history m (level (i + 1)) (p.world b₀, x) = h}) *
          (((ν (p.world b₀)).prod volume).real (S0 (p.world b₀) ∩
              {x | p.history m (level i) (p.world b₀, x) = some b₀} ∩
              {x | worldBin δv (p.world b₀, x) = z}) /
            ((ν (p.world b₀)).prod volume).real (S0 (p.world b₀) ∩
              {x | p.history m (level i) (p.world b₀, x) = some b₀}))) ∧
      (∀ hopt : Option (Fin p.C), ∃ V : Finset (Fin 4 → ℤ), (V.card : ℝ) ≤ 81 * K ^ Cg ∧
        ∀ x ∈ S2, p.history m (level (i + 1)) (p.world b₀, x) = hopt →
          stateCode (frameBase (labelFrame p b₀ (B (p.world b₀)) (δ Nk (p.r (p.lev b₀)))))
            (frameSignal (labelFrame p b₀ (B (p.world b₀)) (δ Nk (p.r (p.lev b₀))))
              ((labelFrame p b₀ (B (p.world b₀)) (δ Nk (p.r (p.lev b₀)))).normTest
                (δ Nk (p.r (p.lev b₀))) (p.test b₀))) mesh x ∈ V) ∧
      ((ν (p.world b₀)).prod volume) (S1 \ S2) ≤
        ENNReal.ofReal τQ * ((ν (p.world b₀)).prod volume) (p.packet b₀) +
          ENNReal.ofReal ((K ^ A)⁻¹) * ((ν (p.world b₀)).prod volume) S1 +
          ENNReal.ofReal (Nk ^ (-ρ * hl * L - ε)) *
            ((ν (p.world b₀)).prod volume) (p.packet b₀) := by
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  have hS0T : ∀ w, S0 w ⊆ TerminalInc W p.C m p.lev p.world p.counted w :=
    fun w => (hS0 w).2.trans (hHT w)
  have hS0t : ∀ w, S0 w ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
    intro w z hz
    obtain ⟨b, -, -, hzb⟩ := hS0T w hz
    exact hE _ (hp.counted_support b z hzb).1
  -- the window parent
  obtain ⟨i, hiJ, b₀, S1, hS1m, hlevb, hS1sub, hS1pos, hfloorP, hfloorS, hwin⟩ :=
    window_parent_original hp hν hω0 hω1 hm S0 (fun w => (hS0 w).1) hS0T hS0t hZ hS0mass
      level hlevel hle δv Rv hδv hRv hvel J hJ
  set w₀ := p.world b₀ with hw₀
  have hS1par : ∀ x ∈ S1, p.history m (p.lev b₀) (w₀, x) = some b₀ := by
    intro x hx
    rw [hlevb]
    exact (hS1sub hx).2
  have hS1H : S1 ⊆ H w₀ := fun x hx => (hS0 w₀).2 (hS1sub hx).1
  have hS1E : S1 ⊆ E w₀ := by
    intro x hx
    obtain ⟨b, -, hb, hxb⟩ := hHT w₀ (hS1H hx)
    rw [← hb]
    exact (hp.counted_support b x hxb).1
  -- the groups at the intermediate level
  have hq : p.lev b₀ ≤ qlev i := by rw [hlevb]; exact hq1 i hiJ
  have hqm : qlev i ≤ m - 1 := (hq2 i hiJ).trans (hle (i + 1))
  have hmask' : S1 ⊆ E w₀ ∩ {x | g w₀ (rq i) (obs (B w₀) (δ Nk (rq i)) x) ≤
      ENNReal.ofReal (Nk ^ (-f (rq i) + τ))} :=
    fun x hx => ⟨hS1E hx, hmask w₀ i hiJ x (hS1H hx)⟩
  have ha1' : δ Nk (p.r (qlev i)) ≤ δ Nk (p.r (p.lev b₀)) := by rw [hlevb]; exact ha1 i hiJ
  obtain ⟨S1', nG, G, hS1'm, hS1'S1, hnG, hGm, hcov, hdel1, hsig⟩ :=
    q_level_groups hp hν hNk hC b₀ (qlev i) hq hqm (hB w₀) S1 hS1m hS1par hτQ
      (hg w₀ i hiJ) (hlaw w₀ i hiJ) hmask' hhgd (hratio i hiJ) (hprofq i hiJ) ha1' hK2 hK7 hKbig
  -- the end labels
  have hS1'term : ∀ x ∈ S1', p.history m (p.lev b₀) (w₀, x) = some b₀ ∧
      x ∈ TerminalInc W p.C m p.lev p.world p.counted w₀ :=
    fun x hx => ⟨hS1par x (hS1'S1 hx), hHT w₀ (hS1H (hS1'S1 hx))⟩
  have hqe : qlev i ≤ level (i + 1) := hq2 i hiJ
  have hem : level (i + 1) ≤ m - 1 := hle (i + 1)
  have hd'' : 16 * Hx ^ 4 * (((2 : ℝ) ^ p.T (level (i + 1)))⁻¹ /
      ((2 : ℝ) ^ p.T (p.lev b₀))⁻¹) ≤ mesh := by rw [hlevb]; exact hd' i hiJ
  have hsmall' : K ^ Cg * (δ Nk (p.r (qlev i)) / δ Nk (p.r (p.lev b₀)) +
        16 * Hx ^ 4 * (((2 : ℝ) ^ p.T (level (i + 1)))⁻¹ / ((2 : ℝ) ^ p.T (qlev i))⁻¹)) +
      16 * Hx ^ 4 * (((2 : ℝ) ^ p.T (level (i + 1)))⁻¹ / ((2 : ℝ) ^ p.T (p.lev b₀))⁻¹) ≤
        mesh := by rw [hlevb]; exact hsmall i hiJ
  obtain ⟨S2, hS2m, hS2S1', hdel2, hcodes⟩ := end_state_codes hp hν hNk hno b₀ (qlev i)
    (level (i + 1)) hq hqe hem (hB w₀) S1' hS1'm (fun x hx => hS1H (hS1'S1 hx)) hS1'term G hnG
    hcov hsig hgain hupper (hroom i hiJ) hbias hH1 hκH hrow hmesh
    (by positivity) hd'' hsmall'
  refine ⟨i, hiJ, b₀, S1, S2, hlevb, hS1m, hS2m, hS2S1'.trans hS1'S1, hS1sub, hS1pos, hfloorP,
    hfloorS, hwin, ?_, ?_⟩
  · intro hopt
    obtain ⟨V, hV, hVm⟩ := hcodes hopt
    exact ⟨V, hV, hVm⟩
  · calc ((ν w₀).prod volume) (S1 \ S2)
        ≤ ((ν w₀).prod volume) ((S1 \ S1') ∪ (S1' \ S2)) := by
          refine measure_mono fun x hx => ?_
          by_cases h : x ∈ S1'
          · exact Or.inr ⟨h, hx.2⟩
          · exact Or.inl ⟨hx.1, h⟩
      _ ≤ ((ν w₀).prod volume) (S1 \ S1') + ((ν w₀).prod volume) (S1' \ S2) :=
          measure_union_le _ _
      _ ≤ _ := add_le_add hdel1 hdel2

end

end

end Submission.Obl.k4_finite_affine_parent_sources
