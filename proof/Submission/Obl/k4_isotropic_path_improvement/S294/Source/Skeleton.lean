-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.Skeleton, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The quantifier skeleton of the relative source (session x1088).

`relRowCoreNat_of_sample` proves x1080's natural-unit relative row core contract
`RelRowCoreNatSourceAssertion` (hence o265, `O204/Tangent/Accepted.lean`) from ONE per-sample
producer `SampleProducer`.  The skeleton makes every choice that precedes the original data
(`Source/Window.lean`: qualification degree, gain, strip exponent, grid, front window), reads
the frozen problem and path as the ported front's `ProblemData`/`PathData`, runs x1095's front
`exists_narrow_or_broad_fraction_envelope` (fraction `2 N^(-budget)`), returns its narrow exit
unchanged and hands its broad branch to the producer.

`SampleProducer` is what remains: from the front's broad branch at one late sample (its
prepared path `Q`, ancestor level `i`, palette family `F`, broad residual `R` with its mass and
the likelihood cut) produce the natural-unit certificate `RelRowCoreNat`, i.e. a packet `b`, an
ancestor block and x1080's `RelativeRowPacket` (clause groups in `Source/Clauses.lean`).  The
producer may shrink the path tolerance and wait for a later sample (`∃ σP, ∀ᶠ k`). -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Window
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.NativeFractionEnvelope
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.PathTolerance
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.NaturalCore

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open MeasureTheory Filter
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

noncomputable section

/-- The palette exponent of the front: its velocity palette has mesh `N^(-paletteExpOf …)`. -/
def paletteExpOf (tune : Tuning) (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss gain L : ℝ) : ℝ :=
  4 * (((Ep : ℝ) + 1) * precision + 3) * gain * tune.depth κ₁ d₁ Ep precision loss / κ₁ * L

/-- The front's labelled-velocity mesh exponent. -/
def ueOf (tune : Tuning) (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss gain δ₀ L : ℝ) : ℝ :=
  paletteExpOf tune κ₁ d₁ Ep precision loss gain L + 2 * δ₀ * L

/-- The front's entropy exponent: its palette constant is `N^entropy` up to a threshold. -/
def entropyOf (C m : ℕ) (ue : ℝ) : ℝ := 4096 * ((C : ℝ) / m) * ue

/-- **The per-sample producer.** At a late sample of the front's broad branch, with the
skeleton's choices, produce `RelRowCoreNat`. -/
def SampleProducer (tune : Tuning) : Prop :=
  O204.Split.mk →
  ∀ (d₁ κ₁ ρ : ℝ) (Ep : ℕ) (precision loss e0 : ℝ),
  0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < ρ → d₁ + ρ < 1 → 1 ≤ precision → 0 < loss →
  loss ≤ 1 → 0 < e0 →
  ∀ (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (C target : ℕ) (indices : Finset ℕ),
  Parent.grid κ₁ ρ m s (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀
      (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) / 8) →
  δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) →
  4 * δ₀ * (m : ℝ) ≤ κ₁ → 8 ≤ m →
  8 ≤ gridFineOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m →
  target < m → s target = 1 / 2 → 2 * (target + 1) = m → 1 ≤ C →
  windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m ≤ C →
  (C : ℝ) ≤ windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m + 1 →
  C + 1 ≤ target → indices = Finset.range (target + 1 - C) →
  ∀ (d : ProblemData), d.Valid →
  (∀ r : ℝ, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L) →
  ∀ (Mp Dp : ℕ) (budget : ℝ), 0 < budget → budget ≤ 1 →
  ∃ σP : ℝ, 0 < σP ∧ ∀ᶠ k in atTop, ∀ p : PathData (d.W k),
    p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σP →
    ∀ H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ), (∀ w, MeasurableSet (H w)) →
    (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
    ENNReal.ofReal (p.κ⁻¹ / 2) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
    ∀ (Qp : PreparedAngularPath d k p m H (fun _ : Fin 1 => d.η * d.L) (tauOf tune δ₀ d.L budget)),
    Qp.uniformPureBounds (tauOf tune δ₀ d.L budget) →
    ENNReal.ofReal (11 * p.κ⁻¹ / 32) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Qp.residual w) →
    ∀ i ∈ indices,
    ∀ Fp : PaletteFamily Qp i (i + C)
        (d.N k ^ (-paletteExpOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) d.L))
        (d.N k ^ entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L) /
          palettePruningThreshold ⌈(4 * p.κ + 6) ^ 2⌉₊)
        (lightParentThreshold p.κ),
    ∀ Rp : BroadResidual Fp
        (d.N k ^ (-(ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * d.L)))
        (2 * ((d.N k ^ budget) ^ 1)⁻¹),
    ENNReal.ofReal (71 * p.κ⁻¹ / 512) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Rp.residual w) →
    (∀ b, Fp.active b → Fp.U b ⊆
      likelihoodGood Qp.law (labelledSupport Qp.residual)
        (finitePacketHistory p.lev p.γ p.F)
        (labelledVelocityPalette
          (d.N k ^ (-ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L)))
        i (i + C)
        (d.N k ^ entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L))) →
    O204.Tangent.RelRowCoreNat (qualDegree κ₁) Ep precision loss (d.N k) d.L d₁
      (gainOf tune κ₁ d₁ Ep precision loss e0) (Mp + 1) p.κ (d.W k) (d.ν k) (d.B k) p.r p.T p.C p.lev
      p.γ p.j p.c p.u p.A p.F H

/-- The numerical facts of the choices. -/
theorem choices_ok {tune : Tuning} {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss e0 : ℝ} (hκ : 0 < κ₁)
    (hκ1 : κ₁ ≤ 1) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1) (hprec : 1 ≤ precision) (hloss : 0 < loss)
    (hloss1 : loss ≤ 1) (he0 : 0 < e0) :
    0 < gainOf tune κ₁ d₁ Ep precision loss e0 ∧ gainOf tune κ₁ d₁ Ep precision loss e0 ≤ 1 / 8 ∧
      0 < ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) ∧
      ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) ≤ 1 ∧
      ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) / 8 ≤
        4 * gainOf tune κ₁ d₁ Ep precision loss e0 ∧
      0 < windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) ∧
      windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) ≤ 1 / 16 ∧
      gainOf tune κ₁ d₁ Ep precision loss e0 ≤
        windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) ∧
      0 < tolOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) := by
  have hg : 0 < gainOf tune κ₁ d₁ Ep precision loss e0 := gainOf_pos hκ hd₁ hprec hloss he0
  have hcap := gainOf_le_cap (tune := tune) (κ₁ := κ₁) (Ep := Ep) (precision := precision)
    (loss := loss) (e0 := e0) (d₁ := d₁)
  have hcap' := gainCap_le (tune := tune) (Ep := Ep) hκ hκ1 hd₀ hd₁ hprec hloss hloss1
  have hD := tune.one_le_depth κ₁ d₁ Ep precision loss
  have hB0 := tune.budget_pos κ₁ d₁ Ep precision loss
  have hB1 := tune.budget_le_one κ₁ d₁ Ep precision loss
  have hgs0 : gainOf tune κ₁ d₁ Ep precision loss e0 ≤ κ₁ ^ 2 / (2 ^ 48 * 9) := hcap.trans hcap'
  unfold gainCap at hcap
  unfold ubOf windowOf
  generalize gainOf tune κ₁ d₁ Ep precision loss e0 = g at hg hcap hgs0 ⊢
  generalize tune.depth κ₁ d₁ Ep precision loss = D at hD hcap ⊢
  generalize tune.budget κ₁ d₁ Ep precision loss = Bq at hB0 hB1 hcap ⊢
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hE1 : (1 : ℝ) ≤ (Ep : ℝ) + 1 := by linarith
  set X := ((Ep : ℝ) + 1) * precision with hX
  have hX0 : 0 ≤ X := by positivity
  have hX1 : 1 ≤ X := by
    have : 1 * 1 ≤ ((Ep : ℝ) + 1) * precision := mul_le_mul hE1 hprec zero_le_one (by linarith)
    linarith
  have hd1 : 0 < 1 - d₁ := by linarith
  have hκ2 : κ₁ ^ 2 ≤ 1 := pow_le_one₀ hκ.le hκ1
  have hgs : g ≤ 1 / 2 ^ 48 := by
    have : κ₁ ^ 2 / (2 ^ 48 * 9) ≤ 1 / 2 ^ 48 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hub : κ₁ * Bq * loss * g / (4096 * ((Ep : ℝ) + 1)) ≤ 16 * g := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : Bq * loss ≤ 1 := by nlinarith
    have h2 : κ₁ * Bq * loss ≤ 1 := by
      have : κ₁ * (Bq * loss) ≤ 1 := mul_le_one₀ hκ1 (by positivity) h1
      linarith [mul_assoc κ₁ Bq loss]
    nlinarith
  have hwpos : 0 < (1 - d₁) * κ₁ := by positivity
  have hD0 : 0 < D := by linarith
  have hwin_ge : g ≤ 1024 * (X + 3) * g * D / ((1 - d₁) * κ₁) := by
    rw [le_div_iff₀ hwpos]
    have : (1 - d₁) * κ₁ ≤ 1 := by nlinarith
    have : (1 : ℝ) ≤ 1024 * (X + 3) * D := by nlinarith
    nlinarith
  refine ⟨hg, by linarith, by positivity, by linarith, by linarith,
    by positivity, ?_, hwin_ge, by
      unfold tolOf
      have := tune.one_le_slack
      have : (0 : ℝ) < tune.slack := by linarith
      have := tune.budget_pos κ₁ d₁ Ep precision loss
      positivity⟩
  -- the window: `1024 (X + 3) g D / ((1 - d₁) κ₁) ≤ 1/16`
  rw [div_le_iff₀ hwpos]
  have hden : 0 < 2 ^ 48 * ((Ep : ℝ) + 1) * (X + 3) ^ 2 * D ^ 2 := by positivity
  have hB : g * (2 ^ 48 * ((Ep : ℝ) + 1) * (X + 3) ^ 2 * D ^ 2) ≤
      loss * (1 - d₁) ^ 2 * κ₁ ^ 2 := by
    have := (le_div_iff₀ hden).mp hcap
    have h0 : 0 ≤ loss * (1 - d₁) ^ 2 * κ₁ ^ 2 := by positivity
    have : loss * (1 - d₁) ^ 2 * κ₁ ^ 2 * Bq ≤ loss * (1 - d₁) ^ 2 * κ₁ ^ 2 := by nlinarith
    linarith
  -- `16384 (X+3) D ≤ 2^48 (E+1) (X+3)^2 D^2`
  have hy : 1 ≤ (X + 3) * D := by
    have : (1 : ℝ) ≤ X + 3 := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (X + 3) * D := mul_le_mul this hD zero_le_one (by linarith)
  have hA : 16384 * (X + 3) * D ≤ 2 ^ 48 * ((Ep : ℝ) + 1) * (X + 3) ^ 2 * D ^ 2 := by
    have h1 : (X + 3) * D ≤ ((X + 3) * D) ^ 2 := le_self_pow₀ hy (by norm_num)
    have h16 : (16384 : ℝ) ≤ 2 ^ 48 * ((Ep : ℝ) + 1) :=
      le_trans (by norm_num) (le_mul_of_one_le_right (by positivity) hE1)
    calc 16384 * (X + 3) * D = 16384 * ((X + 3) * D) := by ring
      _ ≤ 16384 * ((X + 3) * D) ^ 2 := by gcongr
      _ ≤ 2 ^ 48 * ((Ep : ℝ) + 1) * ((X + 3) * D) ^ 2 :=
          mul_le_mul_of_nonneg_right h16 (sq_nonneg _)
      _ = 2 ^ 48 * ((Ep : ℝ) + 1) * (X + 3) ^ 2 * D ^ 2 := by ring
  have hl1 : loss * (1 - d₁) ≤ 1 := mul_le_one₀ hloss1 (by linarith) (by linarith)
  have hl2 : loss * (1 - d₁) * κ₁ ≤ 1 := mul_le_one₀ hl1 (by positivity) hκ1
  have hC : loss * (1 - d₁) ^ 2 * κ₁ ^ 2 ≤ (1 - d₁) * κ₁ := by
    have : loss * (1 - d₁) ^ 2 * κ₁ ^ 2 = (loss * (1 - d₁) * κ₁) * ((1 - d₁) * κ₁) := by ring
    rw [this]
    exact mul_le_of_le_one_left hwpos.le hl2
  have hDg := mul_le_mul_of_nonneg_right hA hg.le
  have e1 : 1024 * (X + 3) * g * D * 16 = 16384 * (X + 3) * D * g := by ring
  have e2 : 2 ^ 48 * ((Ep : ℝ) + 1) * (X + 3) ^ 2 * D ^ 2 * g =
      g * (2 ^ 48 * ((Ep : ℝ) + 1) * (X + 3) ^ 2 * D ^ 2) := by ring
  linarith

/-- The window gap condition of the front. -/
theorem gap_ok {C m card : ℕ} {ue : ℝ} (hm : 0 < m) (hC : 1 ≤ C) (hue : 0 < ue)
    (hcard : (m : ℝ) / 4 ≤ (card : ℝ)) :
    2 * (C : ℝ) * (ue + ue) < (card : ℝ) * (entropyOf C m ue * (1 / 128)) := by
  unfold entropyOf
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have h1 : (card : ℝ) * (4096 * ((C : ℝ) / m) * ue * (1 / 128)) =
      32 * ((card : ℝ) / m) * (C * ue) := by ring
  rw [h1]
  have h2 : 8 ≤ 32 * ((card : ℝ) / m) := by
    rw [← mul_div_assoc, le_div_iff₀ hmR]; linarith
  have h3 : 0 < (C : ℝ) * ue := by positivity
  nlinarith

/-- **The skeleton.** One per-sample producer proves x1080's natural-unit relative row core
contract. -/
theorem relRowCoreNat_of_sample (tune : Tuning) (hS : SampleProducer tune) :
    O204.Tangent.RelRowCoreNatSourceAssertion := by
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS0 hη hρ hdρ
  refine ⟨qualDegree κ₁, one_le_qualDegree κ₁, ?_⟩
  intro Ep precision hprec D₀
  refine ⟨D₀, le_rfl, ?_⟩
  intro J hJ hjet loss hloss hloss1 e0 he0
  obtain ⟨hg, hg8, hub0, hub1, hubgain, hc₀, hc₀1, hgc₀, htol⟩ :=
    choices_ok (Ep := Ep) hκ₁ hκ₁1 hd₁ hd₁1 hprec hloss hloss1 he0
  have hu0 : 0 < ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) / 8 := by positivity
  obtain ⟨m, s, δ₀, C, target, indices, hgrid, hδtol, hδm, hm8, hgm, htarget, hstarget, hm2, hC1,
    hCge, hCle, hCt, hind, hcard, hindices⟩ :=
    exists_relative_grid hκ₁ hρ hg hg8 hu0 hubgain hc₀ hc₀1
      (gridFineOf_pos tune (κ₁ := κ₁) (d₁ := d₁) (Ep := Ep) (precision := precision) hloss hg)
      ((gridFineOf_le_gain tune hloss hloss1 hg).trans hgc₀) htol
  have hgrid' := hgrid
  obtain ⟨-, -, -, hδ0, -, -, -, -, -, -, hδu0, -, -, -⟩ := hgrid'
  refine ⟨m, s, gainOf tune κ₁ d₁ Ep precision loss e0, δ₀,
    ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) / 8, hgrid, gainOf_le_e0, ?_⟩
  intro N K L d W ω ν E P B f g G hpb hprof Mp Dp
  -- the problem as the front reads it
  have hdd : (⟨N, K, L, d, S, η, W, ω, ν, E, P, B, f, g, G⟩ : ProblemData).Valid := hpb
  have hL : 0 < L := hpb.2.2.2.1
  have hδ800 : δ₀ ≤ ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) / 800 := by
    have : ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) / 8 / 100 =
      ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) / 800 := by ring
    linarith
  refine ⟨Mp + 1,
    stripMergedOutputExponent Mp (Mp + ⌈(κ₁ + δ₀) * L⌉₊ + 1)
      ⌈ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * L / 4⌉₊ 1 0, max Dp 1, ?_⟩
  intro Mi Di hMi hDi τ hτ α hα hα1
  obtain ⟨budget, hbud, hbud1, hfront⟩ :=
    FrontAlternative.exists_narrow_or_broad_fraction_envelope (T := Fin 1) hdd hκ₁ m
      (by omega) s δ₀ Mp Dp hub0 hub1 hδ800 le_rfl hubgain target htarget
      (by rw [hstarget]; norm_num) hα 1
  -- the front window
  have hpal0 : 0 ≤ paletteExpOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) L := by
    unfold paletteExpOf
    have : (0 : ℝ) ≤ ((Ep : ℝ) + 1) * precision := by positivity
    have : (0 : ℝ) ≤ tune.depth κ₁ d₁ Ep precision loss :=
      le_trans zero_le_one (tune.one_le_depth κ₁ d₁ Ep precision loss)
    positivity
  have hue0 : 0 < ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ L := by
    unfold ueOf
    have : 0 < 2 * δ₀ * L := by positivity
    linarith
  have hslack : (0 : ℝ) < tune.slack := lt_of_lt_of_le zero_lt_one tune.one_le_slack
  have htau : 0 < tauOf tune δ₀ L budget := lt_min (by positivity) (by positivity)
  have hfr := hfront (fun _ => η * L) (fun _ => ⟨mul_pos hη hL, le_rfl⟩) (tauOf tune δ₀ L budget)
    (tauOf tune δ₀ L budget) htau htau C hC1 indices
    (fun i hi => ⟨(hindices i hi).1, (hindices i hi).2.1⟩)
    (ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ L)
    (ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ L)
    (entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ L))
    (paletteExpOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) L) hue0 hue0.le
    (by unfold entropyOf; have := hue0.le; positivity)
    (gap_ok (by omega) hC1 hue0 hcard) (by unfold ueOf; linarith)
    (fun i hi => (hindices i hi).2.2)
  obtain ⟨σF, hσF, -, hev⟩ := hfr
  obtain ⟨σP, hσP, hevP⟩ := hS hmk d₁ κ₁ ρ Ep precision loss e0 hd₁ hd₁1 hκ₁ hκ₁1 hρ hdρ hprec
    hloss hloss1 he0 m s δ₀ C target indices hgrid hδtol hδm hm8 hgm htarget hstarget hm2 hC1 hCge hCle
    hCt hind _ hdd hprof Mp Dp budget hbud hbud1
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 (hev.and hevP)
  refine ⟨min σF σP, lt_min hσF hσP, k₀, ?_⟩
  intro k hk r T nw κ C' lev par γ j c u Q R A F lst hpath H hH hmass
  have hpp : (⟨r, T, nw, κ, C', lev, par, γ, j, c, u, Q, R, A, F, lst⟩ : PathData (W k)).Valid
      (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp (min σF σP) := hpath
  have hN1 : 1 ≤ N k := le_trans (by norm_num) (hpb.1 k)
  have hppF := PathTolerance.mono hpp hN1 (min_le_left σF σP)
  have hppP := PathTolerance.mono hpp hN1 (min_le_right σF σP)
  have hK1 : 1 ≤ N k ^ budget := Real.one_le_rpow hN1 hbud.le
  obtain ⟨hfk, hPk⟩ := hk₀ k hk
  rcases hfk _ hppF H (fun w => (hH w).1) (fun w => (hH w).2) hmass (N k ^ budget) hK1 le_rfl
    with hnar | ⟨Qp, hpure, hbuf, i, hi, Fp, ⟨Rp, hRmass⟩, hgood⟩
  · exact Or.inl (Or.inr hnar)
  · exact Or.inr (hPk _ hppP H (fun w => (hH w).1) (fun w => (hH w).2) hmass Qp hpure hbuf i hi
      Fp Rp hRmass hgood)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
