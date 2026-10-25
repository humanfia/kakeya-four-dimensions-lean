-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.CoreLipschitz, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/CoreLipschitz.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/CoreLipschitz.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CorePrediction
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.FrameExpansion

/-!
# Whole-core gradient of the old signal, and its Lipschitz bound in old coordinates

Fix a coherent fine core (packet `b`, local coordinates `Z = K^R (nativeBase - c)`) and an
older packet `old ⊇ b`. Let `g` be the old-signal prediction on the core.

* **Row fit.** If the line of a core incidence `q` returns to the core at the shifted time
  `q.2 + h τ` (`h = 2^{-T_b} K^{-R}`), then `g(Z q + τ (1,V)) = sig_old(q)` up to the
  prediction error `K^14 ε δ_b/δ_old` plus the old signal's motion on the old block, at
  most `4 κ 2^{T_old} h` (Markov).
* **Gradient.** Long rows in renewal cells with strip-broad velocities, together with an
  earlier norming law of the core, bound `‖Dg‖` on the ball of radius `2`
  (`original_quarter_row_gradient_renewal`).
* **Lipschitz in old coordinates.** For two incidences of the core, the frame expansion
  `‖Z z - Z z'‖ ≤ K^R C_f 2^{T_b - T_old} ‖Δ packetBase_old‖` cancels the factor
  `2^{T_old} h` of the row fit: no fine/old clock or width ratio is left in front of the
  old base distance.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric MvPolynomial
open Analytic k4_stable_native_signal_oscillation
open scoped ContDiff

noncomputable section

/-- The time step of the fine local core coordinates. -/
def coreRowStep {W : ℕ} (p : Native.PathData W) (b : Fin p.C) (K : ℝ) (R : ℕ) : ℝ :=
  ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * (K ^ R)⁻¹

/-- The times at which the line of `q` is again in `U`, in core units. -/
def coreRowTimes {W : ℕ} (p : Native.PathData W) (b : Fin p.C) (K : ℝ) (R : ℕ)
    (U : Set Event) (q : Event) : Set ℝ :=
  {τ | (q.1, q.2 + coreRowStep p b K R * τ) ∈ U}

theorem measurableSet_coreRowTimes {W : ℕ} (p : Native.PathData W) (b : Fin p.C) (K : ℝ)
    (R : ℕ) {U : Set Event} (hU : MeasurableSet U) (q : Event) :
    MeasurableSet (coreRowTimes p b K R U q) := by
  have hm : Measurable (fun τ : ℝ => ((q.1, q.2 + coreRowStep p b K R * τ) : Event)) :=
    measurable_const.prodMk (measurable_const.add (measurable_const.mul measurable_id))
  exact hm hU

/-- The norming constants of the degree-24 row renewal, chosen once. -/
def coreRowK₀ : ℝ := Classical.choose (original_quarter_row_gradient_renewal.{0} 24)

def coreRowC₀ : ℝ :=
  Classical.choose (Classical.choose_spec (original_quarter_row_gradient_renewal.{0} 24))

theorem coreRow_spec :
    0 < coreRowK₀ ∧ 1 ≤ coreRowC₀ ∧
    ∀ {D J : ℕ}, ValueJetBound D J →
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ 24 →
      U.totalDegree ≤ 24 → V.totalDegree ≤ 24 → W.totalDegree ≤ 24 →
    ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ) (g : EuclideanSpace ℝ (Fin 3) → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = eval (fun j => z j) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun j => z j) W * F z = eval (fun j => z j) U + eval (fun j => z j) V * s z) →
      ContDiffOn ℂ ∞ F (ball 0 4) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 4 → F (Analytic.DenseJet.realSlice x) = (g x : ℂ)) →
      ContDiffOn ℝ 2 g (ball 0 4) →
      (∀ j : Fin 3, exf D (gradientComponent g j)) →
    ∀ {Ω : Type} [MeasurableSpace Ω]
      (μ₀ : Measure Ω) (μ : (Fin 3 → ℤ) → Measure Ω)
      (vel : Ω → EuclideanSpace ℝ (Fin 2)), Measurable vel →
    ∀ (tests : (Fin 3 → ℤ) → Set Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3))
      (E : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet E →
      E ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4) →
    ∀ (K A B δ β θ ε : ℝ) (q : ℕ), 2 ≤ K → 2 ≤ A → A ≤ K →
      0 ≤ B → B ≤ K → 0 < δ → (K ^ q)⁻¹ ≤ δ → 0 < β →
      0 < θ → θ ≤ 1 → 0 ≤ ε →
      ENNReal.ofReal (β / A) ≤ μ₀ univ →
      (∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U →
        μ₀ (Z ⁻¹' U) ≤ ENNReal.ofReal β * volume U) →
      (∀ᵐ p ∂μ₀, Z p ∈ E) →
    ∀ threshold : (Fin 3 → ℤ) → ENNReal,
      (∀ i, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c : ℝ,
        μ i (vel ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip n c δ) ≤ threshold i) →
      (∀ x ∈ E, threshold (renewalCellCode K J q x) <
        μ (renewalCellCode K J q x) (tests (renewalCellCode K J q x))) →
      (∀ i p, p ∈ tests i → renewalCellCode K J q (Z p) = i) →
      (∀ i p, p ∈ tests i → ‖vel p‖ ≤ B) →
      (∀ i p, p ∈ tests i → ‖Z p‖ ≤ 1 / 4) →
      (∀ i p, p ∈ tests i → eval (fun j => (Analytic.DenseJet.realSlice (Z p)) j) W ≠ 0) →
      (∀ i p, p ∈ tests i → ∃ T : Set ℝ, ∃ intercept : ℝ,
        MeasurableSet T ∧ ENNReal.ofReal θ ≤ volume T ∧
        (∀ t ∈ T, ‖Z p + t • spacetimeDirection (vel p)‖ ≤ 1 / 4) ∧
        ∀ t ∈ T, |g (Z p + t • spacetimeDirection (vel p)) - intercept| ≤ ε) →
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        ‖fderiv ℝ g x‖ ≤ 6 * A ^ J * (1 + (B + 2) / δ) *
          (2 * coreRowK₀ * (1 + 2 * B) * θ ^ (-coreRowC₀) * ε)) ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
        |g y - g x| ≤ 12 * A ^ J * (1 + (B + 2) / δ) *
          (2 * coreRowK₀ * (1 + 2 * B) * θ ^ (-coreRowC₀) * ε) :=
  Classical.choose_spec (Classical.choose_spec (original_quarter_row_gradient_renewal.{0} 24))

/-- The gradient coefficient of the whole-core renewal. -/
def coreGradientCoeff (A δs θ : ℝ) (J : ℕ) : ℝ :=
  6 * A ^ J * (1 + (1 / 2 + 2) / δs) * (2 * coreRowK₀ * (1 + 2 * (1 / 2)) * θ ^ (-coreRowC₀))

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev B profile κ₁ m s δ₀ Mp Dp σ)

include hp

/-- The pointwise facts that a core incidence satisfies. -/
def CoreIncidence (Nk : ℝ) (B : Fin W → ℝ) (p : Native.PathData W) (old b : Fin p.C) (K ε : ℝ)
    (R : ℕ) (center : ℝ) (c : EuclideanSpace ℝ (Fin 3)) (f : Base → ℝ) (q : Event) : Prop :=
  q ∈ p.F b ∧ q ∈ p.F old ∧ |packetSignal Nk p b q - center| ≤ ε ∧
    ‖packetLocalCorePoint Nk B p b K R c q‖ ≤ 1 / 4 ∧
    rootLift (packetNativeValueTest Nk B p b center) (packetNativeCubePoint Nk B p b q) 3 =
      f (packetLocalCorePoint Nk B p b K R c q)

omit hp in
theorem coreIncidence_line_old {old b : Fin p.C} {K ε : ℝ} {R : ℕ} {center : ℝ}
    {c : EuclideanSpace ℝ (Fin 3)} {f : Base → ℝ} {q : Event}
    (hq : CoreIncidence Nk B p old b K ε R center c f q) (hpv : p.Valid Nk L weight ν Ev B
      profile κ₁ m s δ₀ Mp Dp σ) :
    q.1 ∈ p.A old ∧ q.2 ∈ Icc ((p.j old : ℝ) / (2 : ℝ) ^ p.T (p.lev old))
      (((p.j old : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev old)) ∧ q.1 ∈ p.A b := by
  obtain ⟨-, -, hcho⟩ := hpv.2.2.2.2.2.2.2 old
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hFo, _⟩ := hcho
  obtain ⟨-, -, hchb⟩ := hpv.2.2.2.2.2.2.2 b
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hFb, _⟩ := hchb
  exact ⟨(hFo q hq.2.1).2.1, (hFo q hq.2.1).2.2.1, (hFb q hq.1).2.1⟩

/-- **Row fit.** -/
theorem core_row_fit (hNk : 0 < Nk) (old b : Fin p.C) (hB : 0 < B (p.γ b))
    (hγ : p.γ b = p.γ old) (hwidth : δ Nk (p.r (p.lev b)) ≤ δ Nk (p.r (p.lev old)))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K) (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹)
    (center : ℝ) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (f : Base → ℝ) (U : Set Event)
    (hU : ∀ q ∈ U, CoreIncidence Nk B p old b K ε R center c f q)
    (q : Event) (hq : q ∈ U) (τ : ℝ) (hτ : τ ∈ coreRowTimes p b K R U q) :
    ‖packetLocalCorePoint Nk B p b K R c q +
        τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ ≤ 1 / 4 ∧
      |oldSignalCorePrediction Nk B p old b K R c f (packetLocalCorePoint Nk B p b K R c q +
          τ • spacetimeDirection (packetCubeVelocity p b q.1)) -
        eval (xp q.1 q.2) (p.R old) / δ Nk (p.r (p.lev old))| ≤
      K ^ 14 * ε * (δ Nk (p.r (p.lev b)) / δ Nk (p.r (p.lev old))) +
        4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R := by
  have hKpos : 0 < K := by linarith
  have hκ : p.κ ≠ 0 := by linarith [hp.1]
  let q' : Event := (q.1, q.2 + coreRowStep p b K R * τ)
  have hline : packetLocalCorePoint Nk B p b K R c q' =
      packetLocalCorePoint Nk B p b K R c q +
        τ • spacetimeDirection (packetCubeVelocity p b q.1) := by
    have hh := packetLocalCorePoint_line Nk B p b hKpos R hκ c q.1 q.2 τ
    simp only [Prod.mk.eta] at hh
    exact hh
  have hq'U : q' ∈ U := hτ
  obtain ⟨hq'b, hq'o, hq'bin, hq'core, hq'match⟩ := hU q' hq'U
  obtain ⟨hqb, hqo, -, hqcore, -⟩ := hU q hq
  have hfirst : ‖packetLocalCorePoint Nk B p b K R c q +
      τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ ≤ 1 / 4 := by
    rw [← hline]; exact hq'core
  refine ⟨hfirst, ?_⟩
  -- `|τ| ≤ 1/2`
  have hτhalf : |τ| ≤ 1 / 2 := by
    have hcoord : |τ| ≤ ‖τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ := by
      have hh := PiLp.norm_apply_le (τ • spacetimeDirection (packetCubeVelocity p b q.1)) 0
      simpa [spacetimeDirection] using hh
    have hdiff : ‖τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ ≤
        ‖packetLocalCorePoint Nk B p b K R c q +
          τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ +
        ‖packetLocalCorePoint Nk B p b K R c q‖ := by
      calc
        ‖τ • spacetimeDirection (packetCubeVelocity p b q.1)‖ =
            ‖(packetLocalCorePoint Nk B p b K R c q +
              τ • spacetimeDirection (packetCubeVelocity p b q.1)) -
              packetLocalCorePoint Nk B p b K R c q‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  -- prediction at the shifted incidence
  have hpred := path_old_signal_core_prediction_error hp hNk old b hB hγ hwidth hK hκK hε hεK
    center hq'b hq'o hq'bin R c f hq'match
  rw [hline] at hpred
  -- the old signal along the line
  obtain ⟨hlo, hto, -⟩ := coreIncidence_line_old (hU q hq) hp
  obtain ⟨-, hto', -⟩ := coreIncidence_line_old (hU q' hq'U) hp
  have hmarkov := hp.old_signal_line_lipschitz old hlo hto' hto
  have hstep : 0 ≤ coreRowStep p b K R := by unfold coreRowStep; positivity
  have hmove : |q'.2 - q.2| ≤ coreRowStep p b K R * (1 / 2) := by
    rw [show q'.2 - q.2 = coreRowStep p b K R * τ by simp only [q']; ring,
      abs_mul, abs_of_nonneg hstep]
    exact mul_le_mul_of_nonneg_left hτhalf hstep
  have hκ0 : 0 ≤ p.κ := by linarith [hp.1]
  have hmarkov' : |eval (xp q'.1 q'.2) (p.R old) / δ Nk (p.r (p.lev old)) -
      eval (xp q.1 q.2) (p.R old) / δ Nk (p.r (p.lev old))| ≤
      4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R := by
    refine hmarkov.trans ?_
    calc
      _ ≤ 8 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * (coreRowStep p b K R * (1 / 2)) :=
        mul_le_mul_of_nonneg_left hmove (by positivity)
      _ = _ := by ring
  calc
    _ ≤ |oldSignalCorePrediction Nk B p old b K R c f (packetLocalCorePoint Nk B p b K R c q +
            τ • spacetimeDirection (packetCubeVelocity p b q.1)) -
          eval (xp q'.1 q'.2) (p.R old) / δ Nk (p.r (p.lev old))| +
        |eval (xp q'.1 q'.2) (p.R old) / δ Nk (p.r (p.lev old)) -
          eval (xp q.1 q.2) (p.R old) / δ Nk (p.r (p.lev old))| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hpred hmarkov'

/-- **Whole-core gradient of the old signal.** Long rows in strip-broad renewal cells and
an earlier norming law of the core bound the gradient of the prediction on the ball of
radius `2` of the local core coordinates. -/
theorem core_old_signal_gradient (hNk : 0 < Nk) (old b : Fin p.C) (hB : 0 < B (p.γ b))
    (hγ : p.γ b = p.γ old) (hwidth : δ Nk (p.r (p.lev b)) ≤ δ Nk (p.r (p.lev old)))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K) (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹)
    (center : ℝ) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (sign : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
    (hbranch : LocalNativeBranchData 5186 (packetNativeValueTest Nk B p b center)
      (fun j => c j) (K ^ R)⁻¹ sign F f)
    (U : Set Event) (hUm : MeasurableSet U)
    (hU : ∀ q ∈ U, CoreIncidence Nk B p old b K ε R center c f q)
    {D J : ℕ} (hD : 578 ≤ D) (hjets : ValueJetBound D J)
    (μ₀ : Measure Event) (μc : (Fin 3 → ℤ) → Measure Event) (tests : (Fin 3 → ℤ) → Set Event)
    (E : Set Base) (hE : MeasurableSet E) (hEball : E ⊆ closedBall (0 : Base) (1 / 4))
    {Kc A δs β θ : ℝ} {qc : ℕ} (hKc : 2 ≤ Kc) (hA : 2 ≤ A) (hAK : A ≤ Kc)
    (hδs : 0 < δs) (hδfloor : (Kc ^ qc)⁻¹ ≤ δs) (hβ : 0 < β) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hmass₀ : ENNReal.ofReal (β / A) ≤ μ₀ univ)
    (hcap : ∀ V : Set Base, MeasurableSet V →
      μ₀ (packetLocalCorePoint Nk B p b K R c ⁻¹' V) ≤ ENNReal.ofReal β * volume V)
    (hsupp : ∀ᵐ q ∂μ₀, packetLocalCorePoint Nk B p b K R c q ∈ E)
    (threshold : (Fin 3 → ℤ) → ENNReal)
    (hstrip : ∀ i, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c' : ℝ,
      μc i ((fun q : Event => packetCubeVelocity p b q.1) ⁻¹'
        Submission.Lib.K4VelocityStrips.affineStrip n c' δs) ≤ threshold i)
    (hmass : ∀ x ∈ E, threshold (renewalCellCode Kc J qc x) <
      μc (renewalCellCode Kc J qc x) (tests (renewalCellCode Kc J qc x)))
    (hcode : ∀ i q, q ∈ tests i →
      renewalCellCode Kc J qc (packetLocalCorePoint Nk B p b K R c q) = i)
    (htestU : ∀ i q, q ∈ tests i → q ∈ U)
    (hlong : ∀ i q, q ∈ tests i → ENNReal.ofReal θ ≤ volume (coreRowTimes p b K R U q)) :
    ∀ x ∈ closedBall (0 : Base) 2,
      ‖fderiv ℝ (oldSignalCorePrediction Nk B p old b K R c f) x‖ ≤
        coreGradientCoeff A δs θ J *
          (K ^ 14 * ε * (δ Nk (p.r (p.lev b)) / δ Nk (p.r (p.lev old))) +
            4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R) := by
  obtain ⟨-, -, hrow⟩ := coreRow_spec
  obtain ⟨⟨Δ, U', V', Wd, sq, Q, hΔ, hU', hV', hW', hroot, hrep, hQ, hreal, hWd⟩, hg, hgext⟩ :=
    oldSignalCorePrediction_analytic hp hNk old b R center c sign F f hbranch
  have hκ0 : 0 ≤ p.κ := by linarith [hp.1]
  have hεfit : 0 ≤ K ^ 14 * ε * (δ Nk (p.r (p.lev b)) / δ Nk (p.r (p.lev old))) +
      4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R := by
    have h1 : 0 ≤ δ Nk (p.r (p.lev b)) / δ Nk (p.r (p.lev old)) := by
      apply div_nonneg <;> unfold δ <;> positivity
    have h2 : 0 ≤ coreRowStep p b K R := by unfold coreRowStep; positivity
    have h3 : (0 : ℝ) ≤ K ^ 14 := by positivity
    positivity
  have hvel : Measurable (fun q : Event => packetCubeVelocity p b q.1) :=
    (measurable_packetCubeVelocity p b).comp measurable_fst
  have hres := hrow hjets Δ U' V' Wd hΔ hU' hV' hW' sq Q
    (oldSignalCorePrediction Nk B p old b K R c f) hroot hrep hQ hreal hg (hgext D hD)
    μ₀ μc (fun q : Event => packetCubeVelocity p b q.1) hvel tests
    (packetLocalCorePoint Nk B p b K R c) E hE hEball Kc A (1 / 2) δs β θ
    (K ^ 14 * ε * (δ Nk (p.r (p.lev b)) / δ Nk (p.r (p.lev old))) +
      4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R) qc
    hKc hA hAK (by norm_num) (by linarith) hδs hδfloor hβ hθ hθ1 hεfit hmass₀ hcap hsupp
    threshold hstrip hmass hcode
    (fun i q hq => packetCubeVelocity_norm_le_half hp b q.1
      (coreIncidence_line_old (hU q (htestU i q hq)) hp).2.2)
    (fun i q hq => (hU q (htestU i q hq)).2.2.2.1)
    (fun i q hq => hWd _ (by linarith [(hU q (htestU i q hq)).2.2.2.1]))
    (fun i q hq => ⟨coreRowTimes p b K R U q, eval (xp q.1 q.2) (p.R old) / δ Nk (p.r (p.lev old)),
      measurableSet_coreRowTimes p b K R hUm q, hlong i q hq,
      fun t ht => (core_row_fit hp hNk old b hB hγ hwidth hK hκK hε hεK center R c f U hU q
        (htestU i q hq) t ht).1,
      fun t ht => (core_row_fit hp hNk old b hB hγ hwidth hK hκK hε hεK center R c f U hU q
        (htestU i q hq) t ht).2⟩)
  intro x hx
  refine (hres.1 x hx).trans (le_of_eq ?_)
  unfold coreGradientCoeff
  ring

/-- **Lipschitz bound of the old signal in old coordinates.** For any two incidences of the
core, the old signal differs by at most a multiple of `δ_b/δ_old` plus a multiple of the
old base distance. Neither coefficient contains a fine/old clock or width ratio. -/
theorem core_old_signal_lipschitz (hN : 1 ≤ Nk) (hNk : 0 < Nk) (old b : Fin p.C)
    (hB : 0 < B (p.γ b))
    (hγ : p.γ b = p.γ old) (hwidth : δ Nk (p.r (p.lev b)) ≤ δ Nk (p.r (p.lev old)))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K) (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹)
    (center : ℝ) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (sign : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
    (hbranch : LocalNativeBranchData 5186 (packetNativeValueTest Nk B p b center)
      (fun j => c j) (K ^ R)⁻¹ sign F f)
    (U : Set Event)
    (hU : ∀ q ∈ U, CoreIncidence Nk B p old b K ε R center c f q)
    {G : ℝ} (hG0 : 0 ≤ G)
    (hgrad : ∀ x ∈ closedBall (0 : Base) 2,
      ‖fderiv ℝ (oldSignalCorePrediction Nk B p old b K R c f) x‖ ≤
        G * (K ^ 14 * ε * (δ Nk (p.r (p.lev b)) / δ Nk (p.r (p.lev old))) +
          4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R)) :
    ∀ z ∈ U, ∀ z' ∈ U,
      |eval (xp z.1 z.2) (p.R old) / δ Nk (p.r (p.lev old)) -
          eval (xp z'.1 z'.2) (p.R old) / δ Nk (p.r (p.lev old))| ≤
        (2 + G / 2) * (K ^ 14 * ε * (δ Nk (p.r (p.lev b)) / δ Nk (p.r (p.lev old)))) +
          4 * p.κ * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
            ‖packetBase p old z - packetBase p old z'‖ := by
  intro z hz z' hz'
  obtain ⟨hzb, hzo, hzbin, hzcore, hzmatch⟩ := hU z hz
  obtain ⟨hz'b, hz'o, hz'bin, hz'core, hz'match⟩ := hU z' hz'
  set g := oldSignalCorePrediction Nk B p old b K R c f with hgdef
  set err := K ^ 14 * ε * (δ Nk (p.r (p.lev b)) / δ Nk (p.r (p.lev old))) with herr
  have hκ0 : 0 ≤ p.κ := by linarith [hp.1]
  have herr0 : 0 ≤ err := by
    have h1 : 0 ≤ δ Nk (p.r (p.lev b)) / δ Nk (p.r (p.lev old)) := by
      apply div_nonneg <;> unfold δ <;> positivity
    have h3 : (0 : ℝ) ≤ K ^ 14 := by positivity
    rw [herr]; positivity
  have hstep0 : 0 ≤ coreRowStep p b K R := by unfold coreRowStep; positivity
  have hfit0 : 0 ≤ err + 4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R := by
    positivity
  -- predictions at the two incidences
  have hpz := path_old_signal_core_prediction_error hp hNk old b hB hγ hwidth hK hκK hε hεK
    center hzb hzo hzbin R c f hzmatch
  have hpz' := path_old_signal_core_prediction_error hp hNk old b hB hγ hwidth hK hκK hε hεK
    center hz'b hz'o hz'bin R c f hz'match
  -- mean value inequality on the ball of radius 2
  obtain ⟨-, hgsmooth, -⟩ := oldSignalCorePrediction_analytic hp hNk old b R center c sign F f
    hbranch
  have hdiff : ∀ x ∈ closedBall (0 : Base) 2, DifferentiableAt ℝ g x := by
    intro x hx
    have hx4 : x ∈ ball (0 : Base) 4 := by
      rw [mem_closedBall, dist_zero_right] at hx
      rw [mem_ball, dist_zero_right]
      linarith
    exact (hgsmooth.contDiffAt (isOpen_ball.mem_nhds hx4)).differentiableAt (by norm_num)
  have hzmem : packetLocalCorePoint Nk B p b K R c z ∈ closedBall (0 : Base) 2 := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hz'mem : packetLocalCorePoint Nk B p b K R c z' ∈ closedBall (0 : Base) 2 := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hgrad
    (convex_closedBall (0 : Base) 2) hz'mem hzmem
  rw [Real.norm_eq_abs] at hmv
  -- distance of the two local points
  set dZ := ‖packetLocalCorePoint Nk B p b K R c z - packetLocalCorePoint Nk B p b K R c z'‖
    with hdZ
  have hdZhalf : dZ ≤ 1 / 2 := by
    rw [hdZ]
    calc
      _ ≤ ‖packetLocalCorePoint Nk B p b K R c z‖ + ‖packetLocalCorePoint Nk B p b K R c z'‖ :=
        norm_sub_le _ _
      _ ≤ 1 / 2 := by linarith
  obtain ⟨hlo, -, hlb⟩ := coreIncidence_line_old (hU z hz) hp
  have hexp := hp.local_core_expansion hN old b (by linarith : (0 : ℝ) ≤ K) R c z z' hlb hlo
  rw [← hdZ] at hexp
  -- the cancellation of the clock and core scales
  have hcancel : 4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R *
      (K ^ R * ((1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
        ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev old)))) =
      4 * p.κ * (1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) := by
    unfold coreRowStep
    have hK0 : K ^ R ≠ 0 := pow_ne_zero _ (by linarith)
    have hT1 : (2 : ℝ) ^ p.T (p.lev b) ≠ 0 := by positivity
    have hT2 : (2 : ℝ) ^ p.T (p.lev old) ≠ 0 := by positivity
    field_simp
  have hsplit : G * (err + 4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R) * dZ ≤
      G / 2 * err + 4 * p.κ * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
        ‖packetBase p old z - packetBase p old z'‖ := by
    have hA : G * err * dZ ≤ G / 2 * err := by
      have := mul_le_mul_of_nonneg_left hdZhalf (mul_nonneg hG0 herr0)
      linarith
    have hB' : G * (4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R) * dZ ≤
        4 * p.κ * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
          ‖packetBase p old z - packetBase p old z'‖ := by
      have hpos : 0 ≤ G * (4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R) := by
        positivity
      calc
        _ ≤ G * (4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R) *
            (K ^ R * ((1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
              ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev old))) *
              ‖packetBase p old z - packetBase p old z'‖) :=
          mul_le_mul_of_nonneg_left hexp hpos
        _ = G * (4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R *
            (K ^ R * ((1 + 4 * p.κ + 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) *
              ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev old))))) *
              ‖packetBase p old z - packetBase p old z'‖ := by ring
        _ = _ := by rw [hcancel]; ring
    have hexpand : G * (err + 4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R) * dZ =
        G * err * dZ + G * (4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R) * dZ := by
      ring
    rw [hexpand]
    exact add_le_add hA hB'
  calc
    _ ≤ |eval (xp z.1 z.2) (p.R old) / δ Nk (p.r (p.lev old)) -
          g (packetLocalCorePoint Nk B p b K R c z)| +
        |g (packetLocalCorePoint Nk B p b K R c z) - g (packetLocalCorePoint Nk B p b K R c z')| +
        |g (packetLocalCorePoint Nk B p b K R c z') -
          eval (xp z'.1 z'.2) (p.R old) / δ Nk (p.r (p.lev old))| := by
      have h1 := abs_sub_le (eval (xp z.1 z.2) (p.R old) / δ Nk (p.r (p.lev old)))
        (g (packetLocalCorePoint Nk B p b K R c z))
        (eval (xp z'.1 z'.2) (p.R old) / δ Nk (p.r (p.lev old)))
      have h2 := abs_sub_le (g (packetLocalCorePoint Nk B p b K R c z))
        (g (packetLocalCorePoint Nk B p b K R c z'))
        (eval (xp z'.1 z'.2) (p.R old) / δ Nk (p.r (p.lev old)))
      linarith
    _ ≤ err + G * (err + 4 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * coreRowStep p b K R) * dZ +
        err := by
      refine add_le_add (add_le_add ?_ hmv) hpz'
      rw [abs_sub_comm]
      exact hpz
    _ ≤ _ := by linarith [hsplit]

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
