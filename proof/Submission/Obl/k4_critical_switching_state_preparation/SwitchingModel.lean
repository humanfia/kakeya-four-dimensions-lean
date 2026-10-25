/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/SwitchingModel.lean.
   Existing source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.SourceRegularity

namespace Submission.Obl.k4_critical_switching_state_preparation

open MeasureTheory Set Filter Inherited

noncomputable section

/-- A local horizontal probability law, with bounds on its FINAL time
conditionals and FINAL switching-state velocity conditionals. The indexed
trajectory space is arbitrary; no disintegration on that space is assumed. -/
def HorizontalLaw {α : Type} [MeasurableSpace α]
    (N a S δ : ℝ) (σ : Measure (α × ℝ)) (π : Measure ℝ)
    (x : α → ℝ → Fin 3 → ℝ) (vel : α → ℝ) (bin : α → ℤ)
    (state : α × ℝ → ℕ) (G : Set (α × ℝ)) : Prop :=
  IsProbabilityMeasure σ ∧ IsProbabilityMeasure π ∧
  Measurable (Function.uncurry x) ∧ Measurable vel ∧ Measurable bin ∧
  Measurable state ∧ MeasurableSet G ∧ σ Gᶜ = 0 ∧
  σ ≤ ENNReal.ofReal (N ^ δ) • ((σ.map Prod.fst).prod volume) ∧
  (∀ p ∈ G, p.2 ∈ Icc (0 : ℝ) 1 ∧ |vel p.1| ≤ N ^ δ ∧
    (∀ t ∈ Icc (0 : ℝ) 1, x p.1 t 0 = t ∧ ∀ e, |x p.1 t e| ≤ N ^ δ) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      x p.1 u 1 = x p.1 t 1 + vel p.1 * (u - t) ∧
      |x p.1 u 2 - x p.1 t 2 - (-x p.1 t 1 + t * vel p.1) * (u - t)| ≤
        N ^ (-20 * a)) ∧
  (∀ p ∈ G, ∀ q ∈ G, state p = state q →
    bin p.1 = bin q.1 ∧ ∀ e, |x p.1 p.2 e - x q.1 q.2 e| ≤ N ^ (-20 * a)) ∧
  (∀ (q : ℕ) (j : ℤ),
    σ {p | state p = q ∧ ⌊vel p.1 / N ^ (-20 * a)⌋ = j} ≤
      ENNReal.ofReal (N ^ δ) * σ {p | state p = q} *
        π {w | ⌊w / N ^ (-20 * a)⌋ = j}) ∧
  (∀ z r : ℝ, N ^ (-20 * a) ≤ r → r ≤ 1 →
    π (Icc (z - r) (z + r)) ≤ ENNReal.ofReal (N ^ δ * r ^ S))

/-- The geometric child has no original-model assumptions: it spreads
intercept bins of a prepared local law using three horizontal traversals. -/
def LocalSpreading : Prop :=
  ∀ S a ε : ℝ, 0 < S → 0 < a → 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α]
        (σ : Measure (α × ℝ)) (π : Measure ℝ)
        (x : α → ℝ → Fin 3 → ℝ) (vel : α → ℝ) (bin : α → ℤ)
        (state : α × ℝ → ℕ) (G : Set (α × ℝ)),
        HorizontalLaw N a S δ σ π x vel bin state G →
        ∀ F : Finset (ℤ × (Fin 3 → ℤ)),
          (∀ᵐ p ∂σ, (bin p.1, fun e => ⌊x p.1 p.2 e / N ^ (-a)⌋) ∈ F) →
          ∃ j : ℤ, ENNReal.ofReal
            (N ^ (-ε) / ((F.card : ℝ) * (N ^ (-a)) ^ 3)) ≤
              σ {p | bin p.1 = j}

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

def centeredLine (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (l : α) (t : ℝ) : Fin 3 → ℝ :=
  cfg.framedPoint k s i (l, cfg.blockLeft k s i + cfg.timeLength k s * t)

def centeredVelocity (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (l : α) : ℝ :=
  cfg.b k l 3 - cfg.c k s i 1

def midpointBin (k : ℕ) (s v : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) (l : α) : ℤ :=
  ⌊cfg.midpointValue k s i L (l, 0) / cfg.N k ^ (-s - v)⌋

/-- Joint preparation uses the already proved original-source pair count.
Its new content is the simultaneous final-law time and state conditioning.
The last inequality transports EACH bin to original rho and FULL nu(A). -/
def PreparedSwitching (k : ℕ) (s η δ : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) : Prop :=
  ∃ (source : Set (α × ℝ)) (σ : Measure (α × ℝ)) (π₀ : Measure ℝ)
    (state : α × ℝ → ℕ) (G : Set (α × ℝ))
    (F : Finset (ℤ × (Fin 3 → ℤ))),
    MeasurableSet source ∧
    source ⊆ cfg.primitiveEvent k s i L (cfg.N k ^ η * cfg.N k ^ (-s)) ∧
    (∀ p ∈ source, ∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * cfg.K k) ∧
    HorizontalLaw (cfg.N k) (10 * s) cfg.S δ σ π₀
      (cfg.centeredLine k s i) (cfg.centeredVelocity k s i)
      (cfg.midpointBin k s (s / 16) i L) state G ∧
    (∀ᵐ p ∂σ, (cfg.midpointBin k s (s / 16) i L p.1,
      fun e => ⌊cfg.centeredLine k s i p.1 p.2 e / cfg.N k ^ (-10 * s)⌋) ∈ F) ∧
    (F.card : ℝ) * (cfg.N k ^ (-10 * s)) ^ 3 ≤
      cfg.N k ^ (cfg.d * (s / 16) + δ) ∧
    (∀ j : ℤ,
      (ENNReal.ofReal (cfg.N k ^ (-δ) / (2 : ℝ) ^ cfg.T k s) *
        cfg.ν k (cfg.A k s i)) *
          σ {p | cfg.midpointBin k s (s / 16) i L p.1 = j} ≤
      cfg.ρ k (source ∩ {p | cfg.midpointBin k s (s / 16) i L p.1 = j}))

end Data

/-- Preparation at a fixed small depth and arbitrary requested loss. The
primitive is used with the smaller loss eta chosen BEFORE k, i, and L. -/
def SwitchingPreparation : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Valid →
    ∀ s : ℝ, 0 < s → 1000 * s < cfg.U → 1000 * s < cfg.e₀ → s < 1 →
      ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧
        ∀ᶠ k in atTop, ∀ (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ),
          L 0 = 0 →
          (∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ η * (2 : ℝ) ^ cfg.T k s) →
          ENNReal.ofReal (cfg.N k ^ (-η) / (2 : ℝ) ^ cfg.T k s) *
            cfg.ν k (cfg.A k s i) ≤
              cfg.ρ k (cfg.primitiveEvent k s i L (cfg.N k ^ η * cfg.N k ^ (-s))) →
          cfg.PreparedSwitching k s η δ i L

end

end Submission.Obl.k4_critical_switching_state_preparation
