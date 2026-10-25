import Mathlib

/-!
# Static scalar charts and coefficient-bin regularization

Adapted from: here:o202 (session x0952).
The input, relative-cap and StageBin interface definitions are adapted from this LOT tree,
obligation o245, session x0931 (branch x0931, Regularization.lean, FirstJet/Statement.lean,
Reg/Stages.lean). Only the coefficient-bin stage is formalized in this library.
-/

namespace Submission.Lib.K4CoefficientBinRegularization

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable section
namespace FirstJet
/-- The normalized scalar `x̄_l(t) = β_l + t γ_l`. -/
def xbar {Ω : Type*} (β γ : Ω → ℝ) (l : Ω) (t : ℝ) : ℝ := β l + t * γ l

/-- The scalar `S_l(t) = x̄_l(t) - F(t) · y_l`. -/
def scal {Ω : Type*} (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (F : ℝ → Fin 2 → ℝ) (l : Ω) (t : ℝ) :
    ℝ :=
  xbar β γ l t - (F t 0 * y l 0 + F t 1 * y l 1)


end FirstJet

/-- The two estimates obtained from the raw geometry, after density cutoff and
line/time-bin duration preparation. The trajectory prior is fixed throughout.
All later label selections restrict `E` and preserve these upper bounds. -/
structure UnregularizedChart {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ)
    (d K ζ : ℝ) : Prop where
  measurable_y : Measurable y
  measurable_β : Measurable β
  measurable_γ : Measurable γ
  measurable_F : Measurable F
  measurableSet_E : MeasurableSet E
  subset_E : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1
  bound_y : ∀ l i, |y l i| ≤ K
  bound_β : ∀ l, |β l| ≤ K
  bound_γ : ∀ l, |γ l| ≤ K
  bound_F : ∀ t i, |F t i| ≤ K
  mass : ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E
  mixedCap : ∀ t r w : ℝ, ζ ≤ r → r ≤ 1 → ζ ≤ w → w ≤ 1 →
    ∀ (z : Fin 2 → ℤ) (j : ℤ),
    ν {l | (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / w⌋ = j ∧
      ⌊y l 0 / r⌋ = z 0 ∧ ⌊y l 1 / r⌋ = z 1} ≤ ENNReal.ofReal (K * r ^ 2 * w ^ d)
  support : ∀ t w : ℝ, ζ ≤ w → w ≤ 1 →
    ∃ C : Finset ℤ, (C.card : ℝ) ≤ K * w ^ (-d) ∧
      ∀ l, (l, t) ∈ E → ⌊FirstJet.scal y β γ F l t / w⌋ ∈ C

/-- Both geometric upper estimates pass to an arbitrary measurable sublabel set. -/
theorem UnregularizedChart.restrict_labels {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E E' : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (h : UnregularizedChart ν y β γ E F d K ζ) (hE' : MeasurableSet E')
    (hsub : E' ⊆ E) (hmass : ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E') :
    UnregularizedChart ν y β γ E' F d K ζ := by
  refine { h with
    measurableSet_E := hE'
    subset_E := hsub.trans h.subset_E
    mass := hmass
    mixedCap := ?_
    support := ?_ }
  · intro t r w hr hr1 hw hw1 z j
    apply le_trans (measure_mono ?_) (h.mixedCap t r w hr hr1 hw hw1 z j)
    rintro l ⟨hl, hx, hy0, hy1⟩
    exact ⟨hsub hl, hx, hy0, hy1⟩
  · intro t w hw hw1
    obtain ⟨C, hC, hcover⟩ := h.support t w hw hw1
    exact ⟨C, hC, fun l hl => hcover l (hsub hl)⟩

/-- A smaller raw hypothesis loss also meets every larger positive bound. -/
theorem UnregularizedChart.mono_bound {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K H ζ : ℝ}
    (h : UnregularizedChart ν y β γ E F d K ζ) (hK : 0 < K) (hKH : K ≤ H)
    (hζ : 0 ≤ ζ) : UnregularizedChart ν y β γ E F d H ζ := by
  refine { h with
    bound_y := fun l i => (h.bound_y l i).trans hKH
    bound_β := fun l => (h.bound_β l).trans hKH
    bound_γ := fun l => (h.bound_γ l).trans hKH
    bound_F := fun t i => (h.bound_F t i).trans hKH
    mass := (ENNReal.ofReal_le_ofReal (inv_anti₀ hK hKH)).trans h.mass
    mixedCap := ?_
    support := ?_ }
  · intro t r w hr hr1 hw hw1 z j
    apply (h.mixedCap t r w hr hr1 hw hw1 z j).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKH (sq_nonneg _)) (Real.rpow_nonneg (hζ.trans hw) _)
  · intro t w hw hw1
    obtain ⟨C, hC, hcover⟩ := h.support t w hw hw1
    exact ⟨C, hC.trans (mul_le_mul_of_nonneg_right hKH (Real.rpow_nonneg (hζ.trans hw) _)), hcover⟩


namespace Reg
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Local scalar counts (the `support` field of `FirstJet.Data`). -/
def LocalCounts (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ)
    (d K ζ : ℝ) : Prop :=
  ∀ t q r a : ℝ, ζ ≤ q → q ≤ r → r ≤ 1 →
    ∃ C : Finset ℤ, (C.card : ℝ) ≤ K * (r / q) ^ d ∧
      ∀ l, (l, t) ∈ E → a ≤ FirstJet.scal y β γ F l t → FirstJet.scal y β γ F l t ≤ a + r →
        ⌊FirstJet.scal y β γ F l t / q⌋ ∈ C

/-- The row comparison (the `rowLip` field of `FirstJet.Data`). -/
def RowComparison (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ) (K ζ : ℝ) : Prop :=
  ∀ t u : ℝ, (∃ l, (l, t) ∈ E) → (∃ l, (l, u) ∈ E) → ∀ i,
    |F t i - F u i| ≤ K * (|t - u| + ζ)

/-- The slope comparison (the `slopeLip` field of `FirstJet.Data`). -/
def SlopeComparison (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (K ζ : ℝ) : Prop :=
  ∀ l l' t u, (l, t) ∈ E → (l', u) ∈ E →
    |γ l - γ l'| ≤ K * (|t - u| + |FirstJet.xbar β γ l t - FirstJet.xbar β γ l' u| +
      |y l 0 - y l' 0| + |y l 1 - y l' 1| + ζ)

/-- The relative dyadic coefficient-bin caps (the `binCap` field of `FirstJet.Data`). -/
def BinCaps (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ))
    (d K ζ : ℝ) : Prop :=
  ∀ (q : ℝ) (n : ℕ), ζ ≤ q → q ≤ (2 : ℝ) ^ (-(n : ℤ)) → ∀ (b : Fin 4 → ℤ) (t : ℝ)
    (z : Fin 3 → ℤ),
    ν {l | (⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧
        ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3) ∧
        (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / q⌋ = z 0 ∧ ⌊y l 0 / q⌋ = z 1 ∧
        ⌊y l 1 / q⌋ = z 2} ≤
      ENNReal.ofReal (K * (q / (2 : ℝ) ^ (-(n : ℤ))) ^ (2 + d)) *
        ν {l | ⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧
          ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3}

theorem BinCaps.mono {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E E' : Set (Ω × ℝ)}
    {d K K' ζ : ℝ} (h : BinCaps ν y β γ E d K ζ) (hE : E' ⊆ E) (hK : K ≤ K') (hζ : 0 < ζ) :
    BinCaps ν y β γ E' d K' ζ := by
  intro q n hq hqn b t z
  have hq0 : 0 < q := hζ.trans_le hq
  refine (measure_mono ?_).trans ((h q n hq hqn b t z).trans ?_)
  · rintro l ⟨hb, hl, hz⟩
    exact ⟨hb, hE hl, hz⟩
  · gcongr

/-- The absolute cap of `FirstJet.Data` is the mixed cap at equal widths. -/
theorem absCap_of_mixedCap {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ}
    {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (h : UnregularizedChart ν y β γ E F d K ζ) (hζ : 0 < ζ) (t q : ℝ) (hq : ζ ≤ q)
    (hq1 : q ≤ 1) (z : Fin 3 → ℤ) :
    ν {l | (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / q⌋ = z 0 ∧ ⌊y l 0 / q⌋ = z 1 ∧
      ⌊y l 1 / q⌋ = z 2} ≤ ENNReal.ofReal (K * q ^ (2 + d)) := by
  have hq0 : 0 < q := hζ.trans_le hq
  have key := h.mixedCap t q q hq hq1 hq hq1 ![z 1, z 2] (z 0)
  have e : K * q ^ 2 * q ^ d = K * q ^ (2 + d) := by
    rw [Real.rpow_add hq0, Real.rpow_two]; ring
  rw [e] at key
  simpa using key

/-- Stage 4: the relative dyadic coefficient-bin caps. -/
def StageBin : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω), IsProbabilityMeasure ν →
      ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ),
        UnregularizedChart ν y β γ E F d (N ^ η) (N ^ (-c)) →
        LocalCounts y β γ E F d (N ^ η) (N ^ (-c)) → RowComparison E F (N ^ η) (N ^ (-c)) →
        SlopeComparison y β γ E (N ^ η) (N ^ (-c)) →
        ∃ E' : Set (Ω × ℝ), E' ⊆ E ∧ UnregularizedChart ν y β γ E' F d (N ^ ε) (N ^ (-c)) ∧
          BinCaps ν y β γ E' d (N ^ ε) (N ^ (-c))


/-- Bins whose full original prior mass falls below a specified threshold. -/
def lightCodeSet {X I : Type*} [MeasurableSpace X] (ν : Measure X) (code : X → I)
    (τ : I → ℝ≥0∞) : Set X := {l | ν {l' | code l' = code l} < τ (code l)}

/-- A measurable discrete code makes its original light-bin deletion measurable. -/
theorem measurableSet_lightCodeSet {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] (ν : Measure X) (code : X → I)
    (τ : I → ℝ≥0∞) (hcode : Measurable code) : MeasurableSet (lightCodeSet ν code τ) := by
  have hm : Measurable (fun i : I => ν {l' | code l' = i}) := measurable_of_countable _
  have ht : Measurable τ := measurable_of_countable _
  exact measurableSet_lt (hm.comp hcode) (ht.comp hcode)

end Reg
end
end Submission.Lib.K4CoefficientBinRegularization
