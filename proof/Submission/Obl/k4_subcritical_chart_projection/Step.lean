import Submission.Obl.k4_subcritical_chart_projection.ScalarPreparation
import Submission.Obl.k4_subcritical_chart_projection.Return
import Submission.Obl.k4_subcritical_chart_projection.ReturnEstimates
import Submission.Obl.k4_subcritical_chart_projection.ThreeLayers
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Mass

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory Filter
open scoped ENNReal BigOperators
open Submission.Obl.k4_horizontal_supercritical_three_projections (ProjectionLayer)

/-- The whole-domain Scalar floors bound the original reference sum of
all returned assignments, before fine slicing. -/
theorem CorrectedLayer.weight_budget {α : Type} [MeasurableSpace α]
    {N K χ D d depth τ : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (ζ : Measure (α × ℝ)) (π : Measure ℝ) (L : CorrectedLayer α)
    (hA : ∀ i, MeasurableSet (L.A i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (L.A i) (L.A j))
    (hfloor : ∀ i, ENNReal.ofReal (L.weight π χ D (N ^ (-depth)) d i / N ^ (2 * τ)) ≤
      ζ (L.A i ×ˢ Icc (0 : ℝ) 1))
    (hmass : ζ univ ≤ ENNReal.ofReal K) :
    ∑ i, L.weight π χ D (N ^ (-depth)) d i ≤ (N ^ τ) ^ 2 * K := by
  classical
  have hdisj' : (↑(Finset.univ : Finset (Fin L.n)) : Set (Fin L.n)).PairwiseDisjoint
      (fun i => L.A i ×ˢ Icc (0 : ℝ) 1) := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro p hp hp'
    exact disjoint_left.mp (hdisj i j hij) hp.1 hp'.1
  have hh := Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.original_reference_budget
    ζ Finset.univ (fun i => L.A i ×ˢ Icc (0 : ℝ) 1)
    (fun i => L.weight π χ D (N ^ (-depth)) d i)
    (Real.rpow_pos_of_pos hN _) hK
    (fun i _ => by unfold CorrectedLayer.weight; positivity)
    (fun i _ => (hA i).prod measurableSet_Icc) hdisj' (fun i _ => hfloor i) hmass
  have hpow : N ^ (2 * τ) = (N ^ τ) ^ (2 : ℕ) := by
    rw [mul_comm (2 : ℝ) τ]
    exact Real.rpow_mul_natCast hN.le τ 2
  simpa [hpow] using hh

/-- The numerical return estimates turn the full corrected Scalar
ensemble into a projection step on every dense submeasure. -/
theorem chart_projection_step (hscalar : Scalar)
    {α : Type} [MeasurableSpace α] (m : Model α)
    (hN : ∀ k, 2 ≤ m.N k) (hNt : Tendsto m.N atTop atTop)
    (hK : ∀ k, 1 ≤ m.K k)
    (hKsub : ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, m.K k ≤ m.N k ^ ξ)
    (hd : 0 ≤ m.d) (hd₁ : m.d < 1) (hκ : 0 < m.κ) (hκ₁ : m.κ ≤ 1)
    (hbasic : m.Basic) (hcaps : m.Caps)
    {s₀ M R : ℝ} (hs₀ : 0 < s₀) (hM : 100 * s₀ < M)
    (depth : Fin 3 → ℝ) (h : Fin 3) (hdepth : s₀ < depth h)
    (hnear : depth h < 3 * s₀ / 2)
    (hreturn : ReturnNumericsRule m M s₀ R (depth h)) :
    ChartProjectionStep m M s₀ R depth h := by
  intro ε hε
  obtain ⟨τ, hτ, ξR, hξR, Hnum⟩ := hreturn ε hε
  obtain ⟨η, hη, ξS, hξS, Hscalar⟩ := corrected_scalar_preparation hscalar m
    hN hNt hK hKsub hd hd₁ hκ hκ₁ hbasic hcaps hs₀ hM depth h hdepth hnear τ hτ
  refine ⟨η, hη, min ξR ξS, lt_min hξR hξS, ?_⟩
  intro ξ hξ hξmax
  have hξR' : ξ ≤ ξR := hξmax.trans (min_le_left _ _)
  have hξS' : ξ ≤ ξS := hξmax.trans (min_le_right _ _)
  filter_upwards [Hnum ξ hξ hξR', Hscalar ξ hξ hξS'] with k hnum Hscalar
  intro C ζ hζ hmass
  obtain ⟨L, hL, hpalette, hfloor, hcovered⟩ := Hscalar C ζ hζ hmass
  obtain ⟨hb, hν, hπ, hμdom, hρμ, hsupp, -⟩ := hbasic k
  have : IsProbabilityMeasure (m.ν k) := hν
  have : IsProbabilityMeasure (m.π k) := hπ
  have hN₁ : 1 ≤ m.N k := by linarith [hN k]
  have hN₀ : 0 < m.N k := by linarith [hN k]
  have hK₀ : 0 ≤ m.K k := by linarith [hK k]
  have hζρ : ζ ≤ m.ρ k := hζ.trans C.le
  have hζμ : ζ ≤ m.μ k := hζρ.trans hρμ
  have hsuppζ : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
    le_antisymm ((hζμ _).trans_eq hsupp) bot_le
  have hmassK : ζ univ ≤ ENNReal.ofReal (m.K k) := by
    simpa only [Set.mem_univ, Set.ofPred_true, measure_univ, mul_one] using
      Submission.Obl.k4_horizontal_supercritical_three_projections.incidence_assignment_bound
        (m.ν k) ζ univ (ENNReal.ofReal (m.K k)) (hζμ.trans hμdom) hsuppζ
  have hweights := L.weight_budget hN₀ hK₀ ζ (m.π k) hL.measurable hL.disjoint hfloor hmassK
  have hbudget : 4 * ∑ i, L.weight (m.π k) (m.N k ^ (-M))
      (m.N k ^ (-(2 * m.κ * s₀))) (m.N k ^ (-depth h)) m.d i ≤ m.N k ^ ε := by
    calc
      _ ≤ 4 * ((m.N k ^ τ) ^ 2 * m.K k) := mul_le_mul_of_nonneg_left hweights (by norm_num)
      _ = 4 * (m.N k ^ τ) ^ 2 * m.K k := by ring
      _ ≤ _ := hnum.budget
  have hD : 0 < m.N k ^ (-(2 * m.κ * s₀)) := Real.rpow_pos_of_pos hN₀ _
  have hD₁ : m.N k ^ (-(2 * m.κ * s₀)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN₁ (by nlinarith)
  obtain ⟨ζ', L', hζ', hcover', hgood, hlost⟩ := refine_corrected_layer hN₁ hD hD₁
    (Real.rpow_pos_of_pos hN₀ _) hnum.fine (Real.rpow_pos_of_pos hN₀ _)
    (Real.rpow_nonneg hN₀.le ξ) (by positivity : 0 ≤ 240 * (m.N k ^ τ) ^ 5)
    (m.b k) hb (m.π k) ζ (m.ρ k) hζρ hsuppζ L hL hpalette
    hnum.corner hnum.norm hnum.fit hnum.coeff hbudget
  refine ⟨L', ζ', hζ', ?_, hcover', ?_⟩
  · let loss := (m.N k ^ ε)⁻¹ * (4 * (m.N k ^ τ) ^ 2 * m.K k)
    apply ENNReal.le_of_add_le_add_right (ENNReal.ofReal_ne_top : ENNReal.ofReal loss ≠ ⊤)
    calc
      _ = ENNReal.ofReal (m.N k ^ (-ε) + loss) := by
        rw [ENNReal.ofReal_add (by positivity) (by dsimp [loss]; positivity)]
      _ ≤ ENNReal.ofReal (m.N k ^ (-2 * τ)) := ENNReal.ofReal_le_ofReal hnum.remaining
      _ ≤ ζ' univ + ENNReal.ofReal ((m.N k ^ ε)⁻¹ *
          (4 * ∑ i, L.weight (m.π k) (m.N k ^ (-M)) (m.N k ^ (-(2 * m.κ * s₀)))
            (m.N k ^ (-depth h)) m.d i)) := hcovered.trans hlost
      _ ≤ _ := by
        apply add_le_add le_rfl
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ 4 * ((m.N k ^ τ) ^ 2 * m.K k) := mul_le_mul_of_nonneg_left hweights (by norm_num)
          _ = _ := by ring
  · simpa only [neg_mul] using hgood

end Submission.Obl.k4_subcritical_chart_projection
