import Submission.Obl.k4_scalar_guarded_entropic_path.Interface
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.PowerFullness
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.DensityTails
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChainBudgets
import Submission.Obl.k4_scalar_normalized_exact_refinement.Asymptotics

/-! Narrow selected pieces of an original layer cost power-small mass.
Assignments and earlier true incidence witnesses remain unchanged. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

/-- Only the selected incidences of narrow labels are removed. -/
def narrowEvent {p : RawData} {k : ℕ} (F : Layer (p.1 k)) (ε u : ℝ)
    (g : Fin (p.1 k)) : Set Incidence :=
  {z | ∃ i, F.world i = g ∧ z ∈ F.witness i ∧
    2 * p.N k ^ ε * F.width i * (2 : ℝ) ^ F.T ≤ p.N k ^ (-u)}

variable {p : RawData} {B k : ℕ} {r h ε : ℝ} {flag : Bool}
  {F : Layer (p.1 k)}

theorem measurableSet_narrowEvent
    (hc : ChartData p B r p.L h ε flag k F.T F.n F.world F.block
      F.assignment F.witness F.u F.v F.width F.graph F.list)
    (u : ℝ) (g : Fin (p.1 k)) : MeasurableSet (narrowEvent F ε u g) := by
  classical
  simp only [narrowEvent, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : F.world i = g
  · by_cases hw : 2 * p.N k ^ ε * F.width i * (2 : ℝ) ^ F.T ≤ p.N k ^ (-u)
    · simpa [hi, hw] using (hc.2.2.1 i).2
    · simp only [hw, and_false, Set.ofPred_false, MeasurableSet.empty]
  · simp only [hi, false_and, Set.ofPred_false, MeasurableSet.empty]

/-- The terminal-list fullness estimate applies to the same original
world laws even when the layer's geometric depth is intermediate. -/
theorem weighted_narrowEvent_le (hp : Exact p)
    (hc : ChartData p B r p.L h ε flag k F.T F.n F.world F.block
      F.assignment F.witness F.u F.v F.width F.graph F.list)
    {u : ℝ} (hu : 0 < u) (huU : u ≤ p.U) (τ : ℝ) :
    (∑ g, ENNReal.ofReal (p.weight k g) * mu p k g (narrowEvent F ε u g)) ≤
      (3 * ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) *
        ENNReal.ofReal (p.N k ^ ε)) *
          (∑ g, ENNReal.ofReal (p.weight k g) * mu p k g Set.univ) +
      ∑ g, ENNReal.ofReal (p.weight k g) *
        mu p k g (originalDensityException p k g u τ) := by
  let ρ := fun g => (mu p k g).restrict (narrowEvent F ε u g)
  have hcover (g : Fin (p.1 k)) : ∀ᵐ z ∂ρ g,
      ∃ i, F.world i = g ∧ z ∈ F.witness i ∧
        2 * p.N k ^ ε * F.width i * (2 : ℝ) ^ F.T ≤ p.N k ^ (-u) :=
    ae_restrict_mem (measurableSet_narrowEvent hc u g)
  have hb := ChartData.weighted_narrow_mass_le_power_windows hp hc ρ
    (fun _ => Measure.restrict_le_self) hu huU τ hcover
  simpa only [ρ, Measure.restrict_apply_univ] using hb

/-- Outside the deleted event, an existing cover is a cover by wide
labels with their full earlier witness sets intact. -/
theorem cover_wide_of_not_mem {g : Fin (p.1 k)} {z : Incidence} {u : ℝ}
    (hcover : ∃ i, F.world i = g ∧ z ∈ F.witness i)
    (hnot : z ∉ narrowEvent F ε u g) :
    ∃ i, F.world i = g ∧ z ∈ F.witness i ∧
      p.N k ^ (-u) < 2 * p.N k ^ ε * F.width i * (2 : ℝ) ^ F.T := by
  obtain ⟨i, hi, hz⟩ := hcover
  refine ⟨i, hi, hz, lt_of_not_ge ?_⟩
  exact fun hw => hnot ⟨i, hi, hz, hw⟩

/-- A fixed positive width deficit is power-small, uniformly for any
actual finite layer family whose chart loss is sufficiently small. -/
theorem narrowEvent_powerSmall (hp : Exact p) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (B : ℕ) (r h ε : ℕ → ℝ) (flag : Bool)
    (F : (j : ℕ) → Layer (p.1 (φ j)))
    (hchart : ∀ᶠ j in atTop,
      ChartData p B (r j) p.L (h j) (ε j) flag (φ j)
        (F j).T (F j).n (F j).world (F j).block (F j).assignment
        (F j).witness (F j).u (F j).v (F j).width (F j).graph (F j).list)
    {u : ℝ} (hu : 0 < u) (huU : u ≤ p.U)
    (hε : ∀ᶠ j in atTop, ε j ≤ p.S * u / 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop,
      (∑ g, ENNReal.ofReal (p.weight (φ j) g) *
        mu p (φ j) g (narrowEvent (F j) (ε j) u g)) ≤
          ENNReal.ofReal (p.N (φ j) ^ (-c)) := by
  have hS : 0 < p.S := hp.1.2.2.2.2.2.2.2.2.1
  have hSu : 0 < p.S * u := mul_pos hS hu
  let τ : ℝ := p.S * u / 8
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨c₁, hc₁, htail⟩ := Exact.eventually_originalDensityException_le hp hu huU hτ
  let c : ℝ := min (p.S * u / 2) c₁
  have hc : 0 < c := lt_min (by positivity) hc₁
  let a : ℕ → ℝ≥0∞ := fun j => ∑ g, ENNReal.ofReal (p.weight (φ j) g) *
    mu p (φ j) g (narrowEvent (F j) (ε j) u g)
  have hN2 (j : ℕ) : 2 ≤ p.N (φ j) := hp.1.1 (φ j)
  have hN1 (j : ℕ) : 1 ≤ p.N (φ j) := (by norm_num : (1 : ℝ) ≤ 2).trans (hN2 j)
  have hNt : Tendsto (fun j => p.N (φ j)) atTop atTop := hp.1.2.1.comp hφ.tendsto_atTop
  have hbound : ∀ᶠ j in atTop,
      a j ≤ (5 : ℝ≥0∞) * ENNReal.ofReal (p.N (φ j) ^ (-c)) := by
    filter_upwards [hchart, hε, hφ.tendsto_atTop.eventually htail] with j hj he ht
    have hN : 0 < p.N (φ j) := zero_lt_one.trans_le (hN1 j)
    have hmass : (∑ g, ENNReal.ofReal (p.weight (φ j) g) * mu p (φ j) g univ) ≤ 1 := by
      exact (PathGeometry.PathMeasures.worldMixture_univ p (φ j)).symm.le.trans
        (PathGeometry.PathMeasures.worldMixture_mass_le_one hp (φ j))
    have hfactor : 3 * ENNReal.ofReal (p.N (φ j) ^ (-p.S * u + 2 * τ)) *
        ENNReal.ofReal (p.N (φ j) ^ ε j) ≤
          3 * ENNReal.ofReal (p.N (φ j) ^ (-(p.S * u / 2))) := by
      calc
        _ = 3 * ENNReal.ofReal (p.N (φ j) ^ (-p.S * u + 2 * τ + ε j)) := by
          rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]
        _ ≤ _ := mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_le (hN1 j) (by
            dsimp only [τ]
            linarith only [he])))
    have hpow₀ : ENNReal.ofReal (p.N (φ j) ^ (-(p.S * u / 2))) ≤
        ENNReal.ofReal (p.N (φ j) ^ (-c)) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hN1 j)
        (neg_le_neg (min_le_left _ _)))
    have hpow₁ : ENNReal.ofReal (p.N (φ j) ^ (-c₁)) ≤
        ENNReal.ofReal (p.N (φ j) ^ (-c)) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hN1 j)
        (neg_le_neg (min_le_right _ _)))
    calc
      a j ≤ _ := weighted_narrowEvent_le hp hj hu huU τ
      _ ≤ 3 * ENNReal.ofReal (p.N (φ j) ^ (-(p.S * u / 2))) +
          2 * ENNReal.ofReal (p.N (φ j) ^ (-c₁)) := by
        simpa only [mul_one] using add_le_add (mul_le_mul' hfactor hmass) ht
      _ ≤ 3 * ENNReal.ofReal (p.N (φ j) ^ (-c)) +
          2 * ENNReal.ofReal (p.N (φ j) ^ (-c)) :=
        add_le_add (mul_le_mul' le_rfl hpow₀) (mul_le_mul' le_rfl hpow₁)
      _ = _ := by rw [← add_mul]; norm_num
  refine ⟨c / 2, by positivity, ?_⟩
  apply Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis.powerSmall_of_factor
    hNt hN1 (ε := fun _ => 0) tendsto_const_nhds 5 (by norm_num) hc
  simpa only [Real.rpow_zero, ENNReal.ofReal_one, one_mul] using hbound

end

end Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry
