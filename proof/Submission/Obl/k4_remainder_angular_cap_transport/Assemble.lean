import Submission.Obl.k4_remainder_angular_cap_transport.FiniteTransfer
import Submission.Obl.k4_profile_density_bounds.Asymptotics

set_option linter.unusedVariables false
set_option maxRecDepth 10000

namespace Submission.Obl.k4_remainder_angular_cap_transport
open MeasureTheory Set Filter
open scoped ENNReal

theorem transport : ∀ (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ) (g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), prob N K L d S η W ω ν E P B f g G → ∀ r h cap : ℝ, 0 ≤ r → r < L → ∀ (M D : ℕ) (ψ : ℕ → ℕ) (κ : ℕ → ℝ) (T C : ℕ → ℕ) (γ : (k : ℕ) → Fin (C k) → Fin (W (ψ k))) (j : (k : ℕ) → Fin (C k) → Fin (2 ^ T k)) (c u : (k : ℕ) → Fin (C k) → EuclideanSpace ℝ (Fin 2)) (Q : (k : ℕ) → Fin (C k) → Matrix (Fin 2) (Fin 2) ℝ) (R : (k : ℕ) → Fin (C k) → MvPolynomial (Fin 4) ℝ) (A : (k : ℕ) → Fin (C k) → Set (ℕ × (Fin 6 → ℝ))) (F : (k : ℕ) → Fin (C k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (K₂ : ℕ → ℝ) (E₂ : (k : ℕ) → Fin (C k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (f₂ : ℝ → ℝ) (g₂ : (k : ℕ) → Fin (C k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (G₂ : (k : ℕ) → Fin (C k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), seq N K L W ω ν E B f r h M D ψ κ T C γ j c u Q R A F → rem N K L W ω ν E B f r h M D ψ κ T C γ j c u Q R A F S η cap K₂ E₂ f₂ g₂ G₂ → angular (fun k => N (ψ k)) K₂ (L - r) cap S η C (fun k b => ω (ψ k) (γ k b) * ((ν (ψ k) (γ k b) (A k b)).toReal / (2 : ℝ) ^ T k) / (normalizer (W (ψ k)) (ω (ψ k)) (ν (ψ k)) (T k) (C k) (γ k) (A k))) (fun k b => (ν (ψ k) (γ k b) (A k b))⁻¹ • MeasureTheory.Measure.map (norm (((j k b : ℕ) : ℝ) / (2 : ℝ) ^ T k) (1 / (2 : ℝ) ^ T k) (c k b) (u k b) (Q k b)) ((ν (ψ k) (γ k b)).restrict (A k b))) E₂ (fun k b => native (((j k b : ℕ) : ℝ) / (2 : ℝ) ^ T k) (1 / (2 : ℝ) ^ T k) (c k b) (u k b) (Q k b) (δ (N (ψ k)) r) (R k b)) (fun k b => B (ψ k) (γ k b) / δ (N (ψ k)) r) f₂ g₂ G₂ := by
  classical
  intro N K L d S η W ω ν E P B f g G hp r h cap hr hrL M D ψ κ T C γ j c u Q R A F
    K₂ E₂ f₂ g₂ G₂ hs hrem
  rcases hp with ⟨hp, hangular⟩
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη,
    hmodel, hg, hG, hprofile, htyp, hcap, _⟩
  rcases hs with ⟨hψ, hκone, hκambient, hκsub, htime, hsys⟩
  rcases hrem with ⟨hp₂, hE₂sub, hpos, hZsub, hcomp⟩
  rcases hp₂ with ⟨_, _, _, _, _, _, _, _, hmodel₂, _, hG₂, _, _, _, _⟩
  obtain ⟨M₀, D₀, hmodel⟩ := hmodel
  obtain ⟨M₂, D₂, hmodel₂⟩ := hmodel₂
  let s : (k : ℕ) → Geometry.ChartSystem (W (ψ k)) (T k) := fun k =>
    { count := C k, world := γ k, block := j k, center := c k, speed := u k,
      frame := Q k, test := R k, assignment := A k, event := F k }
  have hworld : ∀ k b, IsProbabilityMeasure (ν k b) ∧ MeasurableSet (E k b) ∧
      E k b ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
    intro k b
    rcases (hmodel k).2.2.2.1 b with ⟨hp, _, _, _, _, _, _, hE, hEs, _⟩
    exact ⟨hp, hE, hEs⟩
  have hworld₂ : ∀ k b, IsProbabilityMeasure ((s k).normPrior (ν (ψ k)) b) ∧
      MeasurableSet (E₂ k b) ∧ E₂ k b ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
    intro k b
    rcases (hmodel₂ k).2.2.2.1 b with ⟨hp, _, _, _, _, _, _, hE, hEs, _⟩
    exact ⟨hp, hE, hEs⟩
  letI : ∀ k b, IsProbabilityMeasure (ν k b) := fun k b => (hworld k b).1
  letI : ∀ k b, IsProbabilityMeasure ((s k).normPrior (ν (ψ k)) b) :=
    fun k b => (hworld₂ k b).1
  letI : ∀ k b, IsFiniteMeasure ((((s k).normPrior (ν (ψ k)) b).prod volume).restrict (E₂ k b)) := by
    intro k b
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    calc
      _ ≤ (((s k).normPrior (ν (ψ k)) b).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) :=
        measure_mono (hworld₂ k b).2.2
      _ < ⊤ := by simp
  change ∀ u₀ τ : ℝ, 0 < u₀ → u₀ ≤ η * (L - r) → 0 < τ → _
  intro u₀ τ hu hule hτ
  have huold : u₀ ≤ η * L := hule.trans (mul_le_mul_of_nonneg_left (by linarith) hη.le)
  obtain ⟨c₀, hc₀, htail⟩ := hangular u₀ (τ / 4) hu huold (by positivity)
  have hNt' : Tendsto (fun k => N (ψ k)) atTop atTop := hNt.comp hψ.tendsto_atTop
  have hfactor := k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => show 1 ≤ N (ψ k) by linarith [hN (ψ k)]) hNt' hκone hκsub 2
    (show τ / 2 < τ by linarith) (A := 100) (by norm_num)
  have hdecay := k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt'
    (show -3 * c₀ / 4 < -(c₀ / 2) by linarith) 4
  refine ⟨c₀ / 2, by positivity, ?_⟩
  filter_upwards [hψ.tendsto_atTop.eventually htail, hfactor,
    hcomp (τ / 4) (by positivity), hZsub (c₀ / 4) (by positivity), hdecay]
    with k hkold hkfactor hkcomp hkZ hkdecay
  have hNk : 0 < N (ψ k) := by linarith [hN (ψ k)]
  obtain ⟨lst, hC, hsep, hlist, hchart, hmass⟩ := hsys k
  have hchartdata : ∀ b,
      (Q k b).det ≠ 0 ∧
      (∑ i : Fin 2, ∑ j : Fin 2, |Q k b i j|) ≤ κ k / (2 : ℝ) ^ T k ∧
      MeasurableSet (A k b) ∧ MeasurableSet (F k b) ∧
      ∀ p ∈ F k b, p ∈ E (ψ k) (γ k b) ∧ p.1 ∈ A k b ∧
        p.2 ∈ Geometry.timeBlock (T k) (j k b) := by
    intro b
    rcases hchart b with ⟨hD, _, _, hQ, _, _, hA, hF, _, _, hinc, _⟩
    exact ⟨hD, hQ, hA, hF, fun p hp =>
      ⟨(hinc p hp).1, (hinc p hp).2.1, (hinc p hp).2.2.1⟩⟩
  have hω : ∀ b, 0 ≤ ω (ψ k) b := (hmodel (ψ k)).2.1
  have hZ : 0 < (s k).normZ (ω (ψ k)) (ν (ψ k)) :=
    ((s k).normZ_inv_le (ω (ψ k)) (ν (ψ k)) hω
      (fun b p hp => ((hchartdata b).2.2.2.2 p hp).2)
      (show 0 < κ k by linarith [hκone k]) hmass).1
  obtain ⟨m, hm, hm2, hwidth⟩ := terminal_width_ratio (N (ψ k)) L r
  have htarget : ∀ b,
      ENNReal.ofReal (100 * κ k ^ 2) * ENNReal.ofReal (N (ψ k) ^ (-f L - S * u₀ + τ / 4)) *
        ENNReal.ofReal (|(Q k b).det| / (ν (ψ k) (γ k b) (A k b)).toReal) ≤
      ENNReal.ofReal (N (ψ k) ^ (-f₂ (L - r) - S * u₀ + τ)) := by
    intro b
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (threshold_le (by linarith [hN (ψ k)]) (hpos k b)
      (hkcomp b) hkfactor.le)
  have hfinite := finite_angular_tail (s k) (ω (ψ k)) (ν (ψ k)) (E (ψ k)) (B (ψ k)) hω hZ
    (fun b => (hworld (ψ k) b).2.1) (fun b => (hchartdata b).1)
    (fun b => (hchartdata b).2.2.1) (fun b => (hchartdata b).2.2.2.1) (hpos k) hsep
    (fun b => (hchartdata b).2.2.2.2)
    (κ k) (δ (N (ψ k)) r) (δ (N (ψ k)) (L - r)) (δ (N (ψ k)) L)
      (δ (N (ψ k)) u₀) (hκone k) (by unfold δ; positivity) (by unfold δ; positivity)
    (fun b => (hchartdata b).2.1) hm hm2 hwidth (E₂ k) (hE₂sub k)
    (fun b => G (ψ k) b u₀) (fun b => G₂ k b u₀)
    (fun b => (hG (ψ k) b u₀ hu huold).1) (fun b => (hG₂ k b u₀ hu hule).1)
    (fun b => (hG (ψ k) b u₀ hu huold).2) (fun b => (hG₂ k b u₀ hu hule).2)
    (ENNReal.ofReal (N (ψ k) ^ (-f L - S * u₀ + τ / 4)))
    (ENNReal.ofReal (N (ψ k) ^ (-f₂ (L - r) - S * u₀ + τ))) htarget
  have hreal : 4 * ((s k).normZ (ω (ψ k)) (ν (ψ k)))⁻¹ * N (ψ k) ^ (-c₀) ≤
      N (ψ k) ^ (-(c₀ / 2)) := by
    calc
      _ ≤ 4 * N (ψ k) ^ (c₀ / 4) * N (ψ k) ^ (-c₀) := by
        gcongr
        exact hkZ
      _ = 4 * N (ψ k) ^ (-3 * c₀ / 4) := by
        rw [mul_assoc, ← Real.rpow_add (show 0 < N (ψ k) by linarith [hN (ψ k)])]
        congr 2
        ring
      _ ≤ _ := hkdecay.le
  calc
    _ ≤ _ := hfinite
    _ ≤ 4 * ENNReal.ofReal (((s k).normZ (ω (ψ k)) (ν (ψ k)))⁻¹) *
        ENNReal.ofReal (N (ψ k) ^ (-c₀)) := by
      gcongr
      exact hkold
    _ = ENNReal.ofReal (4 * ((s k).normZ (ω (ψ k)) (ν (ψ k)))⁻¹ * N (ψ k) ^ (-c₀)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end Submission.Obl.k4_remainder_angular_cap_transport
