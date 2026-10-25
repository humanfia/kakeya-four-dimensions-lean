/-
Adapted from this LOT tree, obligation o134, session x0438, commit 2e990309978b,
Submission/Obl/k4_scalar_guarded_tangent_obstruction/PowerFullness.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.Fullness
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.ExactLaw

namespace Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry

open MeasureTheory Set

set_option maxHeartbeats 800000

/-- The original exact density windows control a narrow-chart restriction.
Both exceptional terms are charged to the original incidence law. -/
theorem ChartData.narrow_mass_le_power_windows
    {p : RawData} (hp : Exact p) {B k T n : ℕ} {r h ε : ℝ} {isTrue : Bool}
    {γ : Fin n → Fin (p.1 k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Coeff} {C : Fin n → Set Incidence}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (p.1 k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hc : ChartData p B r p.L h ε isTrue k T n γ j A C u v J P Λ)
    (g : Fin (p.1 k)) (ρ : Measure Incidence) (hρ : ρ ≤ mu p k g)
    {a : ℝ} (ha : 0 < a) (haU : a ≤ p.U) (τ : ℝ)
    (hcover : ∀ᵐ z ∂ρ, ∃ i, γ i = g ∧ z ∈ C i ∧
      2 * p.N k ^ ε * J i * (2 : ℝ) ^ T ≤ p.N k ^ (-a)) :
    ρ Set.univ ≤
      (3 * ENNReal.ofReal (p.N k ^ (-p.S * a + 2 * τ)) *
        ENNReal.ofReal (p.N k ^ ε)) * mu p k g Set.univ +
      mu p k g {z | p.density k g p.L
          ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / p.N k ^ (-p.L)⌋ : ℤ)) <
            ENNReal.ofReal (p.N k ^ (-p.profile p.L - τ)) ∨
        ENNReal.ofReal (p.N k ^ (-p.profile p.L - p.S * a + τ)) <
          p.angularDensity k g a
            (((![z.2, y z.1 z.2] : Fin 2 → ℝ),
              (⌊x z.1 z.2 / p.N k ^ (-p.L)⌋ : ℤ)),
                (⌊z.1.2 1 / p.N k ^ (-a)⌋ : ℤ))} := by
  let : IsFiniteMeasure (mu p k g) := hp.selected_finite k g
  have hN : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hp.1.1 k)
  have hδ : 0 < p.N k ^ (-a) := Real.rpow_pos_of_pos hN _
  let observe := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (p.N k ^ (-p.L))
  let bin : Incidence → ℤ := fun z => ⌊z.1.2 1 / p.N k ^ (-a)⌋
  have hobs : Measurable observe :=
    Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsL _
  have hbin : Measurable bin := by dsimp [bin]; fun_prop
  have hL : 0 ≤ p.L := le_of_lt hp.1.2.2.2.2.2.1
  obtain ⟨hf, hpure⟩ := hp.pure_density k g hL le_rfl
  obtain ⟨hF, hjoint⟩ := hp.joint_density k g ha haU
  let G : Set ((((Fin 2 → ℝ) × ℤ) × ℤ)) := {z |
    ENNReal.ofReal (p.N k ^ (-p.profile p.L - τ)) ≤ p.density k g p.L z.1 ∧
    p.angularDensity k g a z ≤ ENNReal.ofReal (p.N k ^ (-p.profile p.L - p.S * a + τ))}
  have hG : MeasurableSet G :=
    (measurableSet_le measurable_const (hf.comp measurable_fst)).inter
      (measurableSet_le hF measurable_const)
  have hcap : ∀ z ∈ G, p.angularDensity k g a z ≤
      ENNReal.ofReal (p.N k ^ (-p.S * a + 2 * τ)) * p.density k g p.L z.1 := by
    intro z hz
    simpa only [neg_mul] using angular_ratio_of_power_window
      (N := p.N k) (a := p.profile p.L) (σ := p.S * a) (τ := τ) hN hz.1 hz.2
  have hlist : ∀ᵐ z ∂ρ, bin z ∈ velocityList (Λ g) v (p.N k ^ (-a)) (observe z) :=
    ChartData.velocity_list_ae hc g ρ hρ hδ hcover
  have hcard (z : (Fin 2 → ℝ) × ℤ) :
      ((velocityList (Λ g) v (p.N k ^ (-a)) z).card : ENNReal) ≤
        3 * ENNReal.ofReal (p.N k ^ ε) := by
    calc
      _ ≤ ((3 * (Λ g z).card : ℕ) : ENNReal) := by
        exact_mod_cast card_velocityList_le (Λ g) v (p.N k ^ (-a)) z
      _ = 3 * ENNReal.ofReal ((Λ g z).card : ℝ) := by simp
      _ ≤ 3 * ENNReal.ofReal (p.N k ^ ε) := by
        gcongr
        exact hc.2.2.2.2.2.2.1 g z
  have hbound := original_mass_le_angular_list_budget_with_bad
    (mu p k g) ρ hρ (volume.prod Measure.count) observe bin hobs hbin
    (p.density k g p.L) (p.angularDensity k g a) hf hpure hjoint G hG
    (ENNReal.ofReal (p.N k ^ (-p.S * a + 2 * τ)))
    (3 * ENNReal.ofReal (p.N k ^ ε)) hcap (velocityList (Λ g) v (p.N k ^ (-a)))
    (measurable_velocityList (Λ g) v _ (hc.2.2.2.2.2.2.2.1 g)) hcard hlist
  have hevent : ((fun z => (observe z, bin z)) ⁻¹' G)ᶜ =
      {z | p.density k g p.L
          ((![z.2, y z.1 z.2] : Fin 2 → ℝ), (⌊x z.1 z.2 / p.N k ^ (-p.L)⌋ : ℤ)) <
            ENNReal.ofReal (p.N k ^ (-p.profile p.L - τ)) ∨
        ENNReal.ofReal (p.N k ^ (-p.profile p.L - p.S * a + τ)) <
          p.angularDensity k g a
            (((![z.2, y z.1 z.2] : Fin 2 → ℝ),
              (⌊x z.1 z.2 / p.N k ^ (-p.L)⌋ : ℤ)),
                (⌊z.1.2 1 / p.N k ^ (-a)⌋ : ℤ))} := by
    ext z
    simp only [mem_compl_iff, mem_preimage, G, mem_ofPred_eq, not_and_or, not_le]
    rfl
  rw [hevent] at hbound
  convert hbound using 1
  ring

/-- Fullness summed with the immutable original mixture weights. -/
theorem ChartData.weighted_narrow_mass_le_power_windows
    {p : RawData} (hp : Exact p) {B k T n : ℕ} {r h ε : ℝ} {isTrue : Bool}
    {γ : Fin n → Fin (p.1 k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Coeff} {C : Fin n → Set Incidence}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (p.1 k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hc : ChartData p B r p.L h ε isTrue k T n γ j A C u v J P Λ)
    (ρ : Fin (p.1 k) → Measure Incidence) (hρ : ∀ g, ρ g ≤ mu p k g)
    {a : ℝ} (ha : 0 < a) (haU : a ≤ p.U) (τ : ℝ)
    (hcover : ∀ g, ∀ᵐ z ∂ρ g, ∃ i, γ i = g ∧ z ∈ C i ∧
      2 * p.N k ^ ε * J i * (2 : ℝ) ^ T ≤ p.N k ^ (-a)) :
    (∑ g, ENNReal.ofReal (p.weight k g) * ρ g Set.univ) ≤
      (3 * ENNReal.ofReal (p.N k ^ (-p.S * a + 2 * τ)) *
        ENNReal.ofReal (p.N k ^ ε)) *
          (∑ g, ENNReal.ofReal (p.weight k g) * mu p k g Set.univ) +
      ∑ g, ENNReal.ofReal (p.weight k g) * mu p k g (originalDensityException p k g a τ) := by
  let c := 3 * ENNReal.ofReal (p.N k ^ (-p.S * a + 2 * τ)) *
    ENNReal.ofReal (p.N k ^ ε)
  have hlocal (g : Fin (p.1 k)) : ρ g Set.univ ≤ c * mu p k g Set.univ +
      mu p k g (originalDensityException p k g a τ) :=
    ChartData.narrow_mass_le_power_windows hp hc g (ρ g) (hρ g) ha haU τ (hcover g)
  calc
    _ ≤ ∑ g, ENNReal.ofReal (p.weight k g) *
        (c * mu p k g Set.univ + mu p k g (originalDensityException p k g a τ)) := by
      apply Finset.sum_le_sum
      intro g _
      gcongr
      exact hlocal g
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      dsimp [c]
      ring

end Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry
