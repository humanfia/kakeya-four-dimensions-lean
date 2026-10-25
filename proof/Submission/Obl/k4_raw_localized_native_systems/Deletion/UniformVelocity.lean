import Submission.Obl.k4_raw_localized_native_systems.Deletion.NativeVelocityMass
import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/- Adapted from this LOT tree o105, session x0548, commit
6ab86148e24dd228044f997c2188e8d03c811f1b, AngularPairExceptions.lean and
UniformListedVelocity.lean under Submission/Obl/k4_critical_path_framework/.
Only terminal pure and joint exceptions are needed here. -/

namespace Submission.Obl.k4_raw_localized_native_systems.Deletion

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable section

def angularException (p : Data) (k : ℕ) (γ : Fin (p.W k)) (u τ : ℝ) : ENNReal :=
  selected p k γ {q | p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) q) <
    ENNReal.ofReal (p.N k ^ (-p.f p.L - τ))} +
  selected p k γ {q | ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ)) <
    p.G k γ u (obs (p.B k γ) (δ (p.N k) p.L) q,
      fun j => ⌊v q.1 j / δ (p.N k) u⌋)}

theorem angularException_power_small {p : Data} (hp : Valid p)
    {u τ : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L) (hτ : 0 < τ) :
    IsPowerSmall p.N (fun k => ∑ γ, ENNReal.ofReal (p.ω k γ) * angularException p k γ u τ) := by
  let pure (k : ℕ) := ∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ
    {q | p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) q) <
      ENNReal.ofReal (p.N k ^ (-p.f p.L - τ)) ∨
      ENNReal.ofReal (p.N k ^ (-p.f p.L + τ)) <
        p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) q)}
  let joint (k : ℕ) := ∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ
    {q | ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ)) <
      p.G k γ u (obs (p.B k γ) (δ (p.N k) p.L) q,
        fun j => ⌊v q.1 j / δ (p.N k) u⌋)}
  have hpure : IsPowerSmall p.N pure :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2.1 p.L τ hp.length_pos.le le_rfl hτ
  have hjoint : IsPowerSmall p.N joint :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2 u τ hu huη hτ
  apply (hpure.add hp.scale_tendsto hjoint).mono
  apply Eventually.of_forall
  intro k
  dsimp only [pure, joint]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro γ _
  simp only [angularException, mul_add]
  exact add_le_add (mul_le_mul' le_rfl (measure_mono fun q hq => Or.inl hq)) le_rfl

theorem small_velocity_labels_power_bound {p : Data} (hp : Valid p)
    {k : ℕ} (γ : Fin (p.W k)) {C : ℕ} {u κ τ : ℝ}
    (hu : 0 < u) (huη : u ≤ p.η * p.L) (hκN : κ ≤ p.N k ^ τ)
    (F : Fin C → Set Point) (lst : Observation → Finset (Fin C))
    (hlist : ∀ b, MeasurableSet {o | b ∈ lst o})
    (hcard : ∀ o, ((lst o).card : ℝ) ≤ κ)
    (hknown : ∀ b q, q ∈ F b → b ∈ lst (obs (p.B k γ) (δ (p.N k) p.L) q))
    (hdiam : ∀ b q, q ∈ F b → ∀ q', q' ∈ F b →
      dist (v q.1) (v q'.1) ≤ δ (p.N k) u) :
    selected p k γ (⋃ b, F b) ≤ angularException p k γ u τ +
      ENNReal.ofReal (16 * p.N k ^ (-p.S * u + 3 * τ)) := by
  have hN0 := hp.scale_pos k
  have hscale : ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ)) ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) *
        ENNReal.ofReal (p.N k ^ (-p.f p.L - τ)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hN0]
    have heq : -p.S * u + 2 * τ + (-p.f p.L - τ) = -p.f p.L - p.S * u + τ := by ring
    rw [heq]
  have hraw := small_velocity_labels_bound hp γ hu huη F lst hlist hcard hknown hdiam
    (ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)))
    (ENNReal.ofReal (p.N k ^ (-p.f p.L - τ)))
    (ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ))) hscale
  apply hraw.trans
  apply add_le_add le_rfl
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = 16 * (p.N k ^ (-p.S * u + 2 * τ) * κ) := by ring
    _ ≤ 16 * (p.N k ^ (-p.S * u + 2 * τ) * p.N k ^ τ) := by gcongr
    _ = 16 * p.N k ^ (-p.S * u + 3 * τ) := by
      rw [← Real.rpow_add hN0]
      congr 2
      ring

/-- All labels known from short original terminal lists and having sub-mesh
velocity diameter have power-small original weighted union mass. -/
theorem uniform_small_velocity_labels {p : Data} (hp : Valid p) {u : ℝ}
    (hu : 0 < u) (huη : u ≤ p.η * p.L) :
    ∃ τ c : ℝ, 0 < τ ∧ τ ≤ u / 100 ∧ 0 < c ∧ ∀ᶠ k in atTop,
      ∀ (C : ℕ) (κ : ℝ) (F : Fin (p.W k) → Fin C → Set Point)
        (lst : Fin (p.W k) → Observation → Finset (Fin C)),
        κ ≤ p.N k ^ τ →
        (∀ γ b, MeasurableSet {o | b ∈ lst γ o}) →
        (∀ γ o, ((lst γ o).card : ℝ) ≤ κ) →
        (∀ γ b q, q ∈ F γ b → b ∈ lst γ (obs (p.B k γ) (δ (p.N k) p.L) q)) →
        (∀ γ b q, q ∈ F γ b → ∀ q', q' ∈ F γ b →
          dist (v q.1) (v q'.1) ≤ δ (p.N k) u) →
        (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (⋃ b, F γ b)) ≤
          ENNReal.ofReal (p.N k ^ (-c)) := by
  have hS : 0 < p.S := hp.2.2.2.2.2.2.1
  let τ := min (p.S * u / 100) (u / 100)
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτu : τ ≤ u / 100 := min_le_right _ _
  have hτSu : τ ≤ p.S * u / 100 := min_le_left _ _
  let exponent := -p.S * u + 3 * τ
  have hexp : exponent < 0 := by
    have hSu := mul_pos hS hu
    dsimp only [exponent]
    linarith only [hSu, hτSu]
  have hmask := angularException_power_small hp hu huη hτ
  have hcost : IsPowerSmall p.N (fun k => ENNReal.ofReal (16 * p.N k ^ exponent)) := by
    have hconst := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
      hp.scale_tendsto (show exponent < exponent / 2 by linarith only [hexp]) 16
    refine ⟨-exponent / 2, by linarith only [hexp], ?_⟩
    filter_upwards [hconst] with k hk
    apply ENNReal.ofReal_le_ofReal
    convert hk.le using 1 <;> congr 1 <;> ring
  obtain ⟨c, hc, hbound⟩ := hmask.add hp.scale_tendsto hcost
  refine ⟨τ, c, hτ, hτu, hc, ?_⟩
  filter_upwards [hbound] with k hk
  intro C κ F lst hκN hlist hcard hknown hdiam
  have hweights : (∑ γ, ENNReal.ofReal (p.ω k γ)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => Window.valid_omega_nonneg hp k γ),
      Window.valid_omega_sum hp k]
    simp
  calc
    _ ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) *
        (angularException p k γ u τ + ENNReal.ofReal (16 * p.N k ^ exponent)) := by
      apply Finset.sum_le_sum
      intro γ _
      exact mul_le_mul' le_rfl (small_velocity_labels_power_bound hp γ hu huη hκN
        (F γ) (lst γ) (hlist γ) (hcard γ) (hknown γ) (hdiam γ))
    _ = (∑ γ, ENNReal.ofReal (p.ω k γ) * angularException p k γ u τ) +
        ENNReal.ofReal (16 * p.N k ^ exponent) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hweights, one_mul]
    _ ≤ _ := hk

end
end Submission.Obl.k4_raw_localized_native_systems.Deletion
