import Submission.Obl.k4_scalar_true_atlas_terminal_lists.SaturationBudget
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Monotonicity
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Lists

/-! The geometric crowding cutoff loses only a density exception and a
fourth-order slack divided by its list threshold. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable def chartCrossings (p : Data) (k : ℕ) (r τ : ℝ) (T : ℕ) {n : ℕ}
    (j : Fin n → Fin (2 ^ T)) (u v J : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) : Fin n → Set Observation :=
  fun i => crossing (N p k ^ (-r)) (N p k ^ τ) ((j i : ℕ) / (2 : ℝ) ^ T)
    (1 / (2 : ℝ) ^ T) (u i) (v i) (J i) (P i)

theorem chartCrossings_measurable (p : Data) (k : ℕ) (r τ : ℝ) (T : ℕ) {n : ℕ}
    (j : Fin n → Fin (2 ^ T)) (u v J : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) (i : Fin n) :
    MeasurableSet (chartCrossings p k r τ T j u v J P i) := crossing_measurable _ _ _ _ _ _ _ _

theorem RawChartData.crowding_tail {p : Data} (hp : Exact p)
    {B k T n : ℕ} {r h δ τ R : ℝ}
    {γ : Fin n → Fin (worlds p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Trajectory} {C : Fin n → Set Incidence} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    (hd : RawChartData p B r r h δ true k T n γ j A C u v J P)
    (hδτ : δ ≤ τ) (hr : 0 ≤ r) (hrL : r ≤ L p) (hR : 0 < R) :
    (∑ a, ENNReal.ofReal (weight p k a) * mu p k a
      {q | R < ((labelsAt γ (chartCrossings p k r τ T j u v J P) a
        (observation p k r q)).card : ℝ)}) ≤
    (∑ a, ENNReal.ofReal (weight p k a) * mu p k a
      {q | ENNReal.ofReal (N p k ^ (-profile p r) * N p k ^ τ) <
        density p k a r (observation p k r q)}) +
      ENNReal.ofReal ((2 * (N p k ^ τ) ^ 3 * (2 * N p k ^ τ + 3)) / R) := by
  have hN : 1 ≤ N p k := le_trans (by norm_num) (hp.resolution_ge k)
  have hN0 : 0 < N p k := zero_lt_one.trans_le hN
  let X := chartCrossings p k r τ T j u v J P
  let ω := fun a => ENNReal.ofReal (weight p k a)
  let φ := observation p k r
  let θ := ENNReal.ofReal (N p k ^ (-profile p r) * N p k ^ τ)
  let H := 2 * (N p k ^ τ) ^ 3 * (2 * N p k ^ τ + 3)
  have hX : ∀ i, MeasurableSet (X i) := chartCrossings_measurable p k r τ T j u v J P
  have hg : ∀ a, Measurable (density p k a r) := fun a => (hp.observation_law k a hr hrL).1
  have hlaw : ∀ a, (mu p k a).map φ =
      (volume.prod Measure.count).withDensity (density p k a r) :=
    fun a => (hp.observation_law k a hr hrL).2
  have hcommon := hd.mono hN le_rfl le_rfl hδτ
  have hpacket := hcommon.packet_budget hp
  have hfloor : ∀ i, θ * (volume.prod Measure.count) (X i) ≤
      ENNReal.ofReal H * mu p k (γ i) (C i) := by
    intro i
    rcases hcommon.2.2.2.2.2.1 i with
      ⟨hμ, hJ, hJinv, hJup, hctr, hdeg, hcoef, hA, hAf, hCf, hfit, htrue⟩
    apply crossing_density_budget _ _ _ _ _ _ _ _ _ (Real.rpow_pos_of_pos hN0 _).le
      (Real.rpow_pos_of_pos hN0 _) (by positivity) hJ.le
    convert htrue rfl using 1
    congr 1
    field_simp
  have hcap₀ := capped_crossing_tail_of_budget γ X hX ω (mu p k) (volume.prod Measure.count)
    φ (observation_measurable p k r) (fun a => density p k a r) hg hlaw C
    (ENNReal.ofReal R) θ (ENNReal.ofReal H) hpacket hfloor
  have hcountiff (a : Fin (worlds p k)) (q : Incidence) :
      ENNReal.ofReal R < ((labelsAt γ X a (φ q)).card : ENNReal) ↔
        R < ((labelsAt γ X a (φ q)).card : ℝ) := by
    have hle : ((labelsAt γ X a (φ q)).card : ENNReal) ≤ ENNReal.ofReal R ↔
        ((labelsAt γ X a (φ q)).card : ℝ) ≤ R := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal_iff hR.le
    simpa only [not_le] using not_congr hle
  have hcap : (∑ a, ω a * mu p k a {q |
      R < ((labelsAt γ X a (φ q)).card : ℝ) ∧ density p k a r (φ q) ≤ θ}) ≤
        ENNReal.ofReal (H / R) := by
    rw [ENNReal.ofReal_div_of_pos hR]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.mpr hR).ne') (Or.inl ENNReal.ofReal_ne_top)).mpr
    simpa only [hcountiff, mul_comm] using hcap₀
  have hsplit (a : Fin (worlds p k)) :
      mu p k a {q | R < ((labelsAt γ X a (φ q)).card : ℝ)} ≤
        mu p k a {q | θ < density p k a r (φ q)} +
          mu p k a {q | R < ((labelsAt γ X a (φ q)).card : ℝ) ∧ density p k a r (φ q) ≤ θ} := by
    apply le_trans (measure_mono ?_) (measure_union_le _ _)
    intro q hq
    by_cases hθ : θ < density p k a r (φ q)
    · exact Or.inl hθ
    · exact Or.inr ⟨hq, le_of_not_gt hθ⟩
  calc
    _ ≤ ∑ a, ω a * (mu p k a {q | θ < density p k a r (φ q)} +
        mu p k a {q | R < ((labelsAt γ X a (φ q)).card : ℝ) ∧ density p k a r (φ q) ≤ θ}) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hsplit a) zero_le
    _ = (∑ a, ω a * mu p k a {q | θ < density p k a r (φ q)}) +
        ∑ a, ω a * mu p k a {q | R < ((labelsAt γ X a (φ q)).card : ℝ) ∧ density p k a r (φ q) ≤ θ} := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add le_rfl hcap

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
