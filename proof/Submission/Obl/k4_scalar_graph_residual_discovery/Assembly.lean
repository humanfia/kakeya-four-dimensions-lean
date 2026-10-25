/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file Assembly.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Model

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

theorem timeBlock_subset_unit (T : ℕ) (j : Fin (2 ^ T)) :
    timeBlock T j ⊆ Icc (0 : ℝ) 1 := by
  have hpow : 0 < (2 : ℝ) ^ T := by positivity
  have hj : ((j : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ T := by
    exact_mod_cast j.isLt
  intro t ht
  exact ⟨(by positivity : 0 ≤ ((j : ℕ) : ℝ) / (2 : ℝ) ^ T).trans ht.1,
    ht.2.trans ((div_le_one hpow).mpr hj)⟩

namespace ScalarData

variable {D : ScalarData}

theorem rho_finite (hbase : D.base) (k : ℕ) (g : Fin (D.W k)) : D.ρ k g univ ≠ ⊤ := by
  obtain ⟨hν, hπ, hcoeff, hdom, hsupp⟩ := (hbase k).2.2.1 g
  haveI := hν
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (original_time_support (D.ν k g) (D.ρ k g) hdom hsupp).2

/-- Forgetting surplus graph precision preserves the entire original graph
certificate and every original selected incidence. -/
theorem graphData.mono_precision
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    {L L' B : ℝ} {H : ℕ → ℝ}
    {G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    {E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (h : D.graphData E₀ L' H B G E) (hN : ∀ k, 1 ≤ D.N k) (hLL' : L ≤ L') :
    D.graphData E₀ L H B G E := by
  refine ⟨h.1, by linarith [h.2.1], ?_⟩
  intro R hR
  filter_upwards [h.2.2 R hR] with k hk
  refine ⟨hk.1, fun g => ?_⟩
  obtain ⟨hEm, hEsub, hfit, hlist, hvel⟩ := hk.2 g
  refine ⟨hEm, hEsub, fun p hp => ?_, ?_, hvel⟩
  · refine ⟨(hfit p hp).1, (hfit p hp).2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg hLL'))
      (by linarith [h.1.1 k])
  · intro r hlo hhi hrL q
    exact hlist r hlo hhi (hrL.trans hLL') q

theorem measurable_phys (D : ScalarData) (k : ℕ) (r : ℝ) : Measurable (D.phys k r) := by
  have hZ : Measurable (fun p : ScalarIncidence =>
      (![p.2, scalarY p.1 p.2, scalarX p.1 p.2] : Fin 3 → ℝ)) := by
    apply Measurable.of_eval
    intro e
    fin_cases e <;> simp [scalarY, scalarX] <;> fun_prop
  apply Measurable.of_eval
  intro e
  exact (((measurable_pi_apply e).comp hZ).div_const _).floor

theorem measurable_graph_row (D : ScalarData) (k : ℕ) (B : ℝ)
    (G : Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) (g : Fin (D.W k)) :
    Measurable (fun p => G g (D.phys k B p)) :=
  (measurable_of_countable (G g)).comp (D.measurable_phys k B)

/-- The exact frozen vanishing-ratio conclusion for one fixed graph. -/
theorem fixed_graph_qualification_of_discovery
    {M : ℕ} {B : ℝ}
    {G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    {E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hN : ∀ k, 2 ≤ D.N k) (hbase : D.base)
    (hdiscovery : (D.toQualificationTable B G E).SlackDiscovery M) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto ((D.toQualificationTable B G E).realFailureRatio M ε) atTop (nhds 0) := by
  intro ε hε
  apply QualificationTable.realFailureRatio_tendsto _ M (rho_finite hbase)
  exact QualificationTable.rationalFailureRatio_tendsto _ M hN
    (fun k => by dsimp [toQualificationTable]; positivity)
    (fun k i => timeBlock_subset_unit _ _) hdiscovery hε

/-- Graph selection, surplus precision and the measurable residual reduction
assemble the frozen qualification oracle from geometric discovery. -/
theorem qualOracle_of_polynomialDiscovery
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hN : ∀ k, 2 ≤ D.N k) (hbase : D.base) (hgraph : D.graphOracle E₀)
    (hdiscover : D.polynomialDiscovery E₀) : D.qualOracle E₀ := by
  intro M hM L hL
  obtain ⟨L', hLL', hL', hdiscovery⟩ := hdiscover M hM L hL
  obtain ⟨H, B, G, E, hdata⟩ := hgraph L' hL'
  refine ⟨H, B, G, E,
    hdata.mono_precision (fun k => by linarith [hN k]) hLL', ?_⟩
  exact fixed_graph_qualification_of_discovery hN hbase (hdiscovery H B G E hdata)

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
