/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Native/Blocks.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Keys
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Model

set_option autoImplicit false

/-!
# The prepared true blocks at one index and depth

`BlocksAt cfg k s R` is the frozen preparation premise of a valid model at index `k` and depth
`s`, with `q = 2^-T`, `a = N^-s`, `g = N^-κs` substituted and split into named fields.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The prepared blocks of depth `s` at index `k`. -/
structure BlocksAt (cfg : Data α) (k : ℕ) (s R : ℝ) : Prop where
  T_lo : cfg.N k ^ (cfg.κ * s) / cfg.K k ≤ (2 : ℝ) ^ cfg.T k s
  T_hi : (2 : ℝ) ^ cfg.T k s ≤ cfg.K k * cfg.N k ^ (cfg.κ * s)
  sets : ∀ i, MeasurableSet (cfg.A k s i) ∧ MeasurableSet (cfg.B k s i) ∧
    cfg.B k s i ⊆ cfg.A k s i
  disj : ∀ i i', i ≠ i' → cfg.j k s i = cfg.j k s i' → Disjoint (cfg.A k s i) (cfg.A k s i')
  nu_lo : ∀ i, ENNReal.ofReal ((cfg.N k ^ (-s)) ^ cfg.d * (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2 *
    cfg.N k ^ (-cfg.κ * s) / cfg.K k) ≤ cfg.ν k (cfg.A k s i)
  nu_hi : ∀ i, cfg.ν k (cfg.A k s i) ≤ ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-s)) ^ cfg.d *
    (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2 * cfg.N k ^ (-cfg.κ * s))
  mu_lo : ∀ i, ENNReal.ofReal (((2 : ℝ) ^ cfg.T k s)⁻¹ / cfg.K k) * cfg.ν k (cfg.A k s i) ≤
    cfg.μ k (cfg.B k s i ×ˢ cfg.I (cfg.T k s) (cfg.j k s i))
  c_bd : ∀ i e, |cfg.c k s i e| ≤ cfg.K k
  geom : ∀ i, ∀ l ∈ cfg.A k s i, ∀ t ∈ cfg.I (cfg.T k s) (cfg.j k s i),
    |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| ≤ cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹ ∧
    |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.x k l t) 1| ≤
      cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.N k ^ (-cfg.κ * s) ∧
    |cfg.b k l 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k l 3| ≤ cfg.K k * cfg.N k ^ (-cfg.κ * s)
  fit : ∀ i, ∀ l ∈ cfg.B k s i, cfg.fit k (cfg.K k) (cfg.N k ^ (-s)) (cfg.F k s i) l
    (cfg.I (cfg.T k s) (cfg.j k s i))
  horiz_ae : ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)
  center : ∀ i, |cfg.c k s i 3 + cfg.c k s i 0 +
      ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.c k s i 1| +
    |cfg.c k s i 4 - ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * ((2 : ℝ) ^ cfg.T k s)⁻¹| ≤
      cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹
  affine : ∀ i, ∃ L : Fin 4 → ℝ, HorizontalForm (cfg.F k s i) L ∧
    |L 3| ≤ cfg.K k * (1 + cfg.N k ^ (-s) / (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2) ∧
    ∀ l ∈ cfg.B k s i, ∀ t ∈ cfg.I (cfg.T k s) (cfg.j k s i),
      |L 1 - (cfg.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤
        cfg.K k * (1 + cfg.N k ^ (-s) / ((2 : ℝ) ^ cfg.T k s)⁻¹)
  cover : ∀ᵐ p ∂cfg.μ k, ∃ i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i)
  palette : ∀ (i : Fin (cfg.n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R →
    cfg.μ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i) ∧
      ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹) * cfg.ν k (cfg.A k s i) *
        cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = v₀}

theorem blocksAt_eventually {cfg : Data α} (hv : cfg.Valid) {R : ℝ} (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ cfg.U → BlocksAt cfg k s R := by
  filter_upwards [hv.prepared R hR] with k hk
  intro s hs1 hs2
  have hp := hk s hs1 hs2
  simp only [zpow_neg, zpow_natCast, hv.horizontal_rate] at hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hp
  refine ⟨h1, h2, h3, h4, fun i => (h5 i).1, fun i => (h5 i).2.1, fun i => (h5 i).2.2.1,
    fun i => (h5 i).2.2.2.1, fun i => (h5 i).2.2.2.2.2.1, fun i => (h5 i).2.2.2.2.2.2.1, ?_,
    fun i => ((h5 i).2.2.2.2.2.2.2.2 trivial).2.2.1, fun i => ((h5 i).2.2.2.2.2.2.2.2 trivial).2.2.2,
    h6, h7⟩
  -- the horizontal relation is the same for every block; take it from the coverage
  by_cases hn : ∃ i : Fin (cfg.n k s), True
  · obtain ⟨i, -⟩ := hn
    exact ((h5 i).2.2.2.2.2.2.2.2 trivial).2.1
  · push_neg at hn
    have hzero : cfg.μ k univ = 0 := by
      have := h6
      rw [Filter.eventually_iff, mem_ae_iff] at this
      have hempty : {p : α × ℝ | ∃ i, p.1 ∈ cfg.B k s i ∧
          p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i)}ᶜ = univ := by
        ext p
        simp only [mem_compl_iff, mem_setOf_eq, mem_univ, iff_true, not_exists, not_and]
        intro i
        exact (hn i).elim
      rw [hempty] at this
      exact this
    rw [Measure.measure_univ_eq_zero.mp hzero, ae_zero]
    exact Filter.eventually_bot

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
