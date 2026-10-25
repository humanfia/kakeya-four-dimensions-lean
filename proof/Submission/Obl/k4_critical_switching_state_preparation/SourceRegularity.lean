/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/SourceRegularity.lean.
   Existing source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.SourcePairs
import Submission.Obl.k4_critical_switching_state_preparation.IncidenceNesting

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Filter Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

def primitiveEvent (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) (E : ℝ) : Set (α × ℝ) :=
  {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
    |affineResidualSlope L (cfg.b k p.1)| ≤ E}

theorem measurableSet_primitiveEvent {cfg : Data α} (h : cfg.Valid)
    (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (E : ℝ)
    (hB : MeasurableSet (cfg.B k s i)) : MeasurableSet (cfg.primitiveEvent k s i L E) := by
  have heq : cfg.primitiveEvent k s i L E =
      (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) ∩
        {p : α × ℝ | |affineResidualSlope L (cfg.b k p.1)| ≤ E} := by
    ext p
    simp only [primitiveEvent, mem_setOf_eq, mem_inter_iff, mem_prod, and_assoc]
  rw [heq]
  refine (hB.prod measurableSet_Icc).inter ?_
  exact measurableSet_le
    ((measurable_affineResidualSlope (cfg.b k) (h.basic k).1 L).comp measurable_fst).abs
    measurable_const

/-- At a fixed positive depth the frozen atlas also supplies measurability
of every fitted subset, on the same original source space. -/
theorem Valid.eventually_fitted_measurable {cfg : Data α} (h : cfg.Valid)
    {s : ℝ} (hs : 0 < s) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, ∀ i : Fin (cfg.n k s), MeasurableSet (cfg.B k s i) := by
  let R := 2 + s⁻¹
  have hR : 1 < R := by
    have hh : 0 < s⁻¹ := inv_pos.mpr hs
    dsimp [R]
    linarith
  have hRs : R⁻¹ ≤ s := by
    have hRpos : 0 < R := by linarith
    have hle : s⁻¹ ≤ R := by dsimp [R]; linarith
    exact (inv_le_comm₀ hRpos hs).mpr hle
  filter_upwards [h.atlas R hR] with k hk i
  exact ((hk s hRs hsU).2.2.1 i).2.1

/-- Fixed depths can be prepared together before any source restriction. -/
theorem Valid.eventually_nesting {cfg : Data α} (h : cfg.Valid)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (htU : t ≤ cfg.U) :
    ∀ᶠ k in atTop, ∀ i : Fin (cfg.n k t), ∃ ip : Fin (cfg.n k s),
      cfg.A k t i ⊆ cfg.A k s ip ∧
      I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip) := by
  let R := 2 + s⁻¹
  have hR : 1 < R := by
    have hh : 0 < s⁻¹ := inv_pos.mpr hs
    dsimp [R]
    linarith
  have hRs : R⁻¹ ≤ s := by
    have hRpos : 0 < R := by linarith
    have hle : s⁻¹ ≤ R := by dsimp [R]; linarith
    exact (inv_le_comm₀ hRpos hs).mpr hle
  filter_upwards [h.nested R hR] with k hk
  exact hk s t hRs hst htU

/-- All required original laws and true descendants may be imposed
pointwise on a measurable subset of the primitive event with EXACTLY its
original residual mass. No true assignment or reference prior is restricted. -/
theorem AssignmentLevel.exists_regular_primitive_source {cfg : Data α}
    (h : cfg.Valid) {k : ℕ} {s : ℝ} (parent : cfg.AssignmentLevel k s)
    (ip : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (E : ℝ)
    (hB : MeasurableSet (cfg.B k s ip)) (depths : Finset ℝ)
    (hlevels : ∀ t ∈ depths, cfg.AssignmentLevel k t)
    (hnest : ∀ t ∈ depths, ∀ i : Fin (cfg.n k t), ∃ ip' : Fin (cfg.n k s),
      cfg.A k t i ⊆ cfg.A k s ip' ∧
      I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip')) :
    ∃ source : Set (α × ℝ), MeasurableSet source ∧
      source ⊆ cfg.primitiveEvent k s ip L E ∧
      cfg.ρ k source = cfg.ρ k (cfg.primitiveEvent k s ip L E) ∧
      (∀ p ∈ source, (∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * cfg.K k) ∧
        |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) ∧
        ∀ t ∈ depths, ∃ i : Fin (cfg.n k t),
          p.1 ∈ cfg.B k t i ∧ p.2 ∈ I (cfg.T k t) (cfg.j k t i) ∧
          cfg.A k t i ⊆ cfg.A k s ip ∧
          I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip)) := by
  classical
  have hcoeff : ∀ᵐ p ∂cfg.μ k, ∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * cfg.K k := by
    filter_upwards [h.ae_base_coefficients k, parent.native_hidden_bounds h ip] with p hp hh e
    have hK := h.subpower.1 k
    fin_cases e <;> simp only [Fin.reduceFinMk] <;>
      linarith [abs_nonneg (cfg.b k p.1 0), abs_nonneg (cfg.b k p.1 1),
        abs_nonneg (cfg.b k p.1 3), abs_nonneg (cfg.b k p.1 4)]
  have hdesc (t : ℝ) (ht : t ∈ depths) : ∀ᵐ p ∂cfg.μ k,
      p ∈ cfg.primitiveEvent k s ip L E → ∃ i : Fin (cfg.n k t),
        p.1 ∈ cfg.B k t i ∧ p.2 ∈ I (cfg.T k t) (cfg.j k t i) ∧
        cfg.A k t i ⊆ cfg.A k s ip ∧
        I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip) := by
    filter_upwards [(hlevels t ht).covers, parent.ae_matching_ancestor h (hnest t ht)]
      with p hp hanc hpE
    obtain ⟨i, hi, hit⟩ := hp
    have hanc' := hanc ip i ⟨parent.fitted_subset ip hpE.1, hpE.2.1⟩
      ⟨(hlevels t ht).fitted_subset i hi, hit⟩
    exact ⟨i, hi, hit, hanc'⟩
  have hdesc_all : ∀ᵐ p ∂cfg.μ k, ∀ t ∈ depths,
      p ∈ cfg.primitiveEvent k s ip L E → ∃ i : Fin (cfg.n k t),
        p.1 ∈ cfg.B k t i ∧ p.2 ∈ I (cfg.T k t) (cfg.j k t i) ∧
        cfg.A k t i ⊆ cfg.A k s ip ∧
        I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip) := by
    exact (Filter.eventually_all_finset depths).mpr hdesc
  have hgood : ∀ᵐ p ∂cfg.ρ k, (∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * cfg.K k) ∧
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) ∧
      ∀ t ∈ depths, p ∈ cfg.primitiveEvent k s ip L E → ∃ i : Fin (cfg.n k t),
        p.1 ∈ cfg.B k t i ∧ p.2 ∈ I (cfg.T k t) (cfg.j k t i) ∧
        cfg.A k t i ⊆ cfg.A k s ip ∧
        I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip) := by
    apply ae_mono (h.basic k).2.2.2.2.1
    filter_upwards [hcoeff, parent.horizontal_equation ip, hdesc_all] with p hp hh hd
    exact ⟨hp, hh, hd⟩
  obtain ⟨G, hGae, hG, hGsub⟩ := hgood.exists_measurable_mem
  refine ⟨cfg.primitiveEvent k s ip L E ∩ G,
    (measurableSet_primitiveEvent h k s ip L E hB).inter hG, inter_subset_left, ?_, ?_⟩
  · apply measure_congr
    filter_upwards [hGae] with p hp
    simp only [mem_inter_iff, hp, and_true]
  · intro p hp
    have hg := hGsub p hp.2
    exact ⟨hg.1, hg.2.1, fun t ht => hg.2.2 t ht hp.1⟩

/-- Bounded original trajectory coefficients and primitive slopes bound
its exact midpoint value by a fixed polynomial in the same bounds. -/
theorem midpointValue_bound {cfg : Data α} (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) (K M : ℝ) (hK : 1 ≤ K) (hM : 1 ≤ M) (hL₀ : L 0 = 0)
    (hL : ∀ e : Fin 3, |L e.succ| ≤ M) (p : α × ℝ)
    (hb : ∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * K) :
    |cfg.midpointValue k s i L p| ≤ 16 * K * M := by
  have ht := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) (cfg.midpoint_mem_I k s i)
  have htm : |cfg.midpoint k s i| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have hK0 : 0 ≤ K := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hmul (e : Fin 3) (j : Fin 6) : |L e.succ * cfg.b k p.1 j| ≤ 2 * K * M := by
    rw [abs_mul]
    exact (mul_le_mul (hL e) (hb j) (abs_nonneg _) hM0).trans_eq (by ring)
  have hconst : |affineResidualIntercept L (cfg.b k p.1)| ≤ 2 * K + 4 * K * M := by
    simp only [affineResidualIntercept, hL₀, sub_zero]
    exact (abs_sub _ _).trans
      ((add_le_add ((abs_sub _ _).trans (add_le_add (hb 2) (hmul 1 0)))
        (hmul 2 1)).trans_eq (by ring))
  have hslope : |affineResidualSlope L (cfg.b k p.1)| ≤ 2 * K + M + 4 * K * M := by
    unfold affineResidualSlope
    exact (abs_sub _ _).trans
      ((add_le_add ((abs_sub _ _).trans
        (add_le_add ((abs_sub _ _).trans (add_le_add (hb 5) (hL 0))) (hmul 1 3)))
        (hmul 2 4)).trans_eq (by ring))
  calc
    _ ≤ |affineResidualIntercept L (cfg.b k p.1)| +
        |cfg.midpoint k s i * affineResidualSlope L (cfg.b k p.1)| := abs_add_le _ _
    _ ≤ (2 * K + 4 * K * M) + (2 * K + M + 4 * K * M) := by
      apply add_le_add hconst
      rw [abs_mul]
      exact (mul_le_mul htm hslope (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ ≤ _ := by nlinarith

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
