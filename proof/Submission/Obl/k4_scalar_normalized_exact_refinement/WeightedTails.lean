import Submission.Obl.k4_scalar_normalized_exact_refinement.Weighted
import Submission.Obl.k4_scalar_grid_density_extension.GridRelation

/-!
# Weighted density tails of a Refinement

All estimates hold at every index `k` of `q`, against the original family at index `φ k`.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

open MeasureTheory Set Filter
open scoped ENNReal

variable {p q : Code} {r b h : ℝ}

namespace RefData

variable (R : RefData p q r b h)

/-- Per-label bounds through the normalization give a weighted bound over `Z`. -/
lemma weighted_transfer (hp : Spec.RawScalar p) (k : ℕ) (S : Fin (q.1 k) → Set Inc)
    (F : Fin (q.1 k) → ℝ≥0∞) (hS : ∀ i, q.mu k i (S i) ≤ R.c k i * F i) :
    ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (S i) ≤
      ENNReal.ofReal (R.Z k)⁻¹ * ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) * F i := by
  calc ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (S i)
      ≤ ∑ i, ENNReal.ofReal (q.ω k i) * (R.c k i * F i) := by gcongr with i; exact hS i
    _ = ∑ i, ENNReal.ofReal (R.Z k)⁻¹ * (ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) * F i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_assoc, R.weight_mul_c hp k i]
        ring
    _ = _ := by rw [Finset.mul_sum]

/-- Upper tails of the pure densities of `q` at depth `s`. -/
theorem weighted_upper (hp : Spec.Exact p) (hq : Spec.PureProfile q) (hLq : q.L = p.L - r)
    (hr : 0 ≤ r) (k : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsL : s ≤ q.L) (θ' : ℝ≥0∞) :
    ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i
        {z | ENNReal.ofReal (R.lam k i) * (4 * θ') < q.ρ k i s (obs (q.N k) s z)} ≤
      ENNReal.ofReal (R.Z k)⁻¹ * (8 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) *
        p.mu (R.φ k) a {z | θ' < p.ρ (R.φ k) a (r + s) (obs (p.N (R.φ k)) (r + s) z)}) := by
  have hraw := Exact.raw hp
  have hN : 0 < p.N (R.φ k) := by linarith [RawScalar.N_ge hraw (R.φ k)]
  set X : Fin (p.1 (R.φ k)) → Set Inc :=
    fun a => {z | θ' < p.ρ (R.φ k) a (r + s) (obs (p.N (R.φ k)) (r + s) z)} with hXdef
  have hX : ∀ a, MeasurableSet (X a) := fun a =>
    measurableSet_lt measurable_const
      (((PureProfile.law (Exact.pure hp) (R.φ k) a (r + s) (by linarith) (by linarith)).1).comp
        (measurable_obs _ _))
  refine (R.weighted_transfer hraw k _
    (fun i => 4 * p.mu (R.φ k) (R.γ k i) (R.C k i ∩ X (R.γ k i))) ?_).trans ?_
  · intro i
    have := mu_isFinite hraw (R.φ k) (R.γ k i)
    have hlawq := PureProfile.law hq k i s hs0 hsL
    rw [R.qN_eq k] at hlawq
    have hlawp := PureProfile.law (Exact.pure hp) (R.φ k) (R.γ k i) (r + s) (by linarith)
      (by linarith)
    have hw := world_upper_tail hN (R.dt_pos k) (R.J_pos k i) (R.θ_meas k i) (R.θ_y' k i)
      (R.θ_x' k i) (R.c_ne_zero hraw k i) (R.c_ne_top k i) (R.mu_eq' k i) s hlawq.1 hlawq.2
      hlawp.1 hlawp.2 θ'
    rw [R.c_mul_dtJ hraw k i] at hw
    rw [R.qN_eq k]
    exact hw
  · rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num]
    gcongr
    calc ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) *
          (4 * p.mu (R.φ k) (R.γ k i) (R.C k i ∩ X (R.γ k i)))
        = 4 * ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) *
          p.mu (R.φ k) (R.γ k i) (R.C k i ∩ X (R.γ k i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ ≤ 4 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * (2 * p.mu (R.φ k) a (X a)) := by
          gcongr
          apply sum_by_world (R.γ k) (fun a => ENNReal.ofReal (p.ω (R.φ k) a))
            (fun i => p.mu (R.φ k) (R.γ k i) (R.C k i ∩ X (R.γ k i)))
          intro a
          calc ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a),
                p.mu (R.φ k) (R.γ k i) (R.C k i ∩ X (R.γ k i))
              = ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a),
                p.mu (R.φ k) a (R.C k i ∩ X a) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [(Finset.mem_filter.mp hi).2]
            _ ≤ 2 * p.mu (R.φ k) a (X a) := ChartData.sum_mu_le_two (R.chart k) a (hX a)
      _ = 4 * 2 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * p.mu (R.φ k) a (X a) := by
          rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          congr 1
          funext a
          ring

/-- Upper tails of joint densities of `q` at the terminal depth. -/
theorem weighted_angular (hp : Spec.Exact p) (hLq : q.L = p.L - r) (k : ℕ) (uq up : ℝ)
    (hup : 0 < up) (hupU : up ≤ p.U)
    (hα : ∀ i, R.J k i / R.dt k * p.N (R.φ k) ^ (-uq) ≤ p.N (R.φ k) ^ (-up))
    (gA : Fin (q.1 k) → Joint → ℝ≥0∞) (hgA : ∀ i, Measurable (gA i))
    (hgAlaw : ∀ i, (q.mu k i).map (aug (q.N k) q.L uq) = JointRef.withDensity (gA i))
    (θ' : ℝ≥0∞) :
    ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i
        {z | ENNReal.ofReal (R.lam k i) * (8 * θ') < gA i (aug (q.N k) q.L uq z)} ≤
      ENNReal.ofReal (R.Z k)⁻¹ * (16 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) *
        p.mu (R.φ k) a {z | θ' < p.ρA (R.φ k) a up (aug (p.N (R.φ k)) p.L up z)}) := by
  have hraw := Exact.raw hp
  have hN : 0 < p.N (R.φ k) := by linarith [RawScalar.N_ge hraw (R.φ k)]
  have hrs : r + q.L = p.L := by linarith
  set X : Fin (p.1 (R.φ k)) → Set Inc :=
    fun a => {z | θ' < p.ρA (R.φ k) a up (aug (p.N (R.φ k)) p.L up z)} with hXdef
  have hX : ∀ a, MeasurableSet (X a) := fun a =>
    measurableSet_lt measurable_const
      (((Exact.joint hp (R.φ k) a up hup hupU).1).comp (measurable_aug _ _ _))
  refine (R.weighted_transfer hraw k _
    (fun i => 8 * p.mu (R.φ k) (R.γ k i) (R.C k i ∩ X (R.γ k i))) ?_).trans ?_
  · intro i
    have := mu_isFinite hraw (R.φ k) (R.γ k i)
    have hlawq := hgAlaw i
    rw [R.qN_eq k] at hlawq
    have hlawp := Exact.joint hp (R.φ k) (R.γ k i) up hup hupU
    rw [← hrs] at hlawp
    have hw := world_angular_tail hN (R.dt_pos k) (R.J_pos k i) (R.θ_meas k i) (R.θ_y' k i)
      (R.θ_x' k i) (R.c_ne_zero hraw k i) (R.c_ne_top k i) (R.mu_eq' k i) q.L uq up (hα i)
      (hgA i) hlawq hlawp.1 hlawp.2 θ'
    rw [R.c_mul_dtJ hraw k i, hrs] at hw
    rw [R.qN_eq k]
    exact hw
  · rw [show (16 : ℝ≥0∞) = 8 * 2 by norm_num]
    gcongr
    calc ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) *
          (8 * p.mu (R.φ k) (R.γ k i) (R.C k i ∩ X (R.γ k i)))
        = 8 * ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) *
          p.mu (R.φ k) (R.γ k i) (R.C k i ∩ X (R.γ k i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ ≤ 8 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * (2 * p.mu (R.φ k) a (X a)) := by
          gcongr
          apply sum_by_world (R.γ k) (fun a => ENNReal.ofReal (p.ω (R.φ k) a))
            (fun i => p.mu (R.φ k) (R.γ k i) (R.C k i ∩ X (R.γ k i)))
          intro a
          calc ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a),
                p.mu (R.φ k) (R.γ k i) (R.C k i ∩ X (R.γ k i))
              = ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a),
                p.mu (R.φ k) a (R.C k i ∩ X a) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [(Finset.mem_filter.mp hi).2]
            _ ≤ 2 * p.mu (R.φ k) a (X a) := ChartData.sum_mu_le_two (R.chart k) a (hX a)
      _ = 8 * 2 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * p.mu (R.φ k) a (X a) := by
          rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          congr 1
          funext a
          ring

/-- Weighted world masses are at most one. -/
lemma weighted_mass_le_one (hp : Spec.RawScalar p) (k : ℕ) :
    ∑ a, ENNReal.ofReal (p.ω k a) * p.mu k a univ ≤ 1 := by
  calc ∑ a, ENNReal.ofReal (p.ω k a) * p.mu k a univ ≤ ∑ a, ENNReal.ofReal (p.ω k a) * 1 := by
        gcongr with a
        exact mu_univ_le_one hp k a
    _ = 1 := by
        simp only [mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => RawScalar.ω_nonneg hp k a),
          RawScalar.ω_sum hp k, ENNReal.ofReal_one]

/-- The label lists of a chart system at a depth `σ ≥ b` bound the restriction loss. -/
theorem world_label_lower (hp : Spec.Exact p) (k : ℕ) (a : Fin (p.1 (R.φ k))) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσL : σ ≤ p.L) (hbσ : b ≤ σ) (D' : Fin (q.1 k) → Base → ℝ≥0∞)
    (hD' : ∀ i, Measurable (D' i))
    (hD'law : ∀ i, ((p.mu (R.φ k) (R.γ k i)).restrict (R.C k i)).map (obs (p.N (R.φ k)) σ) =
      BaseRef.withDensity (D' i)) (δ : ℝ≥0∞) :
    ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a), p.mu (R.φ k) a (R.C k i ∩
        {z | D' i (obs (p.N (R.φ k)) σ z) < δ * p.ρ (R.φ k) a σ (obs (p.N (R.φ k)) σ z)}) ≤
      2 * ENNReal.ofReal (p.N (R.φ k) ^ R.ε k) * δ * p.mu (R.φ k) a univ := by
  classical
  have hraw := Exact.raw hp
  have hN1 : 1 ≤ p.N (R.φ k) := by linarith [RawScalar.N_ge hraw (R.φ k)]
  have hN : 0 < p.N (R.φ k) := by linarith
  set N := p.N (R.φ k) with hNdef
  set w := N ^ (-σ) with hwdef
  set wb := N ^ (-b) with hwbdef
  have hw : 0 < w := Real.rpow_pos_of_pos hN _
  have hwwb : w ≤ wb := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hchart := R.chart k
  set Γ := {i : Fin (q.1 k) // R.γ k i = a}
  let coarse : Base → Base := fun o => (o.1, ⌊(o.2 : ℝ) * w / wb⌋)
  let coarse' : Base → Base := fun o => (o.1, ⌊(o.2 : ℝ) * w / wb⌋ + 1)
  have hcm : Measurable coarse :=
    measurable_fst.prodMk ((measurable_of_countable (fun m : ℤ => ⌊(m : ℝ) * w / wb⌋)).comp
      measurable_snd)
  have hcm' : Measurable coarse' :=
    measurable_fst.prodMk ((measurable_of_countable (fun m : ℤ => ⌊(m : ℝ) * w / wb⌋ + 1)).comp
      measurable_snd)
  let Cs : Γ → Set Base := fun i =>
    {o | i.1 ∈ R.Λ k a (coarse o)} ∪ {o | i.1 ∈ R.Λ k a (coarse' o)}
  have hCs : ∀ i, MeasurableSet (Cs i) := fun i =>
    (hcm (ChartData.Λmeas hchart a i.1)).union (hcm' (ChartData.Λmeas hchart a i.1))
  have hlawG := PureProfile.law (Exact.pure hp) (R.φ k) a σ hσ0 hσL
  have hlawγ : ∀ i : Γ, ((p.mu (R.φ k) a).restrict (R.C k i.1)).map (obs N σ) =
      BaseRef.withDensity (D' i.1) := by
    intro i
    have := hD'law i.1
    rw [i.2] at this
    exact this
  have hsupp : ∀ i : Γ, ∀ᵐ z ∂((p.mu (R.φ k) a).restrict (R.C k i.1)), obs N σ z ∈ Cs i := by
    intro i
    have hnull := ChartData.Λae hchart i.1
    rw [i.2] at hnull
    have hae : ∀ᵐ z ∂((p.mu (R.φ k) a).restrict (R.C k i.1)), i.1 ∈ R.Λ k a (obs N b z) := by
      rw [ae_iff, Measure.restrict_apply' (ChartData.measC hchart i.1)]
      refine measure_mono_null ?_ hnull
      rintro z ⟨hz, hzC⟩
      exact ⟨hzC, hz⟩
    filter_upwards [hae] with z hz
    have hcompat : k4_scalar_grid_density_extension.FloorCompatible wb w
        (obs N b z).2 (obs N σ z).2 := ⟨Spec.x z.1 z.2, rfl, rfl⟩
    have hmem := k4_scalar_grid_density_extension.floorCompatible_coarse_mem hw hwwb
      (obs N σ z).2 _ hcompat
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · left
      change i.1 ∈ R.Λ k a ((obs N σ z).1, ⌊((obs N σ z).2 : ℝ) * w / wb⌋)
      have : obs N b z = ((obs N σ z).1, ⌊((obs N σ z).2 : ℝ) * w / wb⌋) := Prod.ext rfl h1
      rw [← this]
      exact hz
    · right
      change i.1 ∈ R.Λ k a ((obs N σ z).1, ⌊((obs N σ z).2 : ℝ) * w / wb⌋ + 1)
      have : obs N b z = ((obs N σ z).1, ⌊((obs N σ z).2 : ℝ) * w / wb⌋ + 1) := Prod.ext rfl h1
      rw [← this]
      exact hz
  have hK : ∀ o, ∑ i : Γ, (Cs i).indicator (fun _ => (1 : ℝ≥0∞)) o ≤
      2 * ENNReal.ofReal (N ^ R.ε k) := by
    intro o
    set U := R.Λ k a (coarse o) ∪ R.Λ k a (coarse' o)
    calc ∑ i : Γ, (Cs i).indicator (fun _ => (1 : ℝ≥0∞)) o
        ≤ ∑ i : Γ, (if i.1 ∈ U then (1 : ℝ≥0∞) else 0) := by
          gcongr with i
          by_cases hi : o ∈ Cs i
          · rw [indicator_of_mem hi]
            have : i.1 ∈ U := by
              rcases hi with hi | hi
              · exact Finset.mem_union_left _ hi
              · exact Finset.mem_union_right _ hi
            simp [this]
          · rw [indicator_of_notMem hi]
            exact zero_le
      _ ≤ ∑ i : Fin (q.1 k), (if i ∈ U then (1 : ℝ≥0∞) else 0) := by
          rw [← Finset.sum_subtype (Finset.univ.filter (fun i => R.γ k i = a))
            (fun i => by simp) (fun i => if i ∈ U then (1 : ℝ≥0∞) else 0)]
          exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = U.card := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
          simp
      _ ≤ (R.Λ k a (coarse o)).card + (R.Λ k a (coarse' o)).card := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ ENNReal.ofReal (N ^ R.ε k) + ENNReal.ofReal (N ^ R.ε k) := by
          gcongr
          · rw [← ENNReal.ofReal_natCast]
            exact ENNReal.ofReal_le_ofReal (ChartData.Λcard hchart a _)
          · rw [← ENNReal.ofReal_natCast]
            exact ENNReal.ofReal_le_ofReal (ChartData.Λcard hchart a _)
      _ = 2 * ENNReal.ofReal (N ^ R.ε k) := by ring
  have hmain := k4_crop_angular_finite_tail.sum_lower_ratio_le BaseRef (p.mu (R.φ k) a)
    (measurable_obs N σ) hlawG.1 hlawG.2 (fun i : Γ => R.C k i.1) (fun i : Γ => D' i.1)
    (fun i => hD' i.1) hlawγ Cs hCs hsupp _ hK δ
  rw [Finset.sum_subtype (p := fun i => R.γ k i = a) (Finset.univ.filter (fun i => R.γ k i = a))
    (fun i => by simp) (fun i => p.mu (R.φ k) a (R.C k i ∩
      {z | D' i (obs N σ z) < δ * p.ρ (R.φ k) a σ (obs N σ z)}))]
  exact hmain

/-- Lower tails of the pure densities of `q` at a depth `s` with `r + s ≥ b`. -/
theorem weighted_lower (hp : Spec.Exact p) (hq : Spec.PureProfile q) (hLq : q.L = p.L - r)
    (hr : 0 ≤ r) (k : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsL : s ≤ q.L) (hbs : b ≤ r + s)
    (ε' δ X : ℝ≥0∞) :
    ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i
        {z | q.ρ k i s (obs (q.N k) s z) < ENNReal.ofReal (R.lam k i) * (ε' * (δ * X))} ≤
      ENNReal.ofReal (R.Z k)⁻¹ * (4 * ε' + 2 * ENNReal.ofReal (p.N (R.φ k) ^ R.ε k) * δ +
        2 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) *
          p.mu (R.φ k) a {z | p.ρ (R.φ k) a (r + s) (obs (p.N (R.φ k)) (r + s) z) < X}) := by
  have hraw := Exact.raw hp
  have hN : 0 < p.N (R.φ k) := by linarith [RawScalar.N_ge hraw (R.φ k)]
  set N := p.N (R.φ k) with hNdef
  have hσ0 : 0 ≤ r + s := by linarith
  have hσL : r + s ≤ p.L := by linarith
  have hlaw : ∀ a, Measurable (p.ρ (R.φ k) a (r + s)) ∧
      (p.mu (R.φ k) a).map (obs N (r + s)) = BaseRef.withDensity (p.ρ (R.φ k) a (r + s)) :=
    fun a => PureProfile.law (Exact.pure hp) (R.φ k) a (r + s) hσ0 hσL
  have hdens : ∀ i : Fin (q.1 k), ∃ D : Base → ℝ≥0∞, Measurable D ∧
      ((p.mu (R.φ k) (R.γ k i)).restrict (R.C k i)).map (obs N (r + s)) =
        BaseRef.withDensity D := by
    intro i
    have := mu_isFinite hraw (R.φ k) (R.γ k i)
    exact k4_crop_angular_finite_tail.exists_density_of_le BaseRef Measure.restrict_le_self
      (measurable_obs N (r + s)) (hlaw (R.γ k i)).2
  choose D' hD'm hD'law using hdens
  set H : Fin (p.1 (R.φ k)) → Base → ℝ≥0∞ := fun a => p.ρ (R.φ k) a (r + s)
  have hHm : ∀ a, Measurable (H a) := fun a => (hlaw a).1
  set Y : Fin (p.1 (R.φ k)) → Set Inc := fun a => {z | H a (obs N (r + s) z) < X}
  have hY : ∀ a, MeasurableSet (Y a) := fun a =>
    measurableSet_lt ((hHm a).comp (measurable_obs _ _)) measurable_const
  refine (R.weighted_transfer hraw k _ (fun i => ε' * 2 * p.mu (R.φ k) (R.γ k i) (R.C k i) +
      p.mu (R.φ k) (R.γ k i) (R.C k i ∩ {z | D' i (obs N (r + s) z) <
        δ * H (R.γ k i) (obs N (r + s) z)}) +
      p.mu (R.φ k) (R.γ k i) (R.C k i ∩ Y (R.γ k i))) ?_).trans ?_
  · intro i
    have hlawq := PureProfile.law hq k i s hs0 hsL
    rw [R.qN_eq k] at hlawq
    have hw := world_lower_tail hN (R.dt_pos k) (R.J_pos k i) (R.θ_meas k i) (R.θ_y' k i)
      (R.θ_x' k i) (ChartData.measC (R.chart k) i) (R.c_ne_zero hraw k i) (R.c_ne_top k i)
      (R.mu_eq' k i) s hlawq.1 hlawq.2 (hHm (R.γ k i)) (hD'm i) (hD'law i) ε' δ X
    rw [R.c_mul_dtJ hraw k i] at hw
    rw [R.qN_eq k]
    exact hw
  · gcongr
    have h1 : ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) * p.mu (R.φ k) (R.γ k i) (R.C k i) ≤
        2 := by
      calc ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) * p.mu (R.φ k) (R.γ k i) (R.C k i)
          ≤ ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * (2 * p.mu (R.φ k) a univ) := by
            apply sum_by_world (R.γ k) (fun a => ENNReal.ofReal (p.ω (R.φ k) a))
              (fun i => p.mu (R.φ k) (R.γ k i) (R.C k i))
            intro a
            calc ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a), p.mu (R.φ k) (R.γ k i) (R.C k i)
                = ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a),
                    p.mu (R.φ k) a (R.C k i ∩ univ) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [(Finset.mem_filter.mp hi).2, inter_univ]
              _ ≤ 2 * p.mu (R.φ k) a univ :=
                  ChartData.sum_mu_le_two (R.chart k) a MeasurableSet.univ
        _ = 2 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * p.mu (R.φ k) a univ := by
            rw [Finset.mul_sum]
            congr 1
            funext a
            ring
        _ ≤ 2 * 1 := by gcongr; exact weighted_mass_le_one hraw (R.φ k)
        _ = 2 := mul_one 2
    have h2 : ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) * p.mu (R.φ k) (R.γ k i) (R.C k i ∩
        {z | D' i (obs N (r + s) z) < δ * H (R.γ k i) (obs N (r + s) z)}) ≤
        2 * ENNReal.ofReal (N ^ R.ε k) * δ := by
      calc _ ≤ ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) *
            (2 * ENNReal.ofReal (N ^ R.ε k) * δ * p.mu (R.φ k) a univ) := by
            apply sum_by_world (R.γ k) (fun a => ENNReal.ofReal (p.ω (R.φ k) a))
            intro a
            calc _ = ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a), p.mu (R.φ k) a (R.C k i ∩
                    {z | D' i (obs N (r + s) z) < δ * p.ρ (R.φ k) a (r + s) (obs N (r + s) z)}) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [(Finset.mem_filter.mp hi).2]
              _ ≤ _ := R.world_label_lower hp k a (r + s) hσ0 hσL hbs D' hD'm hD'law δ
        _ = 2 * ENNReal.ofReal (N ^ R.ε k) * δ *
            ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * p.mu (R.φ k) a univ := by
            rw [Finset.mul_sum]
            congr 1
            funext a
            ring
        _ ≤ 2 * ENNReal.ofReal (N ^ R.ε k) * δ * 1 := by
            gcongr
            exact weighted_mass_le_one hraw (R.φ k)
        _ = _ := mul_one _
    have h3 : ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) *
        p.mu (R.φ k) (R.γ k i) (R.C k i ∩ Y (R.γ k i)) ≤
        2 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * p.mu (R.φ k) a (Y a) := by
      calc _ ≤ ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * (2 * p.mu (R.φ k) a (Y a)) := by
            apply sum_by_world (R.γ k) (fun a => ENNReal.ofReal (p.ω (R.φ k) a))
              (fun i => p.mu (R.φ k) (R.γ k i) (R.C k i ∩ Y (R.γ k i)))
            intro a
            calc _ = ∑ i ∈ Finset.univ.filter (fun i => R.γ k i = a),
                    p.mu (R.φ k) a (R.C k i ∩ Y a) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [(Finset.mem_filter.mp hi).2]
              _ ≤ 2 * p.mu (R.φ k) a (Y a) := ChartData.sum_mu_le_two (R.chart k) a (hY a)
        _ = _ := by
            rw [Finset.mul_sum]
            congr 1
            funext a
            ring
    calc ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) *
          (ε' * 2 * p.mu (R.φ k) (R.γ k i) (R.C k i) +
            p.mu (R.φ k) (R.γ k i) (R.C k i ∩ {z | D' i (obs N (r + s) z) <
              δ * H (R.γ k i) (obs N (r + s) z)}) +
            p.mu (R.φ k) (R.γ k i) (R.C k i ∩ Y (R.γ k i)))
        = ε' * 2 * ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) *
              p.mu (R.φ k) (R.γ k i) (R.C k i) +
            ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) * p.mu (R.φ k) (R.γ k i) (R.C k i ∩
              {z | D' i (obs N (r + s) z) < δ * H (R.γ k i) (obs N (r + s) z)}) +
            ∑ i, ENNReal.ofReal (p.ω (R.φ k) (R.γ k i)) *
              p.mu (R.φ k) (R.γ k i) (R.C k i ∩ Y (R.γ k i)) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ ≤ ε' * 2 * 2 + 2 * ENNReal.ofReal (N ^ R.ε k) * δ +
            2 * ∑ a, ENNReal.ofReal (p.ω (R.φ k) a) * p.mu (R.φ k) a (Y a) := by
          gcongr
      _ = _ := by ring

end RefData

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
