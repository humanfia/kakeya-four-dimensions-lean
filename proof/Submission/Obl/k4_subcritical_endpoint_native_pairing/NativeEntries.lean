import Submission.Obl.k4_subcritical_endpoint_native_pairing.ParameterBudget
import Submission.Obl.k4_subcritical_endpoint_native_pairing.OriginalGoodLines
import Submission.Obl.k4_subcritical_endpoint_native_pairing.EndpointLevel
import Submission.Obl.k4_row_cell_regularization.Palette

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set MeasureTheory
open scoped ENNReal

noncomputable section

abbrev NativeParameterIndex (n : ℕ) := Σ _ : Fin n, Σ _ : ℤ, (Fin 2 → ℤ)

/-- A finite table of occupied native parameter cells. Its original reference
sum is paid by the full assignment priors and the original palette. -/
theorem exists_native_parameter_table {α : Type*} (n : ℕ)
    (A B : Fin n → Set α) (Good : Set α) (b : α → Fin 6 → ℝ)
    (c : Fin n → Fin 5 → ℝ) (time : Fin n → ℝ)
    (prior : Fin n → ℝ) (weight : ℤ → ℝ)
    {K q g D χ H a d : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (hg : 0 < g) (hg1 : g ≤ 1)
    (hD : 0 < D) (hDK : D ≤ K * q * g) (hχ : 0 < χ) (hχg : χ ≤ q * g)
    (ha : 0 < a) (hsub : ∀ i, B i ⊆ A i)
    (htime : ∀ i, time i ∈ Icc (0 : ℝ) 1) (hc : ∀ i, |c i 4| ≤ K)
    (hgood : ∀ l ∈ Good, |b l 3| ≤ H ∧ |b l 4 + b l 0| ≤ χ)
    (hgeom : ∀ i, ∀ l ∈ A i,
      |b l 0 + time i * b l 3 - c i 0 - time i * c i 1| ≤ K * q ∧
      |b l 1 + time i * b l 4 - c i 2 - time i * c i 3 -
        c i 4 * (b l 0 + time i * b l 3)| ≤ K * q * g)
    (hprior : ∀ i, a ^ d * q ^ 2 * g / K ≤ prior i)
    (hbudget : (∑ i, q * prior i) ≤ 1)
    (hweight : ∀ v, 0 ≤ weight v)
    (hweightsum : ∀ V : Finset ℤ, (∑ v ∈ V, weight v) ≤ 1) :
    ∃ S : Finset (NativeParameterIndex n),
      (∀ i l, l ∈ B i → l ∈ Good →
        (⟨i, ⟨⌊b l 3 / χ⌋, ![⌊b l 0 / D⌋, ⌊b l 1 / D⌋]⟩⟩ : NativeParameterIndex n) ∈ S) ∧
      (∀ e ∈ S, ∃ l ∈ B e.1, l ∈ Good ∧ ⌊b l 3 / χ⌋ = e.2.1 ∧
        ![⌊b l 0 / D⌋, ⌊b l 1 / D⌋] = e.2.2) ∧
      (∑ e ∈ S, q * D ^ 2 * a ^ d * weight e.2.1) ≤ 4096 * K ^ 6 := by
  classical
  let J : Finset ℤ := Finset.Icc ⌊(-H) / χ⌋ ⌊H / χ⌋
  have hJ (l : α) (hl : l ∈ Good) : ⌊b l 3 / χ⌋ ∈ J := by
    have hb := abs_le.mp (hgood l hl).1
    exact Finset.mem_Icc.mpr
      ⟨Int.floor_mono (div_le_div_of_nonneg_right hb.1 hχ.le),
        Int.floor_mono (div_le_div_of_nonneg_right hb.2 hχ.le)⟩
  have htable (i : Fin n) (v : ℤ) :=
    native_parameter_mesh_cover (c i) hD hK hq hg hg1 hDK hχg (htime i) (hc i) (χ * v)
  choose F hFcard hFcover using htable
  let S₀ : Finset (NativeParameterIndex n) := Finset.univ.sigma (fun i => J.sigma (F i))
  let S := S₀.filter (fun e => ∃ l ∈ B e.1, l ∈ Good ∧ ⌊b l 3 / χ⌋ = e.2.1 ∧
    ![⌊b l 0 / D⌋, ⌊b l 1 / D⌋] = e.2.2)
  have hcover (i : Fin n) (l : α) (hlB : l ∈ B i) (hlG : l ∈ Good) :
      (⟨i, ⟨⌊b l 3 / χ⌋, ![⌊b l 0 / D⌋, ⌊b l 1 / D⌋]⟩⟩ : NativeParameterIndex n) ∈ S₀ := by
    have hvel := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hχ (b l 3)
    have hgeoml := hgeom i l (hsub i hlB)
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_sigma.mpr ⟨hJ l hlG, ?_⟩⟩
    exact hFcover i ⌊b l 3 / χ⌋ (b l) hvel (hgood l hlG).2 hgeoml.1 hgeoml.2
  have hbudget₀ : (∑ e ∈ S₀, q * D ^ 2 * a ^ d * weight e.2.1) ≤ 4096 * K ^ 6 := by
    have hh := native_parameter_reference_budget J weight F prior hK hq hg ha
      (fun v _ => hweight v) (hweightsum J) (fun i v _ => hFcard i v) hprior hbudget
    simpa only [S₀, Finset.sum_sigma] using hh
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i l hlB hlG
    exact Finset.mem_filter.mpr ⟨hcover i l hlB hlG, l, hlB, hlG, rfl, rfl⟩
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · apply le_trans ?_ hbudget₀
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro e _ _
    exact mul_nonneg (by positivity) (hweight e.2.1)

namespace Data

open Submission.Obl.k4_critical_intercept_concentration.Data
open Filter

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- A strict grid-depth margin resolves the thin native parameter side.
The estimate is uniform over every original assignment level. -/
theorem Prepared.eventually_native_parameter_cell_width (h : cfg.Prepared) {s M : ℝ}
    (hgap : 2 * cfg.κ * s < M) :
    ∀ᶠ k in atTop, ∀ a : cfg.AssignmentLevel k s,
      cfg.N k ^ (-M) ≤ cfg.timeLength k s * cfg.N k ^ (-cfg.κ * s) := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hev := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 1
    (show -M < -2 * cfg.κ * s by linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  filter_upwards [hev] with k hk
  intro a
  have hN : 0 < cfg.N k := zero_lt_one.trans_le (hN1 k)
  have hK : 0 < cfg.K k := zero_lt_one.trans_le (h.subpower.1 k)
  have hg : 0 ≤ cfg.N k ^ (-cfg.κ * s) := Real.rpow_nonneg hN.le _
  have hq := (Submission.Obl.k4_critical_intercept_concentration.time_length_comparison
    hN hK a.time_lower a.time_upper).2
  have hpow : cfg.N k ^ (-2 * cfg.κ * s) = (cfg.N k ^ (-cfg.κ * s)) ^ 2 := by
    rw [pow_two, ← Real.rpow_add hN]
    congr 1
    ring
  apply (mul_le_mul_iff_right₀ hK).mp
  calc
    cfg.K k * cfg.N k ^ (-M) ≤ cfg.N k ^ (-2 * cfg.κ * s) := by simpa using hk.le
    _ = (cfg.N k ^ (-cfg.κ * s)) ^ 2 := hpow
    _ ≤ cfg.K k * (cfg.timeLength k s * cfg.N k ^ (-cfg.κ * s)) := by
      simpa only [pow_two, mul_assoc, timeLength] using mul_le_mul_of_nonneg_right hq hg

/-- The full assignment budget in real original units. -/
theorem Prepared.native_assignment_real_budget (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) :
    (∑ i, cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i)) ≤ 1 := by
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hs := ENNReal.toReal_mono ENNReal.one_ne_top (h.native_assignment_budget a)
  rw [ENNReal.toReal_sum] at hs
  · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le, ENNReal.toReal_one,
      measureReal_def] using hs
  · intro i _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

/-- The actual prepared native atlas supplies an occupied finite parameter table
with a uniform original reference budget. -/
theorem Prepared.native_parameter_table (h : cfg.Prepared) {k : ℕ} {s M : ℝ}
    (a : cfg.NativeLevel k s) (hs : 0 ≤ s)
    (hχ : cfg.N k ^ (-M) ≤ cfg.timeLength k s * cfg.N k ^ (-cfg.κ * s)) :
    ∃ S : Finset (NativeParameterIndex (cfg.n k s)),
      (∀ i l, l ∈ cfg.B k s i →
        l ∈ goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M)) →
        (⟨i, ⟨⌊cfg.b k l 3 / cfg.N k ^ (-M)⌋,
          ![⌊cfg.b k l 0 / cfg.parameterWidth k s⌋,
            ⌊cfg.b k l 1 / cfg.parameterWidth k s⌋]⟩⟩ : NativeParameterIndex (cfg.n k s)) ∈ S) ∧
      (∀ e ∈ S, ∃ l ∈ cfg.B k s e.1,
        l ∈ goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M)) ∧
        ⌊cfg.b k l 3 / cfg.N k ^ (-M)⌋ = e.2.1 ∧
        ![⌊cfg.b k l 0 / cfg.parameterWidth k s⌋,
          ⌊cfg.b k l 1 / cfg.parameterWidth k s⌋] = e.2.2) ∧
      (∑ e ∈ S, cfg.timeLength k s * cfg.parameterWidth k s ^ 2 *
        cfg.hiddenWidth k s ^ cfg.d *
          (cfg.velocityWeight k (cfg.N k ^ (-M)) e.2.1).toReal) ≤ 4096 * cfg.K k ^ 6 := by
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  letI : IsProbabilityMeasure (cfg.π k) := (h.basic k).2.2.1
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hN : 0 < cfg.N k := zero_lt_one.trans_le hN1
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hg : 0 < cfg.N k ^ (-cfg.κ * s) := Real.rpow_pos_of_pos hN _
  have hg1 : cfg.N k ^ (-cfg.κ * s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith [h.rate_pos])
  have hD : 0 < cfg.parameterWidth k s := Real.rpow_pos_of_pos hN _
  have hDg : cfg.parameterWidth k s = (cfg.N k ^ (-cfg.κ * s)) ^ 2 := by
    rw [parameterWidth, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    norm_num
    ring
  have hDq : cfg.parameterWidth k s ≤ cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.κ * s) := by
    rw [hDg, pow_two]
    exact mul_le_mul_of_nonneg_right
      (Submission.Obl.k4_critical_intercept_concentration.time_length_comparison hN hKp
        a.assignments.time_lower a.assignments.time_upper).2 hg.le
  let time (i : Fin (cfg.n k s)) := ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s
  have htime (i : Fin (cfg.n k s)) : time i ∈ I (cfg.T k s) (cfg.j k s i) := by
    exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) (by positivity)⟩
  have hprior (i : Fin (cfg.n k s)) :
      cfg.hiddenWidth k s ^ cfg.d * cfg.timeLength k s ^ 2 *
        cfg.N k ^ (-cfg.κ * s) / cfg.K k ≤ (cfg.ν k).real (cfg.A k s i) := by
    have hh := ENNReal.toReal_mono (measure_ne_top (cfg.ν k) _) (a.assignments.prior_lower i)
    rw [h.horizontal_rate] at hh
    simpa only [hiddenWidth, ENNReal.toReal_ofReal (by positivity : 0 ≤
      (cfg.N k ^ (-s)) ^ cfg.d * cfg.timeLength k s ^ 2 *
        cfg.N k ^ (-cfg.κ * s) / cfg.K k), measureReal_def] using hh
  apply exists_native_parameter_table (cfg.n k s) (cfg.A k s) (cfg.B k s)
    (goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M))) (cfg.b k)
    (cfg.c k s) time (fun i => (cfg.ν k).real (cfg.A k s i))
    (fun v => (cfg.velocityWeight k (cfg.N k ^ (-M)) v).toReal)
    hK hq hg hg1 hD hDq (Real.rpow_pos_of_pos hN _) hχ
    (Real.rpow_pos_of_pos hN _) a.assignments.fitted_subset
    (fun i => Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit _ _ (htime i))
    (fun i => a.assignments.coefficient_bound i 4)
    (fun l hl => ⟨hl.1 3, hl.2⟩) ?_ hprior (h.native_assignment_real_budget a.assignments)
    (fun _ => ENNReal.toReal_nonneg) ?_
  · intro i l hl
    have hh := a.assignments.geometry i l hl (time i) (htime i)
    rw [h.horizontal_rate] at hh
    exact ⟨hh.1, hh.2.1⟩
  · intro V
    exact Submission.Obl.k4_row_cell_regularization.sum_binWeight_le_one
      (Real.rpow_pos_of_pos hN _) (cfg.π k) V

/-- Convert the native real reference budget back to the exact original
extended-real palette weights required by the matching theorem. -/
theorem Prepared.native_reference_budget_ennreal (h : cfg.Prepared) {k : ℕ} {s M C : ℝ}
    (S : Finset (NativeParameterIndex (cfg.n k s)))
    (hbudget : (∑ e ∈ S, cfg.timeLength k s * cfg.parameterWidth k s ^ 2 *
      cfg.hiddenWidth k s ^ cfg.d *
        (cfg.velocityWeight k (cfg.N k ^ (-M)) e.2.1).toReal) ≤ C) :
    (∑ e ∈ S, ENNReal.ofReal (cfg.timeLength k s * cfg.parameterWidth k s ^ 2 *
      cfg.hiddenWidth k s ^ cfg.d) *
        cfg.velocityWeight k (cfg.N k ^ (-M)) e.2.1) ≤ ENNReal.ofReal C := by
  letI : IsProbabilityMeasure (cfg.π k) := (h.basic k).2.2.1
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hcoef : 0 ≤ cfg.timeLength k s * cfg.parameterWidth k s ^ 2 *
      cfg.hiddenWidth k s ^ cfg.d := by
    dsimp only [timeLength, hiddenWidth]
    positivity
  have heq : (∑ e ∈ S, ENNReal.ofReal (cfg.timeLength k s * cfg.parameterWidth k s ^ 2 *
      cfg.hiddenWidth k s ^ cfg.d) *
        cfg.velocityWeight k (cfg.N k ^ (-M)) e.2.1) =
      ENNReal.ofReal (∑ e ∈ S, cfg.timeLength k s * cfg.parameterWidth k s ^ 2 *
        cfg.hiddenWidth k s ^ cfg.d *
          (cfg.velocityWeight k (cfg.N k ^ (-M)) e.2.1).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg hcoef ENNReal.toReal_nonneg)]
    apply Finset.sum_congr rfl
    intro e _
    rw [ENNReal.ofReal_mul hcoef, ENNReal.ofReal_toReal]
    exact measure_ne_top (cfg.π k) _
  rw [heq]
  exact ENNReal.ofReal_le_ofReal hbudget

end Data
end
end Submission.Obl.k4_subcritical_endpoint_native_pairing
