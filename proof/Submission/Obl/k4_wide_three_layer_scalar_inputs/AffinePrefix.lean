import Submission.Obl.k4_wide_three_layer_scalar_inputs.AffineCoefficients
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Layers
import Submission.Obl.k4_wide_three_layer_scalar_inputs.InheritedBridge
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Blocks
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.FromPartition
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MeasureTheory Set Filter

noncomputable section

/-- One small input loss gives both affine coefficient budgets. The stronger bound
`N^(2s)` is independent of the final requested output loss. -/
theorem eventually_affine_prefix_budget {s₀ s κ : ℝ}
    (hs₀ : 0 < s₀) (hs₀s : s₀ < s) (hs : s < 3 * s₀ / 2) (hκ : κ ≤ 1) :
    ∀ᶠ N : ℝ in atTop, ∀ σ K q : ℝ, 0 ≤ σ → σ ≤ s₀ / 20 →
      1 ≤ K → K ≤ N ^ σ → 0 < q → N ^ (-κ * s) / K ≤ q →
      2 * N ^ σ + K * N ^ (-s) +
        3 * (1 + 2 * N ^ σ) ^ 2 * (K * (1 + N ^ (-s) / q ^ 2)) ≤ N ^ (2 * s) ∧
      N ^ (2 * s) ≤ N ^ (5 * s₀) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show 0 < s₀ / 4 by positivity)).eventually_ge_atTop 100]
    with N hN h100
  intro σ K q hσ hσ₀ hK hKN hq hqlo
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hspos : 0 < s := hs₀.trans hs₀s
  have hK₀ : 0 < K := zero_lt_one.trans_le hK
  have hA : 1 ≤ N ^ σ := Real.one_le_rpow hN hσ
  have hcancel : N ^ (κ * s) * N ^ (-κ * s) = 1 := by
    rw [← Real.rpow_add hN₀, show κ * s + -κ * s = 0 by ring, Real.rpow_zero]
  have hqinv : q⁻¹ ≤ K * N ^ (κ * s) := by
    rw [← one_div]
    apply (div_le_iff₀ hq).mpr
    have hh := mul_le_mul_of_nonneg_left hqlo (show 0 ≤ K * N ^ (κ * s) by positivity)
    have heq : (K * N ^ (κ * s)) * (N ^ (-κ * s) / K) = 1 := by
      calc
        _ = N ^ (κ * s) * N ^ (-κ * s) := by field_simp <;> ring
        _ = 1 := hcancel
    rw [heq] at hh
    exact hh
  have htime : N ^ (-s) * (N ^ (κ * s)) ^ 2 ≤ N ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN₀.le, ← Real.rpow_add hN₀]
    apply Real.rpow_le_rpow_of_exponent_le hN
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_right hκ hspos.le]
  have hratio : N ^ (-s) / q ^ 2 ≤ N ^ (s + 2 * σ) := by
    rw [div_eq_mul_inv, ← inv_pow]
    calc
      _ ≤ N ^ (-s) * (K * N ^ (κ * s)) ^ 2 := by gcongr
      _ = K ^ 2 * (N ^ (-s) * (N ^ (κ * s)) ^ 2) := by ring
      _ ≤ (N ^ σ) ^ 2 * N ^ s := by gcongr
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN₀.le, ← Real.rpow_add hN₀]
        congr 1
        ring
  have hR : 1 ≤ N ^ (s + 2 * σ) := Real.one_le_rpow hN (by positivity)
  have hB : K * (1 + N ^ (-s) / q ^ 2) ≤ 2 * N ^ (s + 3 * σ) := by
    calc
      _ ≤ N ^ σ * (2 * N ^ (s + 2 * σ)) := by gcongr; linarith
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add hN₀]
        congr 2
        ring
  have hbig : N ^ σ ≤ N ^ (s + 5 * σ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hproduct : (N ^ σ) ^ 2 * N ^ (s + 3 * σ) = N ^ (s + 5 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN₀.le, ← Real.rpow_add hN₀]
    congr 1
    ring
  have hraw : 2 * N ^ σ + K * N ^ (-s) +
      3 * (1 + 2 * N ^ σ) ^ 2 * (K * (1 + N ^ (-s) / q ^ 2)) ≤
      100 * N ^ (s + 5 * σ) := by
    have ha : N ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
    calc
      _ ≤ 3 * N ^ σ + 3 * (3 * N ^ σ) ^ 2 * (2 * N ^ (s + 3 * σ)) := by
        have hKa : K * N ^ (-s) ≤ N ^ σ :=
          (mul_le_mul_of_nonneg_left ha hK₀.le).trans (by simpa using hKN)
        gcongr
        · linarith
        · linarith
      _ = 3 * N ^ σ + 54 * ((N ^ σ) ^ 2 * N ^ (s + 3 * σ)) := by ring
      _ = 3 * N ^ σ + 54 * N ^ (s + 5 * σ) := by rw [hproduct]
      _ ≤ _ := by nlinarith [Real.rpow_nonneg hN₀.le (s + 5 * σ)]
  constructor
  · calc
      _ ≤ 100 * N ^ (s + 5 * σ) := hraw
      _ ≤ N ^ (s₀ / 4) * N ^ (s + 5 * σ) := by gcongr
      _ = N ^ (s₀ / 4 + (s + 5 * σ)) := (Real.rpow_add hN₀ _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The calibrated affine graph is bounded using one genuinely occupied original
projected label, then packaged with the unchanged original block and law. -/
theorem exists_affine_prefix_of_layers {α : Type} [MeasurableSpace α] {cfg : Data α}
    {k : ℕ} {s s₀ σ ε R Rcap χ D u : ℝ} {depth : Fin 3 → ℝ}
    (hN : 1 ≤ cfg.N k) (hK : 1 ≤ cfg.K k) (hs : 0 ≤ s) (hσ : 0 ≤ σ) (hε : 0 ≤ ε)
    (hB : Inherited.Native.BlocksAt cfg.comparisonData k s Rcap)
    (layers : ComparedLayers cfg k σ R χ D depth s u)
    (i : Fin (cfg.n k s)) (lam : Measure (α × ℝ)) (hle : lam ≤ layers.ρs)
    (hpos : 0 < lam univ)
    (hsupp : ∀ᵐ p ∂lam, p.1 ∈ cfg.B k s i ∧
      p.2 ∈ Submission.Obl.k4_critical_conditional_row_preparation.Data.I (cfg.T k s) (cfg.j k s i))
    (hmass : ENNReal.ofReal ((cfg.N k ^ ε)⁻¹) *
      (ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s i)) ≤ lam univ)
    (hnum : 2 * cfg.N k ^ σ + cfg.K k * cfg.N k ^ (-s) +
      3 * (1 + 2 * cfg.N k ^ σ) ^ 2 *
        (cfg.K k * (1 + cfg.N k ^ (-s) / (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2)) ≤
          cfg.N k ^ (2 * s))
    (hfixed : cfg.N k ^ (2 * s) ≤ cfg.N k ^ (5 * s₀)) :
    ∃ P : Support.BlockPrefix cfg k s (cfg.N k ^ ε), P.i = i ∧ P.lam = lam ∧
      (∀ e, |P.L e| ≤ cfg.N k ^ (2 * s)) ∧ (∀ e, |P.L e| ≤ cfg.N k ^ (5 * s₀)) := by
  classical
  have hN₀ : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hne : lam ≠ 0 := by intro hz; simpa [hz] using hpos
  letI : NeZero lam := ⟨hne⟩
  obtain ⟨p, hp, hcover⟩ := (hsupp.and (ae_mono hle layers.cover)).exists
  obtain ⟨i₀, hi₀⟩ := hcover 0
  have hbound : ∀ e, |cfg.b k p.1 e| ≤ cfg.N k ^ σ :=
    ((layers.piece 0 i₀).1 p.1 hi₀).2.2.2
  have hpow : (0 : ℝ) < (2 : ℝ) ^ cfg.T k s := by positivity
  have hq : 0 < ((2 : ℝ) ^ cfg.T k s)⁻¹ := by positivity
  have hq₁ : ((2 : ℝ) ^ cfg.T k s)⁻¹ ≤ 1 := by
    have hh := inv_anti₀ (by norm_num : (0 : ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := cfg.T k s))
    simpa using hh
  have ht : p.2 ∈ Icc (0 : ℝ) 1 := by
    have hstart : (0 : ℝ) ≤ ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s := by positivity
    have hend : (((cfg.j k s i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ cfg.T k s ≤ 1 := by
      apply (div_le_one hpow).mpr
      exact_mod_cast Nat.succ_le_of_lt (cfg.j k s i).isLt
    exact ⟨hstart.trans hp.2.1, hp.2.2.trans hend⟩
  have ht_abs : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hcoords (e e' : Fin 6) : |cfg.b k p.1 e + p.2 * cfg.b k p.1 e'| ≤ 2 * cfg.N k ^ σ := by
    calc
      _ ≤ |cfg.b k p.1 e| + |p.2| * |cfg.b k p.1 e'| := by
        simpa only [abs_mul] using abs_add_le (cfg.b k p.1 e) (p.2 * cfg.b k p.1 e')
      _ ≤ cfg.N k ^ σ + 1 * cfg.N k ^ σ := by gcongr; exact hbound e; exact hbound e'
      _ = _ := by ring
  obtain ⟨Lc, hform, h3, hslope⟩ := hB.affine i
  have hfit := (hB.fit i p.1 hp.1 p.2 hp.2).1
  rw [Inherited.Native.eval_horizontalForm hform, Inherited.Native.blockGraph_eq hform] at hfit
  change |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
    (Lc 0 + Lc 1 * p.2 + Lc 2 * (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) +
      Lc 3 * (cfg.b k p.1 1 + p.2 * cfg.b k p.1 4))| ≤ cfg.K k * cfg.N k ^ (-s) at hfit
  have hsl := hslope p.1 hp.1 p.2 hp.2
  change |Lc 1 - (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) * Lc 3| +
    |Lc 2 + p.2 * Lc 3| ≤
      cfg.K k * (1 + cfg.N k ^ (-s) / ((2 : ℝ) ^ cfg.T k s)⁻¹) at hsl
  have hratio : cfg.N k ^ (-s) / ((2 : ℝ) ^ cfg.T k s)⁻¹ ≤
      cfg.N k ^ (-s) / (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2 := by
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hN₀.le _) (sq_pos_of_pos hq)
      (by nlinarith : (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2 ≤ ((2 : ℝ) ^ cfg.T k s)⁻¹)
  have hsl' := hsl.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hratio)
    (zero_le_one.trans hK))
  have hraw := affine_coefficients_from_sample Lc
    (by linarith [Real.one_le_rpow hN hσ] : 1 ≤ 2 * cfg.N k ^ σ)
    (by positivity : 0 ≤ cfg.K k * cfg.N k ^ (-s)) (by positivity) ht_abs
    (hcoords 0 3) (hcoords 1 4) (hcoords 2 5) h3 hsl' hfit
  have hLc : ∀ e, |Lc e| ≤ cfg.N k ^ (2 * s) := fun e => (hraw e).trans hnum
  have hLcε : ∀ e, |Lc e| ≤ cfg.N k ^ ε * cfg.N k ^ (2 * s) := by
    intro e
    exact (hLc e).trans (le_mul_of_one_le_left (Real.rpow_nonneg hN₀.le _) (Real.one_le_rpow hN hε))
  have hsupp' : ∀ᵐ p ∂lam, p.1 ∈ cfg.B k s i ∧
      p.2 ∈ Icc ((cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s)
        ((cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s + ((2 : ℝ) ^ cfg.T k s)⁻¹) := by
    filter_upwards [hsupp] with p hp
    refine ⟨hp.1, ?_⟩
    convert hp.2 using 1
    unfold Submission.Obl.k4_critical_conditional_row_preparation.Data.I
    congr 1
    field_simp
  let P : Support.BlockPrefix cfg k s (cfg.N k ^ ε) := {
    i := i, L := Lc, hL := hform, L_bd := hLcε, H_one := Real.one_le_rpow hN hε,
    lam := lam, lam_le := hle.trans layers.le_rho, lam_supp := hsupp', lam_mass := hmass }
  exact ⟨P, rfl, rfl, hLc, fun e => (hLc e).trans hfixed⟩

/-- The actual affine prefix is available uniformly at all sufficiently large indices
for every input loss at most `s₀/20` and every final output loss. -/
theorem eventually_exists_affine_prefix {α : Type} [MeasurableSpace α] {cfg : Data α}
    (hv : cfg.Valid) {s₀ s : ℝ} (hs₀ : 0 < s₀) (hs₀s : s₀ < s) (hs : s < 3 * s₀ / 2) :
    ∀ᶠ k in atTop, ∀ σ ε : ℝ, 0 ≤ σ → σ ≤ s₀ / 20 → 0 ≤ ε → cfg.K k ≤ cfg.N k ^ σ →
      ∀ R Rcap χ D u : ℝ, ∀ depth : Fin 3 → ℝ,
      Inherited.Native.BlocksAt cfg.comparisonData k s Rcap →
      ∀ layers : ComparedLayers cfg k σ R χ D depth s u,
      ∀ (i : Fin (cfg.n k s)) (lam : Measure (α × ℝ)), lam ≤ layers.ρs → 0 < lam univ →
      (∀ᵐ p ∂lam, p.1 ∈ cfg.B k s i ∧
        p.2 ∈ Submission.Obl.k4_critical_conditional_row_preparation.Data.I (cfg.T k s) (cfg.j k s i)) →
      ENNReal.ofReal ((cfg.N k ^ ε)⁻¹) *
        (ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s i)) ≤ lam univ →
      ∃ P : Support.BlockPrefix cfg k s (cfg.N k ^ ε), P.i = i ∧ P.lam = lam ∧
        (∀ e, |P.L e| ≤ cfg.N k ^ (2 * s)) ∧ (∀ e, |P.L e| ≤ cfg.N k ^ (5 * s₀)) := by
  filter_upwards [hv.scale_limit.eventually
    (eventually_affine_prefix_budget hs₀ hs₀s hs hv.rate_le_one)] with k hk
  intro σ ε hσ hσ₀ hε hKN R Rcap χ D u depth hB layers i lam hle hpos hsupp hmass
  have hN : 1 ≤ cfg.N k := by linarith [hv.scale k]
  have hN₀ : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hK : 1 ≤ cfg.K k := hv.subpower.1 k
  have hK₀ : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hq : 0 < ((2 : ℝ) ^ cfg.T k s)⁻¹ := by positivity
  have hqlo : cfg.N k ^ (-cfg.κ * s) / cfg.K k ≤ ((2 : ℝ) ^ cfg.T k s)⁻¹ := by
    have hh := inv_anti₀ (show (0 : ℝ) < (2 : ℝ) ^ cfg.T k s by positivity) hB.T_hi
    calc
      _ = (cfg.K k * cfg.N k ^ (cfg.κ * s))⁻¹ := by
        rw [show -cfg.κ * s = -(cfg.κ * s) by ring, Real.rpow_neg hN₀.le,
          div_eq_mul_inv, mul_inv_rev]
      _ ≤ _ := hh
  have hnum := hk σ (cfg.K k) (((2 : ℝ) ^ cfg.T k s)⁻¹) hσ hσ₀ hK hKN hq hqlo
  exact exists_affine_prefix_of_layers hN hK (hs₀.le.trans hs₀s.le) hσ hε hB layers
    i lam hle hpos hsupp hmass hnum.1 hnum.2

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
