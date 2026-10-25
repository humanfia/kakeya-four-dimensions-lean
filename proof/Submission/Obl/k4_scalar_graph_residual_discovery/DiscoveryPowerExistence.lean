/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 09bc463f, file DiscoveryPowerExistence.lean.
   Helper namespace and imports renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryPowerBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryPowerSchedule

open Filter
open scoped ENNReal BigOperators
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

theorem list_formula_plus_one_monomial {N H Hg Hbig ω : ℝ}
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hHg : 1 ≤ Hg) (hHbig : 1 ≤ Hbig)
    (hHHbig : H ≤ Hbig) (hHgHbig : Hg ≤ Hbig) (hω : 0 ≤ ω) (J : ℕ) :
    discoveryListFormula N H Hg (eta N ω) J + 1 ≤
      40000000 * Hbig ^ 10 * N ^ (3 * ω + 2 / (J : ℝ)) := by
  have hh := list_formula_monomial hN hH hHg hHbig hHHbig hHgHbig hω J
  have hmin : 1 ≤ Hbig ^ 10 * N ^ (3 * ω + 2 / (J : ℝ)) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hHbig)
      (Real.one_le_rpow hN (by positivity))
  nlinarith only [hh, hmin]

theorem eventually_selection_budget {N H Hg Hbig : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : ∀ k, 1 ≤ H k) (hHg : ∀ k, 1 ≤ Hg k) (hHbig : Subpower N Hbig)
    (hHHbig : ∀ k, H k ≤ Hbig k) (hHgHbig : ∀ k, Hg k ≤ Hbig k)
    (C J₁ J₂ : ℕ) {ω α : ℝ} (hω : 0 ≤ ω)
    (hgap : (3 * ω + 2 / (J₁ : ℝ)) * ((C : ℝ) * J₂ + 1) < α / 10) :
    ∀ᶠ k in atTop,
      ((4 : ℝ≥0∞) ^ 3 * (discoveryListBudget (N k) (H k) (Hg k) (eta (N k) ω) J₁ : ℝ≥0∞)) ^
        (C * J₂ + 1) ≤ ENNReal.ofReal (selection (N k) α) := by
  have hP := subpower_polynomial hN hNt hHbig (A := 40000000) (by norm_num) 10
  have hh := DiscoveryGrowth.eventually_ceil_selection_cost_le_ennreal hN hNt hP
    (Finset.range (C * J₂ + 1))
    (fun _ k => discoveryListFormula (N k) (H k) (Hg k) (eta (N k) ω) J₁ + 1)
    (C := 64) (a := 3 * ω + 2 / (J₁ : ℝ)) (b := α / 10)
    (by norm_num) (by positivity)
    (by simpa only [Finset.card_range, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hgap)
    (fun _ _ => Eventually.of_forall (fun k => add_nonneg
      (discovery_list_formula_nonneg (by linarith [hN k]) (by linarith [hH k])
        (by linarith [hHg k]) (Real.rpow_nonneg (by linarith [hN k]) _) J₁) zero_le_one))
    (fun _ _ => Eventually.of_forall (fun k =>
      list_formula_plus_one_monomial (hN k) (hH k) (hHg k) (hHbig.1 k)
        (hHHbig k) (hHgHbig k) hω J₁))
  norm_num only [Nat.cast_ofNat] at hh
  simpa only [Finset.prod_const, Finset.card_range, discoveryListBudget, selection,
    show (4 : ℝ≥0∞) ^ 3 = 64 by norm_num] using hh

theorem density_representation {N H ω α : ℝ} (hN : 0 < N) :
    H * selection N α / (mass N ω / 2) = 2 * H * N ^ (α / 10 + ω / 4) := by
  have hm : (mass N ω / 2)⁻¹ = 2 * N ^ (ω / 4) := by
    rw [inv_div, mass, Real.rpow_neg hN.le]
    simp only [div_eq_mul_inv, inv_inv]
  calc
    _ = H * N ^ (α / 10) * (2 * N ^ (ω / 4)) := by
      rw [div_eq_mul_inv, hm, selection]
    _ = 2 * H * (N ^ (α / 10) * N ^ (ω / 4)) := by ring
    _ = _ := by rw [← Real.rpow_add hN]

theorem eventually_mass_budget {N H Hbig : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hHbig : Subpower N Hbig)
    (hHHbig : ∀ k, H k ≤ Hbig k) {ω α : ℝ} (hgap : α / 10 + ω / 4 < α) :
    ∀ᶠ k in atTop, H k * selection (N k) α / (mass (N k) ω / 2) ≤ N k ^ α := by
  have hh := DiscoveryGrowth.eventually_monomial_lt hN hNt hHbig 1 hgap (A := 2) (by norm_num)
  filter_upwards [hh] with k hk
  rw [density_representation (by linarith [hN k])]
  apply le_trans ?_ hk.le
  simpa only [pow_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hHHbig k) (by norm_num : (0 : ℝ) ≤ 2))
    (Real.rpow_nonneg (by linarith [hN k]) _)

/-- Every nonprecision discovery budget follows from the five strict exponent gaps.
The exponent `τ` is fixed before the sample index, as required by the graph hypothesis. -/
theorem eventually_power_bounds {N K H Hg : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Subpower N K) (hH : Subpower N H) (hHg : Subpower N Hg)
    {d S δ α Cmk ω τ : ℝ} (hd : d ≤ 1) (hδ : 0 < δ) (hα : 0 < α)
    (hCmk : 0 < Cmk) (hω : 0 < ω) (hτ : 0 < τ) (hrel : S * τ = 4 * ω)
    (C₁ C J₁ J₂ : ℕ)
    (hselection : (3 * ω + 2 / (J₁ : ℝ)) * ((C : ℝ) * J₂ + 1) + ω / 4 < α / 100)
    (hcap : ω + 4 / (J₂ : ℝ) < α / 100)
    (hsupport : 24 * ω + 3 * τ + 2 / (J₂ : ℝ) < α / 100)
    (htime : 2 / (J₁ : ℝ) < α / 100) (hresidual : 1 / (J₂ : ℝ) < α / 100) :
    ∀ᶠ k in atTop, Nonempty
      (DiscoveryPowerBounds (N k) (H k) (Hg k) (K k) d S δ α Cmk τ C₁ C J₁ J₂) := by
  let Hb : ℕ → ℝ := fun k => majorant (K k) (H k) (Hg k)
  have hHb : Subpower N Hb := majorant_subpower hN hK hH hHg
  have hdom (k : ℕ) : 1 ≤ Hb k ∧ K k ≤ Hb k ∧ H k ≤ Hb k ∧ Hg k ≤ Hb k :=
    majorant_one_le (hK.1 k) (hH.1 k) (hHg.1 k)
  have hKHb : ∀ k, K k ≤ Hb k := fun k => (hdom k).2.1
  have hHHb : ∀ k, H k ≤ Hb k := fun k => (hdom k).2.2.1
  have hHgHb : ∀ k, Hg k ≤ Hb k := fun k => (hdom k).2.2.2
  have hraw : 0 ≤ (3 * ω + 2 / (J₁ : ℝ)) * ((C : ℝ) * J₂ + 1) := by positivity
  have hsrc := eventually_source_budget hN hNt hHg C₁ J₁ hω hδ
  have hcut := eventually_cut_budget hN hNt hHb C J₂ hω
  have hang := eventually_angular_budget hN hNt hK hHg hHb hKHb hHgHb hω hrel
  have hsel := eventually_selection_budget hN hNt hH.1 hHg.1 hHb hHHb hHgHb C J₁ J₂ (α := α) hω.le
    (by linarith)
  have hmass := eventually_mass_budget hN hNt hHb hHHb (ω := ω) (α := α) (by linarith)
  have hrc := DiscoveryGrowth.eventually_monomial_lt hN hNt hHb 4
    (a := 2 / (J₁ : ℝ)) (b := α) (by linarith) (A := 196608) (by norm_num)
  have hres := DiscoveryGrowth.eventually_monomial_lt hN hNt hHb 1
    (a := 1 / (J₂ : ℝ)) (b := α) (by linarith) (A := 42) (by norm_num)
  have hbc := DiscoveryGrowth.eventually_monomial_lt hN hNt hHb 6
    (a := ω + 4 / (J₂ : ℝ)) (b := α) (by linarith) (A := 9) (by norm_num)
  have hss := DiscoveryGrowth.eventually_monomial_lt hN hNt hHb 25
    (a := 24 * ω + 3 * τ + 2 / (J₂ : ℝ)) (b := α) (by linarith)
    (A := 3000000000000000000000000 * (max 1 Cmk + 1) ^ 3) (by positivity)
  filter_upwards [hsrc, hcut, hang, hsel, hmass, hrc, hres, hbc, hss, hK.2 α hα, hHg.2 α hα]
    with k hsrc hcut hang hsel hmass hrc hres hbc hss hKnormal hHgnormal
  have hNk : 0 < N k := by linarith [hN k]
  have hbase := base_budgets (hN k) (hH.1 k) (hHb.1 k) (hHHb k) hω.le
  have hgeom := geometry_budgets (hN k) (hH.1 k) (hHg.1 k) (hHb.1 k)
    (hHHb k) (hHgHb k) hCmk hω.le hτ.le
  refine ⟨{
    η := eta (N k) ω
    m₀ := mass (N k) ω
    Hbig := Hb k
    Kbase := base (N k) (Hb k) ω
    Kgeom := geom (N k) (Hb k) Cmk ω τ
    Lfill := fill (N k) (Hb k) Cmk ω τ
    P := selection (N k) α
    Knormal := N k ^ α
    eta_pos := Real.rpow_pos_of_pos hNk _
    eta_le_one := eta_le_one (hN k) hω.le
    tau_pos := hτ
    mass_pos := Real.rpow_pos_of_pos hNk _
    one_le_Hbig := hHb.1 k
    prep_le := hHHb k
    graph_le := hHgHb k
    original_le := hKHb k
    source_budget := hsrc
    cut_budget := hcut
    Kbase_pos := hbase.1
    Kgeom_pos := hgeom.2.1
    Lfill_pos := hgeom.1
    Kbase_density := hbase.2.1
    Kbase_prior := hbase.2.2
    filling_budget := hgeom.2.2.1
    filling_le := hgeom.2.2.2.1
    angular_budget := hang
    hereditary_budget := hgeom.2.2.2.2.1
    overlap_budget := hgeom.2.2.2.2.2
    one_le_Knormal := Real.one_le_rpow (hN k) hα.le
    constant_budget := le_rfl
    original_budget := hKnormal
    P_pos := Real.rpow_pos_of_pos hNk _
    selection_budget := hsel
    mass_budget := hmass
    row_budget := hHgnormal
    row_compare_budget := ?_
    residual_budget := ?_
    cap_budget := ?_
    support_budget := ?_
  }⟩
  · exact (time_constant_monomial (hN k) (hH.1 k) (hHg.1 k) (hHb.1 k)
      (hHHb k) (hHgHb k) J₁).trans hrc.le
  · exact (residual_constant_monomial (hN k) (hHb.1 k) (hHgHb k) J₂).trans
      (by simpa only [pow_one] using hres.le)
  · exact (cap_constant_monomial (hN k) (hH.1 k) (hHb.1 k) (hHHb k) J₂).trans hbc.le
  · exact (support_constant_monomial (hN k) (by linarith [hHg.1 k]) (hHb.1 k)
      (hHgHb k) hω.le hτ.le hd J₂).trans hss.le

end Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryPowerSchedule
