-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.ParameterCell.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_subtube_selection.Grouping
import Submission.WZ.Obl.wz_coarse_grains_assembly.CarrierNet

/- Adapted from this workspace: o197/x0567, d9e04e2b24c3, ParameterCell.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set Metric MeasureTheory Classical
open WangZahlLot.Obl.wz_coarse_grains_assembly (V O T)

/-- A fixed number of parameter classes gives a common narrow carrier and
nearly the same oriented direction within every class. -/
theorem exists_parameter_classes {θ : ℝ} (hθ : 0 < θ) :
    ∃ N : ℕ, 0 < N ∧ ∀ {n : ℕ} (x v : Fin n → V),
      (∀ i, ‖x i‖ ≤ 1) → (∀ i, ‖v i‖ = 1) →
      ∃ f : Fin n → Fin N, ∀ i j, f i = f j →
        ‖v i - v j‖ ≤ θ / 100 ∧ ∀ δ : ℝ, δ ≤ θ / 8 →
          T δ (x i) (v i) ⊆ T (θ / 4) (x j) (v j) := by
  obtain ⟨N, c, κ, hN, hκ⟩ :=
    WangZahlLot.Obl.wz_coarse_subtube_selection.exists_param_cover
      (R := 1) (by norm_num) (ε := θ / 1000) (by positivity)
  refine ⟨N, hN, ?_⟩
  intro n x v hx hv
  let f := fun i => κ (x i, v i)
  refine ⟨f, ?_⟩
  intro i j hij
  have hnorm (i : Fin n) : ‖(x i, v i)‖ ≤ 1 := by
    rw [Prod.norm_mk, hv i]
    exact max_le (hx i) le_rfl
  have hdi := hκ (x i, v i) (hnorm i)
  have hdj := hκ (x j, v j) (hnorm j)
  change κ (x i, v i) = κ (x j, v j) at hij
  rw [hij] at hdi
  have hd : dist (x i, v i) (x j, v j) < θ / 500 := by
    calc
      _ ≤ dist (x i, v i) (c (κ (x j, v j))) + dist (c (κ (x j, v j))) (x j, v j) :=
        dist_triangle _ _ _
      _ < θ / 500 := by rw [dist_comm (c _)]; linarith
  rw [Prod.dist_eq, max_lt_iff] at hd
  refine ⟨?_, ?_⟩
  · rw [← dist_eq_norm]
    linarith [hd.2]
  · intro δ hδ
    apply WangZahlLot.Obl.wz_coarse_grains_assembly.tube_containment_of_parameters
    linarith [hd.1, hd.2]

/-- One class contains a fixed fraction of any positive finite family of
nonnegative incidence weights. Its representative has positive weight. -/
theorem massful_parameter_class {n N : ℕ} (hN : 0 < N)
    (f : Fin n → Fin N) (w : Fin n → ENNReal) (hw : 0 < ∑ i, w i) :
    ∃ i₀ : Fin n, 0 < w i₀ ∧
      (N : ENNReal)⁻¹ * (∑ i, w i) ≤ ∑ i ∈ Finset.univ.filter (fun i => f i = f i₀), w i := by
  let C (k : Fin N) := ∑ i ∈ Finset.univ.filter (fun i => f i = k), w i
  have hNne : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ C hNne
  have hsum : ∑ k, C k = ∑ i, w i := by
    simp only [C, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have hmax : (∑ i, w i) ≤ (N : ENNReal) * C k := by
    rw [← hsum]
    calc
      _ ≤ ∑ _ : Fin N, C k := Finset.sum_le_sum fun j hj => hk j hj
      _ = _ := by simp
  have hkpos : 0 < C k := by
    by_contra hn
    have hz : C k = 0 := le_antisymm (le_of_not_gt hn) bot_le
    rw [hz, mul_zero] at hmax
    exact (not_le_of_gt hw) hmax
  obtain ⟨i₀, hi₀, hpos⟩ := Finset.sum_pos_iff.mp hkpos
  have hfi : f i₀ = k := (Finset.mem_filter.mp hi₀).2
  refine ⟨i₀, hpos, ?_⟩
  change _ ≤ C (f i₀)
  rw [hfi]
  calc
    _ ≤ (N : ENNReal)⁻¹ * ((N : ENNReal) * C k) := mul_le_mul' le_rfl hmax
    _ = C k := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (by simp), one_mul]

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
