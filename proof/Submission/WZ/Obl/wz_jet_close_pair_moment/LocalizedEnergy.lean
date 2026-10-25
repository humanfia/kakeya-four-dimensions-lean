-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_close_pair_moment.LocalizedEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_close_pair_moment.Energy

namespace WangZahlLot.Obl.wz_jet_close_pair_moment

/-- The inverse-square-root energy on a ball retains the square root of its
radius. This is the scale-sensitive form of the linear-count estimate. -/
theorem sum_inv_sqrt_le_of_linear_count_at_scale {ι : Type*} [Fintype ι]
    (d : ι → ℝ) {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hd : ∀ i, 0 < d i) (hupper : ∀ i, d i < R)
    (hcount : ∀ r : ℝ, 0 < r → r ≤ R →
      ((Finset.univ.filter (fun i => d i < r)).card : ℝ) ≤ A*r) :
    ∑ i, (Real.sqrt (d i))⁻¹ ≤ 10*A*Real.sqrt R := by
  classical
  have hscaled : ∀ r : ℝ, 0 < r → r ≤ 1 →
      ((Finset.univ.filter (fun i => d i/R < r)).card : ℝ) ≤ (A*R)*r := by
    intro r hr hr1
    have he : (Finset.univ.filter (fun i => d i/R < r)) =
        Finset.univ.filter (fun i => d i < r*R) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, div_lt_iff₀ hR]
    rw [he]
    have h := hcount (r*R) (mul_pos hr hR) (by nlinarith)
    nlinarith
  have h := sum_inv_sqrt_le_of_count (fun i => d i/R)
    (fun i => div_pos (hd i) hR) (mul_nonneg hA hR.le) hscaled
  have hn : (Fintype.card ι : ℝ) ≤ A*R := by
    simpa [Finset.filter_eq_self.mpr (fun i _ => hupper i)] using hcount R hR le_rfl
  have he : (∑ i, (Real.sqrt (d i/R))⁻¹) =
      Real.sqrt R * ∑ i, (Real.sqrt (d i))⁻¹ := by
    simp_rw [Real.sqrt_div (hd _).le, inv_div]
    simp only [div_eq_mul_inv, Finset.mul_sum]
  rw [he] at h
  have hroot : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsq := Real.sq_sqrt hR.le
  nlinarith

/-- The coefficient energy from distances less than `R`, excluding the
diagonal, is bounded uniformly by `sqrt R` times the density. -/
theorem coefficient_local_inverse_sqrt_energy : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {δ η R : ℝ},
      0 < δ → δ ≤ 1 → 0 < R → (∀ i, ‖q i‖ ≤ 10) →
      (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
      (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
        (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ^(-η)*(r/δ)) →
    ∀ i : Fin n,
      (∑ j, if j ≠ i ∧ dist (q i) (q j) < R then
        (Real.sqrt (dist (q i) (q j)))⁻¹ else 0) ≤
      C*(δ^(-η)/δ)*Real.sqrt R := by
  classical
  obtain ⟨E, hE, hglobal⟩ := coefficient_inverse_sqrt_energy
  refine ⟨E+10, by positivity, ?_⟩
  intro n q δ η R hδ hδ1 hR hq hsep hcount i
  have hA : 0 ≤ δ^(-η)/δ := by positivity
  by_cases hR1 : R ≤ 1
  · let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ i ∧ dist (q i) (q j) < R)
    let d : S → ℝ := fun j => dist (q i) (q j)
    have hd : ∀ j, 0 < d j := by
      intro j
      have hj := (Finset.mem_filter.mp j.property).2.1
      exact hδ.trans_le (hsep i j (Ne.symm hj))
    have hu : ∀ j, d j < R := fun j => (Finset.mem_filter.mp j.property).2.2
    have hc : ∀ r : ℝ, 0 < r → r ≤ R →
        ((Finset.univ.filter (fun j : S => d j < r)).card : ℝ) ≤ (δ^(-η)/δ)*r := by
      intro r hr hrR
      by_cases hdr : δ ≤ r
      · let F : Finset (Fin n) := Finset.univ.filter (fun j => q j ∈ Metric.ball (q i) r)
        have hf : (↑F : Set (Fin n)) = {j | q j ∈ Metric.ball (q i) r} := by
          ext j
          simp [F]
        have hcard : (Finset.univ.filter (fun j : S => d j < r)).card ≤ F.card := by
          apply Finset.card_le_card_of_injOn (fun j : S => (j : Fin n))
          · intro j hj
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, ?_⟩
            simpa only [Metric.mem_ball, dist_comm] using (Finset.mem_filter.mp hj).2
          · intro a ha b hb hab
            exact Subtype.ext hab
        have hh := hcount (q i) r hdr (hrR.trans hR1)
        rw [← hf, Set.ncard_coe_finset] at hh
        have hh' : ((Finset.univ.filter (fun j : S => d j < r)).card : ℝ) ≤ (F.card : ℝ) :=
          Nat.cast_le.mpr hcard
        calc
          _ ≤ (F.card : ℝ) := hh'
          _ ≤ δ^(-η)*(r/δ) := hh
          _ = (δ^(-η)/δ)*r := by ring
      · have hempty : Finset.univ.filter (fun j : S => d j < r) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro j hj hdj
          have hji := (Finset.mem_filter.mp j.property).2.1
          have hdist := hsep i j (Ne.symm hji)
          change dist (q i) (q j) < r at hdj
          linarith
        rw [hempty, Finset.card_empty, Nat.cast_zero]
        positivity
    have h := sum_inv_sqrt_le_of_linear_count_at_scale d hA hR hd hu hc
    have he : (∑ j : S, (Real.sqrt (d j))⁻¹) =
        ∑ j : Fin n, if j ≠ i ∧ dist (q i) (q j) < R then
          (Real.sqrt (dist (q i) (q j)))⁻¹ else 0 := by
      change (∑ j ∈ S.attach, (Real.sqrt (dist (q i) (q j)))⁻¹) = _
      rw [Finset.sum_attach S (fun j => (Real.sqrt (dist (q i) (q j)))⁻¹)]
      simp [S, Finset.sum_filter]
    rw [he] at h
    apply h.trans
    gcongr
    linarith
  · have hroot : 1 ≤ Real.sqrt R := (Real.one_le_sqrt).mpr (le_of_not_ge hR1)
    have hsum : (∑ j, if j ≠ i ∧ dist (q i) (q j) < R then
        (Real.sqrt (dist (q i) (q j)))⁻¹ else 0) ≤
        ∑ j, (Real.sqrt (dist (q i) (q j)))⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs
      · exact le_rfl
      · positivity
    apply hsum.trans ((hglobal hδ hδ1 hq hsep hcount i).trans ?_)
    calc
      E*(δ^(-η)/δ) ≤ E*(δ^(-η)/δ)*Real.sqrt R := by
        nlinarith [mul_nonneg hE.le hA]
      _ ≤ (E+10)*(δ^(-η)/δ)*Real.sqrt R := by gcongr; linarith

end WangZahlLot.Obl.wz_jet_close_pair_moment
