-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.FrostmanExtraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.DyadicExtraction

/-!
# Extracting separated planar Frostman sets

The accepted dyadic quota extraction for o052 is applied to a finite planar
Frostman set. The resulting subset is separated at the original scale, has
cardinality comparable to the reciprocal Frostman mass at that scale, and
retains a normalized linear Frostman bound with an absolute constant loss.

Ported from session x0444 (o141, commit 89688bb).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open WangZahlLot.Obl.wz_normalized_projection_coarse_fine
open scoped Classical

lemma closed_ball_count_from_open_ball_count {E : Type*} [PseudoMetricSpace E]
    (V : Finset E) {r δ : ℝ} (hr : 0 < r) (hrδ : r ≤ δ) (hδr : δ < 2 * r)
    (hcount : ∀ (x : E) (ρ : ℝ), δ ≤ ρ → ρ ≤ 1 →
      ((V.filter (fun a => a ∈ Metric.ball x ρ)).card : ℝ) ≤ 18 * (ρ / δ)) :
    ∀ (x : E) (ρ : ℝ), r ≤ ρ → ρ ≤ 1 / 2 →
      (((V : Set E) ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ 36 * ρ / r := by
  classical
  intro x ρ hρ hρhalf
  have hρpos := hr.trans_le hρ
  have hQsub : (V : Set E) ∩ Metric.closedBall x ρ ⊆
      ↑(V.filter (fun a => a ∈ Metric.ball x (2 * ρ))) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨ha.1,
      Metric.mem_ball.mpr ((Metric.mem_closedBall.mp ha.2).trans_lt (by linarith only [hρpos]))⟩
  have hc := Set.ncard_le_ncard hQsub (Finset.finite_toSet _)
  have hb := hcount x (2 * ρ) (by linarith only [hδr, hρ]) (by linarith only [hρhalf])
  have hbound : ((V.filter (fun a => a ∈ Metric.ball x (2 * ρ))).card : ℝ) ≤
      36 * ρ / r := by
    calc _ ≤ 18 * (2 * ρ / δ) := hb
      _ ≤ 18 * (2 * ρ / r) := by gcongr
      _ = 36 * ρ / r := by ring
  exact (show (((V : Set E) ∩ Metric.closedBall x ρ).ncard : ℝ) ≤
    ((V.filter (fun a => a ∈ Metric.ball x (2 * ρ))).card : ℝ) by
      exact_mod_cast hc).trans hbound

set_option maxHeartbeats 4000000 in
/-- A finite planar linear Frostman set contains a separated linear Frostman
subset, without requiring any separation in the input set. -/
theorem planar_frostman_separated_subset_core
    {r C : ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hr : 0 < r) (hr1 : r ≤ 1) (hC : 1 ≤ C)
    (hP : P.Finite) (hPne : P.Nonempty)
    (hFr : ∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ →
      ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ C * ρ * P.ncard) :
    ∃ Q ⊆ P, Q.Finite ∧ Q.Nonempty ∧
      1 / (40 * C * r) ≤ (Q.ncard : ℝ) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → r ≤ dist x y) ∧
      ∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ρ ≤ 1 / 2 →
        ((Q ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ 36 * ρ / r := by
  classical
  obtain ⟨J, hJlow, hJhigh⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hpow (n : ℕ) : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by simp
  have hrJ : r ≤ ((2 : ℝ) ^ J)⁻¹ := by simpa only [hpow] using hJhigh
  have hJr : ((2 : ℝ) ^ J)⁻¹ < 2 * r := by
    rw [pow_succ, hpow] at hJlow
    linarith
  let U := hP.toFinset
  have hU : (↑U : Set (EuclideanSpace ℝ (Fin 2))) = P := hP.coe_toFinset
  have hUcard : U.card = P.ncard := by rw [← hU, Set.ncard_coe_finset]
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hscale (k : ℕ) (hk : k ≤ J) : r ≤ ((2 : ℝ) ^ k)⁻¹ := by
    apply hrJ.trans
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num) hk
  have hcell (k : ℕ) (hk : k ≤ J) (l : Fin 2 → ℤ) :
      ((U.filter (fun a => dyadicLabel k a = l)).card : ℝ) ≤
        (2 * C) * (((2 : ℝ) ^ k)⁻¹) ^ (1 : ℝ) * U.card := by
    by_cases he : U.filter (fun a => dyadicLabel k a = l) = ∅
    · simp only [he, Finset.card_empty, Nat.cast_zero]
      positivity
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hla := (Finset.mem_filter.mp ha).2
    have hsub : (↑(U.filter (fun b => dyadicLabel k b = l)) : Set _) ⊆
        P ∩ Metric.closedBall a (2 * ((2 : ℝ) ^ k)⁻¹) := by
      intro b hb
      obtain ⟨hbU, hbl⟩ := Finset.mem_filter.mp hb
      refine ⟨by simpa only [← hU, Finset.mem_coe] using hbU, ?_⟩
      apply Metric.mem_closedBall.mpr
      calc dist b a ≤ Real.sqrt 2 * ((2 : ℝ) ^ k)⁻¹ :=
            dist_le_of_dyadicLabel_eq (hbl.trans hla.symm)
        _ ≤ 2 * ((2 : ℝ) ^ k)⁻¹ := by
          gcongr
          exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hc := Set.ncard_le_ncard hsub (hP.inter_of_left _)
    calc
      _ ≤ ((P ∩ Metric.closedBall a (2 * ((2 : ℝ) ^ k)⁻¹)).ncard : ℝ) := by
        exact_mod_cast hc
      _ ≤ C * (2 * ((2 : ℝ) ^ k)⁻¹) * P.ncard :=
        hFr _ _ (by linarith [hscale k hk])
      _ = _ := by rw [Real.rpow_one, hUcard]; ring
  have hmin : 1 ≤ (2 * C) * (((2 : ℝ) ^ J)⁻¹) ^ (1 : ℝ) * U.card := by
    obtain ⟨a, ha⟩ := hPne
    have haU : a ∈ U := by simpa only [← hU, Finset.mem_coe] using ha
    have hmem : a ∈ U.filter (fun b => dyadicLabel J b = dyadicLabel J a) := by simp [haU]
    have hn : 1 ≤ (U.filter (fun b => dyadicLabel J b = dyadicLabel J a)).card :=
      Finset.card_pos.mpr ⟨a, hmem⟩
    exact (by exact_mod_cast hn : (1 : ℝ) ≤ _).trans (hcell J le_rfl _)
  obtain ⟨V, hVU, hVmass, hVsep, hVcount⟩ := dyadic_frostman_separated_extraction
    U (fun a => a) J (by positivity : 0 < 2 * C) (by norm_num : (1 : ℝ) ≤ 1) hmin hcell
  have hVmass' : 1 / (40 * C * r) ≤ (V.card : ℝ) := by
    norm_num only [Real.rpow_one, Nat.cast_ofNat, Nat.reducePow] at hVmass
    have hden : 0 < 2 * C * ((2 : ℝ) ^ J)⁻¹ := by positivity
    have hmass := (div_le_iff₀ hden).mp hVmass
    apply (div_le_iff₀ (by positivity : 0 < 40 * C * r)).mpr
    have hm : (V.card : ℝ) * (2 * C * ((2 : ℝ) ^ J)⁻¹) ≤
        (V.card : ℝ) * (4 * C * r) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        2 * C * ((2 : ℝ) ^ J)⁻¹ ≤ 2 * C * (2 * r) :=
          mul_le_mul_of_nonneg_left hJr.le (by positivity)
        _ = 4 * C * r := by ring
    nlinarith
  have hVpos : 0 < (V.card : ℝ) := lt_of_lt_of_le (by positivity) hVmass'
  have hlocal := closed_ball_count_from_open_ball_count V hr hrJ hJr
    (by simpa only [show (2 : ℝ) * 3 ^ 2 = 18 by norm_num] using hVcount)
  refine ⟨(V : Set _), ?_, V.finite_toSet, ?_, ?_, ?_, hlocal⟩
  · intro x hx
    simpa only [← hU, Finset.mem_coe] using hVU hx
  · exact Finset.coe_nonempty.mpr (Finset.card_pos.mp (by exact_mod_cast hVpos))
  · simpa only [Set.ncard_coe_finset] using hVmass'
  · intro x hx y hy hxy
    exact hrJ.trans (hVsep x hx y hy hxy)

/-- The absolute small-ball bound also gives a normalized Frostman bound. -/
theorem planar_frostman_separated_subset_with_local_bound
    {r C : ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hr : 0 < r) (hr1 : r ≤ 1) (hC : 1 ≤ C)
    (hP : P.Finite) (hPne : P.Nonempty)
    (hFr : ∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ →
      ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ C * ρ * P.ncard) :
    ∃ Q ⊆ P, Q.Finite ∧ Q.Nonempty ∧
      1 / (40 * C * r) ≤ (Q.ncard : ℝ) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → r ≤ dist x y) ∧
      (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ →
        ((Q ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ 1440 * C * ρ * Q.ncard) ∧
      ∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ρ ≤ 1 / 2 →
        ((Q ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ 36 * ρ / r := by
  obtain ⟨Q, hQP, hQ, hQne, hmass, hsep, hlocal⟩ :=
    planar_frostman_separated_subset_core hr hr1 hC hP hPne hFr
  refine ⟨Q, hQP, hQ, hQne, hmass, hsep, ?_, hlocal⟩
  intro x ρ hρ
  have hρpos := hr.trans_le hρ
  by_cases hρhalf : ρ ≤ 1 / 2
  · have hm := (div_le_iff₀ (by positivity : 0 < 40 * C * r)).mp hmass
    have hresult : 36 * ρ / r ≤ 1440 * C * ρ * Q.ncard := by
      rw [div_le_iff₀ hr]
      calc 36 * ρ ≤ 36 * ρ * ((Q.ncard : ℝ) * (40 * C * r)) :=
          le_mul_of_one_le_right (by positivity) hm
        _ = 1440 * C * ρ * Q.ncard * r := by ring
    exact (hlocal x ρ hρ hρhalf).trans hresult
  · have hc : ((Q ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ Q.ncard := by
      exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left hQ
    have hfac : 1 ≤ 1440 * C * ρ := by
      have hρhalf' : (1 / 2 : ℝ) ≤ ρ := le_of_not_ge hρhalf
      calc (1 : ℝ) ≤ 1440 * 1 * (1 / 2 : ℝ) := by norm_num
        _ ≤ 1440 * C * ρ := by gcongr
    exact hc.trans (le_mul_of_one_le_left (Nat.cast_nonneg Q.ncard) hfac)

/-- The normalized Frostman conclusion, without the additional absolute
small-ball bound. -/
theorem planar_frostman_separated_subset
    {r C : ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hr : 0 < r) (hr1 : r ≤ 1) (hC : 1 ≤ C)
    (hP : P.Finite) (hPne : P.Nonempty)
    (hFr : ∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ →
      ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ C * ρ * P.ncard) :
    ∃ Q ⊆ P, Q.Finite ∧ Q.Nonempty ∧
      1 / (40 * C * r) ≤ (Q.ncard : ℝ) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → r ≤ dist x y) ∧
      ∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ →
        ((Q ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ 1440 * C * ρ * Q.ncard := by
  obtain ⟨Q, hQP, hQ, hQne, hmass, hsep, hfr, _⟩ :=
    planar_frostman_separated_subset_with_local_bound hr hr1 hC hP hPne hFr
  exact ⟨Q, hQP, hQ, hQne, hmass, hsep, hfr⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
