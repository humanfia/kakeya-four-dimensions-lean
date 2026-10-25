import Submission.Obl.k4_horizontal_three_traversal_spreading.Geometry
import Submission.Obl.k4_horizontal_three_traversal_spreading.Palette

namespace Submission.Obl.k4_horizontal_three_traversal_spreading

open Set MeasureTheory Finset
open Discretize Inherited
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

noncomputable section

/-- A scale-explicit form of the three-traversal spreading estimate. -/
theorem quantitative_spreading :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : Type) [MeasurableSpace α] (D : Law α), D.Valid →
      ∀ K V : ℝ, 2 ≤ K → 1 ≤ D.L → 0 ≤ V → D.B + D.h ≤ K → D.h ≤ K⁻¹ →
      600 * K ^ 3 * D.h ≤ D.ω / 2 → D.L * V + 144 * D.L / K ≤ 1 / 9 →
      (∀ v : ℝ, D.π (Icc (v - 2 / K) (v + 2 / K)) ≤ ENNReal.ofReal V) →
      ∃ j : ℤ, 1 / (C * K ^ 24 * D.L ^ 6 * (D.F.card : ℝ) * D.ω ^ 3) ≤
        (D.σ {p | D.bin p.1 = j}).toReal := by
  classical
  obtain ⟨C, hC, hfinite⟩ := finite_critical_heavy_intercept_uniform
  refine ⟨8 * 36 ^ 3 * C, by positivity, ?_⟩
  intro α _ D hD K V hK hL hV hBK hfine hgeom hloss hpal
  letI := hD.prob_σ
  letI := hD.prob_π
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hL0 : 0 < D.L := by linarith
  have hh : 0 ≤ D.h := hD.h_pos.le
  have hω0 : 0 < D.ω := hD.ω_pos
  have hω : 0 ≤ D.ω := hω0.le
  obtain ⟨n, hn⟩ := D.exists_state_truncation hD
  have hMhalf := D.mass_half hD hn
  have hM : 0 < D.mass n := by linarith
  obtain ⟨t, ht⟩ := exists_nat_one_div_lt
    (lt_min hD.h_pos (inv_pos.mpr (show 0 < 4 * K by positivity)))
  let T : ℕ := t + 1
  have hT : 0 < T := Nat.succ_pos t
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hd : (0 : ℝ) < 1 / T := by positivity
  have hdt : 1 / (T : ℝ) ≤ D.h := by
    simpa only [T, Nat.cast_add, Nat.cast_one] using (lt_of_lt_of_le ht (min_le_left _ _)).le
  have hdt4 : 1 / (T : ℝ) ≤ (4 * K)⁻¹ := by
    simpa only [T, Nat.cast_add, Nat.cast_one] using (lt_of_lt_of_le ht (min_le_right _ _)).le
  have hdtK : 1 / (T : ℝ) ≤ K⁻¹ := hdt4.trans
    ((inv_le_inv₀ (by positivity) hK0).mpr (by linarith))
  have hmargin : (2 * K)⁻¹ + 2 * (1 / (T : ℝ)) ≤ K⁻¹ := by
    calc
      _ ≤ (2 * K)⁻¹ + 2 * (4 * K)⁻¹ := by gcongr
      _ = K⁻¹ := by field_simp; ring
  have hbudget : 5 * D.h + 2 * K * (1 / (T : ℝ)) + 6 * K * D.h ≤ 13 * K * D.h := by
    have hmul := mul_le_mul_of_nonneg_left hdt (show 0 ≤ 2 * K by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hK1) hh]
  have hpred : criticalPredictionError K (13 * K * D.h) 3 ≤ 600 * K ^ 3 * D.h := by
    rw [criticalPredictionError_three]
    have hKsq : K ≤ K ^ 2 := by nlinarith
    have hcoef : 1 + 6 * K + 36 * K ^ 2 ≤ 43 * K ^ 2 := by nlinarith
    calc
      _ ≤ (43 * K ^ 2) * (13 * K * D.h) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = 559 * K ^ 3 * D.h := by ring
      _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg hK0.le 3) hh]
  have herror : criticalPredictionError K (13 * K * D.h) 3 + D.ω / 2 ≤ D.ω := by
    linarith
  have hjitter : 20 * K ^ 2 * (1 / (T : ℝ)) ≤ D.ω := by
    calc
      _ ≤ 20 * K ^ 2 * D.h := mul_le_mul_of_nonneg_left hdt (by positivity)
      _ ≤ 600 * K ^ 3 * D.h := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hK1) (mul_nonneg (sq_nonneg K) hh)]
      _ ≤ D.ω / 2 := hgeom
      _ ≤ D.ω := by linarith
  let X := D.switch n T
  have hP := D.switch_nonneg hM (T := T)
  have hP1 := D.switch_sum hD hT hM
  have hheavy : (∑ e, X.P e * (if X.heavy (fun _ => D.prior) (1 / 18) e false then 0 else 1)) ≤
      1 / 18 := by
    have h := Submission.Obl.k4_matching_abstract_switching_mixture.sum_light_le X hP
      (fun _ => D.prior) (fun _ _ => ENNReal.toReal_nonneg) (1 / 18) (by norm_num) false
    simp only [Fintype.card_unique, Nat.cast_one, one_mul] at h
    exact h.trans (by have hs := D.sum_prior_le hD; linarith)
  have hsurvive : D.L * V + 2 * (2 * D.L) * (K⁻¹ + 1 / (T : ℝ)) / (1 / 18) + 1 / 18 ≤ 1 / 6 := by
    have hm := mul_le_mul_of_nonneg_left hdtK (show 0 ≤ 72 * D.L by positivity)
    rw [div_eq_mul_inv (144 * D.L) K] at hloss
    nlinarith
  have hFpos : 0 < (D.F.card : ℝ) := by
    obtain ⟨p, hp⟩ := hD.support.exists
    exact_mod_cast Finset.card_pos.mpr ⟨_, hp⟩
  let geom := D.finiteGeometry hD hT hM hBK
  obtain ⟨j, hj⟩ := hfinite (D.Event n T) (Fin n × ℤ) Unit D.armSet Unit D.palSet
    (Fin T) ℤ (Fin 3 → ℤ) X hP hP1 (fun _ => D.prior) (fun z => D.palMass z.val)
    D.velocity Law.timeInterval Law.center (1 / T) (1 / T) D.h K (5 * D.h)
    (13 * K * D.h) (D.ω / 2) D.ω D.L (2 * D.L) (1 / 18) V (1 / 18) D.F.card
    hd hd.le hh hK (by positivity) (by positivity) hbudget hD.ω_pos herror
    hL0 (by positivity) (by norm_num) hV hFpos
    (fun _ => ENNReal.toReal_nonneg) (D.palette_sum_le_one hD)
    (fun _ => measurableSet_Ico) (Law.timeInterval_disjoint hT)
    (Law.timeInterval_volume hT) (Law.timeInterval_unit hT) (Law.timeInterval_near hT)
    hmargin hjitter (D.switch_cell hD hT hMhalf) (D.switch_palette hD hT hM)
    (D.palette_interval hD hK0 hfine hV hpal) hheavy hsurvive geom
    (fun e => D.binOf e.2.1) (D.pointCell hD) (cellCenter D.ω)
    (fun e er hf => congrArg Prod.snd hf)
    (fun er e' harm => congrArg D.binOf (congrArg (fun k : D.armSet × Unit => k.1) harm))
    D.F le_rfl (fun e he => D.point_support hD (D.switch_pos_weight hM he))
    (fun e _ => D.point_spatial hD e)
  have hsum : (∑ e ∈ Finset.univ.filter (fun e : D.Event n T => D.binOf e.2.1 = j), X.P e) =
      (∑ e ∈ Finset.univ.filter (fun e : D.Event n T => D.binOf e.2.1 = j), D.weight e) / D.mass n := by
    exact (Finset.sum_div _ _ _).symm
  rw [hsum] at hj
  have hbin := D.sum_weight_test_le hD
    (fun e : D.Event n T => D.binOf e.2.1 = j) (fun p => D.bin p.1 = j)
    (fun e p he hp => (D.pre_bin hp).trans he)
  have hden : 0 < 4 * C * K ^ 24 * D.ω ^ 3 * (D.L * (2 * D.L) / (1 / 18)) ^ 3 * D.F.card := by
    positivity
  have hmul := (le_div_iff₀ hM).mp hj
  have hhalf := mul_le_mul_of_nonneg_left hMhalf (one_div_pos.mpr hden).le
  have hfinal := hhalf.trans (hmul.trans hbin)
  refine ⟨j, ?_⟩
  convert hfinal using 1
  field_simp [hC.ne', hK0.ne', hL0.ne', hFpos.ne', hD.ω_pos.ne']
  ring

end
end Submission.Obl.k4_horizontal_three_traversal_spreading
