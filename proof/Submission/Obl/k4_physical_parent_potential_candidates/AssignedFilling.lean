import Submission.Obl.k4_physical_parent_potential_candidates.BaseFilling
import Submission.Obl.k4_physical_parent_potential_candidates.StripDeterminants
import Submission.Obl.k4_physical_parent_potential_candidates.InterceptCells

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory
open Submission.Lib.K4ContinuousKakeya
open Submission.Lib.K4OriginalCellSampling.Sampling
open scoped NNReal ENNReal

noncomputable section

def assignedBaseCode {Ω : Type*} (ε p : ℝ)
    (z : Ω → EuclideanSpace ℝ (Fin 3)) (e : Ω) : Fin 3 → ℤ :=
  stateAssignedBase ε p ((fun i => ⌊z e i / ε⌋), 0)

def assignedProxy {Ω : Type*} (ε p : ℝ)
    (z : Ω → EuclideanSpace ℝ (Fin 3)) (e : Ω) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => (assignedBaseCode ε p z e i : ℝ))

theorem measurable_assignedProxy {Ω : Type*} [MeasurableSpace Ω]
    (ε p : ℝ) (z : Ω → EuclideanSpace ℝ (Fin 3)) (hz : Measurable z) :
    Measurable (assignedProxy ε p z) := by
  unfold assignedProxy assignedBaseCode stateAssignedBase
  fun_prop

theorem assignedProxy_mem_cell {Ω : Type*} (ε p : ℝ)
    (z : Ω → EuclideanSpace ℝ (Fin 3)) (e : Ω) (k : Fin 3 → ℤ) :
    assignedProxy ε p z e ∈ assignedUnitCell k ↔ assignedBaseCode ε p z e = k := by
  change (fun i => ⌊(assignedProxy ε p z e i) / 1⌋) = k ↔ _
  simp only [assignedProxy, PiLp.toLp_apply, div_one, Int.floor_intCast]

theorem lift_eq_norm_smul_unitLift (v : EuclideanSpace ℝ (Fin 2)) :
    lift v = ‖lift v‖ • unitLift v := by
  have hpos : 0 < ‖lift v‖ := lt_of_lt_of_le one_pos (one_le_norm_lift v)
  rw [unitLift, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- Whole fine states are assigned to coarse base cells before applying MK3.
The rounded position is used only to label cells; tubes follow the actual base lines. -/
theorem assigned_original_filling
    {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A : Set Λ) (hA : MeasurableSet A)
    (h t0 ε p K δ C : ℝ) (hh : 0 < h) (hε : 0 < ε) (hp : 0 < p) (hεp : ε ≤ p)
    (hK : 0 ≤ K) (hδ : 0 < δ) (hC : 0 ≤ C) (hMK : FiniteMK 3 C)
    (base : Λ → EuclideanSpace ℝ (Fin 3))
    (velocity : Λ → EuclideanSpace ℝ (Fin 2))
    (hbase : Measurable base) (hvelocity : Measurable velocity)
    (B : ℝ) (hB : 0 ≤ B) (hbaseB : ∀ l ∈ A, ‖base l‖ ≤ B)
    (hvel : ∀ l ∈ A, ‖velocity l‖ ≤ K)
    (z : (Λ × ℝ) → EuclideanSpace ℝ (Fin 3)) (hz : Measurable z)
    (hfirst : ∀ e, z e 0 = (e.2-t0)/h)
    (haffine : ∀ e, z e = base e.1 + ((e.2-t0)/h) • lift (velocity e.1))
    (G : Set (Λ × ℝ)) (hG : MeasurableSet G)
    (hGA : G ⊆ A ×ˢ Icc t0 (t0+h))
    {m : ℕ} (code : Fin m → Fin 3 → ℤ) (hcode : Function.Injective code)
    (hcover : ∀ e ∈ G, assignedBaseCode ε p z e ∈ Set.range code)
    (R : ℝ) (hball : ∀ i, assignedUnitCell (code i) ⊆ Metric.closedBall 0 R)
    (hstrip : ∀ i (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ), ‖n‖ = 1 →
      (((ν.prod volume).restrict G).restrict
        {e | e.1 ∈ A ∧ assignedBaseCode ε p z e = code i})
        {e | |inner ℝ n (velocity e.1)-t| ≤ δ} ≤
        (1/1000 : ENNReal) * ((ν.prod volume).restrict G)
          {e | e.1 ∈ A ∧ assignedBaseCode ε p z e = code i}) :
    (δ ^ 2 / (1 + K) ^ 3 / 8) * (((ν.prod volume).restrict G).real univ) ^ 3 ≤
      (m : ℝ) * (1000*C) ^ 2 * (2*h*p) ^ 3 * (ν.real A) ^ 3 := by
  classical
  let inc := (ν.prod volume).restrict G
  have hincfin : inc univ < ⊤ := by
    simp only [inc, Measure.restrict_apply_univ]
    apply lt_of_le_of_lt (measure_mono hGA)
    rw [Measure.prod_prod, Real.volume_Icc, add_sub_cancel_left]
    exact ENNReal.mul_lt_top (measure_lt_top ν A) ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure inc := ⟨hincfin⟩
  let Φ := assignedProxy ε p z
  have hΦ : Measurable Φ := measurable_assignedProxy ε p z hz
  let E (i : Fin m) := assignedUnitCell (code i)
  have hEm (i : Fin m) : MeasurableSet (E i) := measurableSet_assignedUnitCell _
  have hdisj : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
    assignedUnitCell_disjoint (fun hc => hij (hcode hc))
  let S (i : Fin m) : Set (Λ × ℝ) := {e | e.1 ∈ A ∧ Φ e ∈ E i}
  have hSm (i : Fin m) : MeasurableSet (S i) :=
    (hA.preimage measurable_fst).inter (hΦ (hEm i))
  have hSeq (i : Fin m) : S i = {e | e.1 ∈ A ∧ assignedBaseCode ε p z e = code i} := by
    ext e
    simp only [S, Φ, E, mem_setOf_eq, assignedProxy_mem_cell]
  let D : ℝ≥0 := ⟨2*h*p, by positivity⟩
  have hD : 0 < D := by change (0:ℝ) < 2*h*p; positivity
  have hpush (i : Fin m) :
      (inc.restrict (S i)).map Prod.fst ≤ D • ν.restrict A := by
    have hdom : inc ≤ (1 : ℝ≥0) • ν.prod volume := by
      simpa only [one_smul] using (Measure.restrict_le_self : inc ≤ ν.prod volume)
    have hsection (l : Λ) (hl : l ∈ A) :
        volume {t | (l,t) ∈ S i} ≤ (D : ENNReal) := by
      rw [show (D : ENNReal) = ENNReal.ofReal (2*h*p) by
        exact (ENNReal.ofReal_coe_nnreal (p := D)).symm]
      apply volume_state_assigned_time_section_le hh hε hp hεp t0 (code i 0)
      intro t ht
      have hcod := congrFun ((assignedProxy_mem_cell ε p z (l,t) (code i)).mp ht.2) 0
      change (⌊(ε*(⌊z (l,t) 0/ε⌋ : ℝ))/p⌋ : ℤ) = code i 0 at hcod
      simpa only [hfirst] using hcod
    simpa only [one_mul] using map_fst_restrict_le ν inc 1 D hdom (S i) (hSm i)
      A hA (fun e he => he.1) hsection
  let a (l : Λ) : EuclideanSpace ℝ (Fin 3) := if l ∈ A then p⁻¹ • base l else 0
  have ha : Measurable a :=
    (show Measurable (fun l => p⁻¹ • base l) by fun_prop).piecewise hA measurable_const
  have hanchor (l : Λ) : ‖a l‖ ≤ p⁻¹*B := by
    dsimp [a]
    split_ifs with hl
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
      exact mul_le_mul_of_nonneg_left (hbaseB l hl) (by positivity)
    · simpa only [norm_zero] using mul_nonneg (inv_nonneg.mpr hp.le) hB
  have htube (i : Fin m) (e : Λ × ℝ) (he : e.1 ∈ A) (hei : Φ e ∈ E i)
      (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ E i) :
      x ∈ tube 5 (a e.1) (unitLift (velocity e.1)) := by
    have hcod := (assignedProxy_mem_cell ε p z e (code i)).mp hei
    have hdist := assignedUnitCell_dist_le hε hp hεp (z e) 0 (code i) hcod x hx
    have hline : p⁻¹ • z e ∈
        Set.range (fun s : ℝ => a e.1 + s • unitLift (velocity e.1)) := by
      refine ⟨(p⁻¹*((e.2-t0)/h))*‖lift (velocity e.1)‖, ?_⟩
      rw [show a e.1 = p⁻¹ • base e.1 by simp only [a, if_pos he], haffine e]
      conv_rhs => rw [lift_eq_norm_smul_unitLift (velocity e.1)]
      module
    exact Metric.mem_thickening_iff.mpr ⟨p⁻¹ • z e, hline, hdist.trans_lt (by norm_num)⟩
  have hsuccess (i : Fin m) :
      ENNReal.ofReal (((1/2:ℝ)*inc.real (S i))^3) ≤
        Measure.pi (fun _ : Fin 3 => inc)
          {e | (∀ k, (e k).1 ∈ A ∧ Φ (e k) ∈ E i) ∧
            δ^2/(1+K)^3 ≤ |(Matrix.of fun k j : Fin 3 => unitLift (velocity (e k).1) j).det|} := by
    have hs := unit_determinant_mass_in_cell inc (S i) (hSm i)
      (fun e => velocity e.1) (hvelocity.comp measurable_fst) hδ hK
      (fun e he => hvel e.1 he.1) (1/1000) le_rfl
      (by simpa only [hSeq i] using hstrip i)
    exact hs
  have hfill := base_incidence_filling_of_determinant_mass ν inc Φ hΦ
    a (fun l => unitLift (velocity l)) ha (measurable_unitLift.comp hvelocity)
    (fun l => norm_unitLift _) (p⁻¹*B) hanchor A hA E hEm hdisj R hball
    1 5 C (δ^2/(1+K)^3) (1/2) (by norm_num) (by norm_num) hC hMK
    (by positivity) (by norm_num) D hD
    (fun i => by simp only [E, volume_assignedUnitCell]; norm_num)
    hpush (by simpa only [mul_one] using htube) hsuccess
  have hGcover : G ⊆ ⋃ i, S i := by
    intro e he
    obtain ⟨i, hi⟩ := hcover e he
    exact mem_iUnion.mpr ⟨i, (hGA he).1, (assignedProxy_mem_cell ε p z e (code i)).mpr hi.symm⟩
  have hunion : (⋃ i, S i) ∩ G = G := inter_eq_right.mpr hGcover
  have hmass : inc univ = ∑ i, inc (S i) := by
    calc
      _ = inc (⋃ i, S i) := by
        dsimp only [inc]
        simp only [Measure.restrict_apply' hG, univ_inter, hunion]
      _ = _ := by
        rw [measure_iUnion]
        · exact tsum_fintype _
        · intro i j hij
          exact ((hdisj hij).preimage Φ).mono
            (fun e he => he.2) (fun e he => he.2)
        · exact hSm
  have hreal : ∑ i, inc.real (S i) = inc.real univ := by
    rw [measureReal_def, hmass, ENNReal.toReal_sum (fun _ _ => measure_ne_top inc _)]
    rfl
  rw [hreal] at hfill
  change δ^2/(1+K)^3*(1/2:ℝ)^3*inc.real univ^3 ≤
    (m:ℝ)*(8*C*5^3)^2*(2*h*p)^3*(ν.real A)^3 at hfill
  have hincReal : inc.real univ = (ν.prod volume).real G := by
    simp only [inc, measureReal_def, Measure.restrict_apply_univ]
  rw [hincReal] at hfill
  simp only [measureReal_def, Measure.restrict_apply_univ] at hfill ⊢
  convert hfill using 1 <;> ring

end

end Submission.Obl.k4_physical_parent_potential_candidates
