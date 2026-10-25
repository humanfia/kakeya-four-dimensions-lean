import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialPacket
import Submission.Obl.k4_physical_parent_potential_candidates.StripDeterminants
import Submission.Lib.K4ParentSignalPreparation.PolynomialBounds

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4OriginalCellSampling.Sampling
open Submission.Lib.K4ChartLifting
open PhysicalPotentialData
open scoped ENNReal

noncomputable section

def packetOrigin (T j : ℕ) (c u : P2) (l : Ln) : P3 :=
  packetBase T j c u (l, (j:ℝ)*((2:ℝ)^T)⁻¹)

def ownIntercept (T j : ℕ) (c u : P2) (P0 : Po)
    (Pot : MvPolynomial (Fin 3) ℝ) (l : Ln) : ℝ :=
  packetSignal P0 (l, (j:ℝ)*((2:ℝ)^T)⁻¹) -
    MvPolynomial.eval (fun i => packetOrigin T j c u l i) Pot

theorem measurable_packetBase (T j : ℕ) (c u : P2) :
    Measurable (packetBase T j c u) := by
  unfold packetBase xp
  fun_prop

theorem measurable_velocity : Measurable v := by
  unfold v
  fun_prop

theorem measurable_packetOrigin (T j : ℕ) (c u : P2) :
    Measurable (packetOrigin T j c u) :=
  (measurable_packetBase T j c u).comp (measurable_id.prodMk measurable_const)

theorem measurable_packetSignal (P0 : Po) : Measurable (packetSignal P0) := by
  unfold packetSignal
  exact (MvPolynomial.continuous_eval P0).measurable.comp (by unfold xp; fun_prop)

theorem measurable_ownIntercept (T j : ℕ) (c u : P2) (P0 : Po)
    (Pot : MvPolynomial (Fin 3) ℝ) : Measurable (ownIntercept T j c u P0 Pot) := by
  unfold ownIntercept
  apply Measurable.sub
  · exact (measurable_packetSignal P0).comp (measurable_id.prodMk measurable_const)
  · exact (MvPolynomial.continuous_eval Pot).measurable.comp
      (Measurable.of_eval fun i =>
        (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).measurable.comp
          (measurable_packetOrigin T j c u))

theorem packetBase_affine (T j : ℕ) (c u : P2) (e : Ev) :
    packetBase T j c u e = packetOrigin T j c u e.1 +
      ((e.2-(j:ℝ)*((2:ℝ)^T)⁻¹)/((2:ℝ)^T)⁻¹) • lift (v e.1) := by
  have hh : ((2:ℝ)^T)⁻¹ ≠ 0 := by positivity
  ext i
  fin_cases i <;>
    simp [packetBase, packetOrigin, xp, v, lift] <;> field_simp <;> ring

theorem packetOrigin_bound {T j : ℕ} {c u : P2} {K : ℝ} (hK : 1 ≤ K)
    (e : Ev)
    (ht : e.2 ∈ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹))
    (hz : ‖packetBase T j c u e‖ ≤ K) (hv : ‖v e.1‖ ≤ K) :
    ‖packetOrigin T j c u e.1‖ ≤ 3*K := by
  let s := (e.2-(j:ℝ)*((2:ℝ)^T)⁻¹)/((2:ℝ)^T)⁻¹
  have hh : 0 < ((2:ℝ)^T)⁻¹ := by positivity
  have hs0 : 0 ≤ s := div_nonneg (by linarith [ht.1]) hh.le
  have hs1 : s ≤ 1 := (div_le_one hh).mpr (by nlinarith [ht.2])
  have hsabs : |s| ≤ 1 := by rw [abs_of_nonneg hs0]; exact hs1
  have haff := packetBase_affine T j c u e
  have heq : packetOrigin T j c u e.1 = packetBase T j c u e - s • lift (v e.1) :=
    eq_sub_of_add_eq haff.symm
  rw [heq]
  calc
    _ ≤ ‖packetBase T j c u e‖ + ‖s • lift (v e.1)‖ := norm_sub_le _ _
    _ ≤ K + 1*(1+K) := add_le_add hz (by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hsabs ((norm_lift_le _).trans (by linarith [hv]))
        (norm_nonneg _) (by norm_num))
    _ ≤ _ := by linarith

theorem normalized_own_fit {a ζ X Y c : ℝ} (ha : 0 < a)
    (hfit : |(X-Y)-c| ≤ a*ζ) : |X/a-Y/a-c/a| ≤ ζ := by
  rw [← sub_div, ← sub_div, abs_div, abs_of_pos ha]
  exact (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using hfit)

def physicalPotentialLip (q : ℕ) (K : ℝ) : ℝ :=
  3 * (q:ℝ) * ((q+1)^3:ℕ) * K^(q+1)

theorem physicalPotentialLip_nonneg (q : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ physicalPotentialLip q K := by
  unfold physicalPotentialLip
  positivity

/-- The physical potential retains its h factor. Dividing by a costs h/a,
which is exactly the ratio in the physical census and fine-mesh hypotheses. -/
theorem physical_potential_lipschitz (q : ℕ) (Pot : MvPolynomial (Fin 3) ℝ)
    (hPot : Pot.totalDegree ≤ q) {K h a : ℝ} (hK : 1 ≤ K) (hh : 0 ≤ h) (ha : 0 < a)
    (hcoeff : ∀ e, |Pot.coeff e| ≤ K*h)
    (x y : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ K) (hy : ∀ i, |y i| ≤ K) :
    |MvPolynomial.eval x Pot/a - MvPolynomial.eval y Pot/a| ≤
      (physicalPotentialLip q K*h/a) * ‖x-y‖ := by
  have hc := coeffL1_le_of_coeff_le Pot hPot (K*h) hcoeff
  have he := Submission.Lib.K4ParentSignalPreparation.PolynomialBounds.abs_eval_sub_eval_le_box
    Pot hK x y hx hy
  have hs : (∑ i : Fin 3, |x i-y i|) ≤ 3*‖x-y‖ := by
    calc
      _ ≤ ∑ _i : Fin 3, ‖x-y‖ := Finset.sum_le_sum fun i _ =>
        norm_le_pi_norm (x-y) i
      _ = _ := by simp
  rw [← sub_div, abs_div, abs_of_pos ha]
  apply (div_le_iff₀ ha).mpr
  calc
    _ ≤ (q:ℝ) * (((q+1)^3:ℕ)*(K*h)) * K^q * (3*‖x-y‖) := by
      apply he.trans
      gcongr
      exact coeffL1_nonneg Pot
    _ = _ := by unfold physicalPotentialLip; field_simp; ring

theorem physical_potential_coefficient_lip (q : ℕ) (Pot : MvPolynomial (Fin 3) ℝ)
    (hPot : Pot.totalDegree ≤ q) {K h : ℝ} (hK : 1 ≤ K) (hh : 0 ≤ h)
    (hcoeff : ∀ e, |Pot.coeff e| ≤ K*h) :
    Pot.totalDegree*coeffL1 Pot*K^Pot.totalDegree ≤ physicalPotentialLip q K*h := by
  have hc := coeffL1_le_of_coeff_le Pot hPot (K*h) hcoeff
  have hb : Pot.totalDegree*coeffL1 Pot*K^Pot.totalDegree ≤
      (q:ℝ)*(((q+1)^3:ℕ)*(K*h))*K^q := by
    gcongr
    exact coeffL1_nonneg Pot
  calc
    _ ≤ (q:ℝ)*(((q+1)^3:ℕ)*(K*h))*K^q := hb
    _ ≤ 3*((q:ℝ)*(((q+1)^3:ℕ)*(K*h))*K^q) := by
      have hpos : 0 ≤ (q:ℝ)*(((q+1)^3:ℕ)*(K*h))*K^q := by positivity
      linarith
    _ = _ := by unfold physicalPotentialLip; rw [pow_succ]; ring

end

end Submission.Obl.k4_physical_parent_potential_candidates
