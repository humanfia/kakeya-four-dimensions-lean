import Submission.Obl.k4_matching_abstract_switching_mixture.CoverTransfer
import Submission.Obl.k4_matching_abstract_switching_mixture.Start
import Submission.Obl.k4_matching_abstract_switching_mixture.Parameters

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open MeasureTheory Finset
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

set_option linter.unusedVariables false

namespace Data

variable {n₁ n₂ : ℕ} (D : Data n₁ n₂)

/-- The finite representative experiment realizes one of the supplied covers. -/
theorem exists_endpoint (m : ℕ) {N K δ V θ : ℝ} (hN : 0 < N)
    (hB : 1 ≤ D.B) (hK : 2 ≤ K) (hδ : 0 < δ)
    (hbad : D.μ {x | x ∈ D.S ∧ N ^ θ * D.post D.F₀ x < D.post D.F₁ x} ≤
      ENNReal.ofReal (smallError m))
    (hcovers : ∀ a ∈ D.S, Nonempty (EventCover D m K δ V a)) :
    ∃ (U : Fin (m + 1) → ℝ) (s₀ : ℝ) (T : Set (ℝ × (Fin m → ℝ))),
      (∀ p, |U p| ≤ K) ∧ |s₀| ≤ 1 ∧
      (∀ p : Fin m, K⁻¹ ≤ |U p.succ - U p.castSucc|) ∧
      MeasurableSet T ∧ volume T ≤ ENNReal.ofReal (K * V) ∧
      1 / 2 ≤ (Real.exp (θ * Real.log N) * (D.B / smallError m) * (2 * K)) ^ (m + 1) *
        (volume (pullback (sizeBound m D.B K) U s₀ T)).toReal := by
  classical
  let ε := smallError m
  let rt := timeRadius m D.B
  have hε : 0 < ε := smallError_pos m
  have hB0 : 0 < D.B := by linarith
  have hrt : 0 < rt := timeRadius_pos m hB0
  obtain ⟨G, hG, hmesh⟩ := exists_fine_depth D.H D.H'
    (lt_min hδ (div_pos hrt (by norm_num : (0 : ℝ) < 4)))
  have hHG : D.H ≤ G := D.hHH'.trans hG
  let d : ℝ := (2 : ℝ) ^ D.H / (2 : ℝ) ^ G
  have hd : 0 < d := by dsimp [d]; positivity
  have hdδ : d ≤ δ := hmesh.trans (min_le_left _ _)
  have hdrt : d ≤ rt / 4 := hmesh.trans (min_le_right _ _)
  have hdrt' : d ≤ rt := by linarith
  let lam : ℝ := ε / (2 : ℝ) ^ D.H
  have hlam : 0 < lam := by dsimp [lam]; positivity
  let ψ₀ : ℤ × ℤ → ℕ → Bool → ℝ := fun _ _ _ => 0
  let X₀ := D.sw G ψ₀ (θ * Real.log N)
  have hbadreal : (D.μ {x | x ∈ D.S ∧ N ^ θ * D.post D.F₀ x < D.post D.F₁ x}).toReal ≤ ε := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
    simpa only [ENNReal.toReal_ofReal (smallError_pos m).le] using h
  have hbad₀ : ∑ e, X₀.P e * (if X₀.good e then (0 : ℝ) else 1) ≤ ε :=
    (D.sw_bad_le ψ₀ hG hN).trans hbadreal
  have hlight₀ : ∀ c, ∑ e, X₀.P e * (if X₀.heavy D.prior lam e c then (0 : ℝ) else 1) ≤ ε := by
    intro c
    have h := D.sw_light_le G ψ₀ (θ * Real.log N) lam hlam.le c
    have heq : (2 : ℝ) ^ D.H * lam = ε := by dsimp [lam]; field_simp
    exact h.trans_eq heq
  obtain ⟨a, ha, hfail₀⟩ := exists_start_of_small_kills X₀
    (D.sw_P_nonneg G ψ₀ _) (D.sw_sum_P G ψ₀ _) D.prior lam ε hε.le m
    hbad₀ hlight₀ (smallError_loss m)
  let C : EventCover D m K δ V (D.rep G a) := Classical.choice (hcovers _ (D.rep_mem G a))
  let ψ : ℤ × ℤ → ℕ → Bool → ℝ := fun z f c => C.C f z c
  let X := D.sw G ψ (θ * Real.log N)
  let pc : PathCover X (D.sTime G a) m K δ V a :=
    C.lift (D.rep G) (D.rep_mem G) X (fun _ => rfl)
      (fun e er c e' h => ⟨h.1, D.rep_of_armKey_eq G ψ (θ * Real.log N) h.2⟩)
      a (fun _ _ => rfl)
  obtain ⟨g, hg⟩ := D.sw_coarse G ψ (θ * Real.log N)
  have hfail : X.failBound D.prior lam ε (m + 1) a ≤ 1 / 2 := by
    have heq : X.failBound D.prior lam ε (m + 1) a = X₀.failBound D.prior lam ε (m + 1) a :=
      failBound_with_controls X₀ ψ D.prior lam ε (m + 1) a
    exact heq.trans_le hfail₀
  have hcell : ∀ c arm cell,
      fiberMass X.P (fun e => (X.arm e c, X.cell e)) (arm, cell) ≤
        D.prior c arm * (lam * (D.B / ε) * d) := by
    intro c arm cell
    have heq : lam * (D.B / ε) * d = D.B / (2 : ℝ) ^ G := by
      dsimp [lam, d]
      field_simp
    rw [heq]
    exact D.sw_cell G ψ (θ * Real.log N) c arm cell
  let v : ℝ := (2 * D.B * (rt / (2 : ℝ) ^ D.H + 1 / (2 : ℝ) ^ G)) / lam
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hvbudget : ((m : ℝ) + 1) * v ≤ ε := by
    have heq : v = 2 * D.B * (rt + d) / ε := by
      dsimp [v, lam, d]
      field_simp
      <;> ring
    rw [heq]
    exact near_budget m hB0 hdrt'
  have hnear : ∀ er c, X.heavy D.prior lam er c → ∀ t₀ : ℝ,
      ∑ e, condKey X.P (X.armKey c) er e *
        (if |D.ntime G e - t₀| < rt then (1 : ℝ) else 0) ≤ v := by
    intro er c hheavy t₀
    exact condKey_pred_le X (D.sw_P_nonneg G ψ _) c er
      (fun e => |D.ntime G e - t₀| < rt) hlam (by positivity) hheavy
      (D.sw_near_le G ψ (θ * Real.log N) c er t₀ rt hrt.le)
  have hsep : ∀ n path er c, path.length + n + 1 ≤ m + 1 → X.heavy D.prior lam er c →
      ∑ e, condKey X.P (X.armKey c) er e *
        (if separatedArrival (D.ntime G) rt n path e then (0 : ℝ) else 1) ≤ ε := by
    intro n path er c hlen hheavy
    have h := separatedArrival_failure_le X (D.sw_P_nonneg G ψ _) (D.ntime G) rt
      c er path n hv (fun q _ => hnear er c hheavy (D.ntime G q.2.2))
    have hlength : (path.length : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast (by omega : path.length ≤ m + 1)
    exact h.trans ((mul_le_mul_of_nonneg_right hlength hv).trans hvbudget)
  obtain ⟨U, hU, hgap, hvol⟩ := pc.exists_control (by linarith)
    (D.sw_P_nonneg G ψ _) ha hg
    (fun x y h => D.ival_eq_of_fine_eq G ψ (θ * Real.log N) h)
    D.prior hlam (by positivity) hε.le hcell hfail hsep
    (D.normCells G a) (D.measurableSet_normCells G a) (D.normCells_disjoint G a) hd
    (D.volume_normCells G a) (D.sTime_sub G a)
    (fun e he hi y hy => D.normCells_unit hHG a he hi hy)
    (fun e he y hy => D.normCells_close G a he hy)
    hdδ (mesh_margin m hB hK hdrt)
  exact ⟨U, D.sTime G a a, C.T, hU, C.start_bound, hgap, C.measurable, C.volume_bound, hvol⟩

end Data

end Submission.Obl.k4_matching_abstract_switching_mixture
