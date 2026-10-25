/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, FrozenSupportInputs.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.FullLabelCount
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.OriginalMass

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The native pure joint cap at hidden scale one, in the actual frozen
coordinates and the original source law. -/
theorem Valid.eventually_native_pure_joint_cap (h : cfg.Valid)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ k in atTop, ∀ (q : Fin 3 → ℤ) (n : ℤ),
      cfg.μ k {p | baseGridCode (cfg.N k ^ (-r))
        (![p.2, cfg.b k p.1 0 + p.2 * cfg.b k p.1 3,
          cfg.b k p.1 1 + p.2 * cfg.b k p.1 4] : Fin 3 → ℝ) = q ∧
          ⌊cfg.b k p.1 2 + p.2 * cfg.b k p.1 5⌋ = n} ≤
        ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-r)) ^ 3) := by
  let R := 2 + r + r⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hr]
  have hRpos : 0 < R := by linarith
  have hrR : r ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr]
  have hRr : R⁻¹ ≤ r := by
    apply (inv_le_comm₀ hRpos hr).mpr
    dsimp [R]
    linarith
  filter_upwards [h.caps R hR] with k hk
  intro q n
  have hn : 0 < cfg.N k := by linarith [h.scale k]
  have hh := (hk r 0 r hRr hrR le_rfl (by linarith) hRr hrR).2.1 false q n
  have hscale : cfg.N k ^ (-3 * r - cfg.d * 0) = (cfg.N k ^ (-r)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    ring
  rw [hscale] at hh
  have hzeq : cfg.z k (cfg.N k) r = fun (p : α × ℝ) =>
      baseGridCode (cfg.N k ^ (-r))
        (![p.2, cfg.b k p.1 0 + p.2 * cfg.b k p.1 3,
          cfg.b k p.1 1 + p.2 * cfg.b k p.1 4] : Fin 3 → ℝ) := rfl
  rw [hzeq] at hh
  simpa [Data.x] using hh

/-- Each fitted true label still has an original full incidence witness of
fourth-power size. The current residual need not retain this floor. -/
theorem Valid.eventually_full_label_mass_floor (h : cfg.Valid)
    (s : ℝ) (hs : 0 < s) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, ∀ i : Fin (cfg.n k s), MeasurableSet (cfg.B k s i) ∧
      ENNReal.ofReal (cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 3) ≤
        cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) := by
  let R := 2 + s⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hs]
  have hRs : R⁻¹ ≤ s := by
    apply (inv_le_comm₀ (by linarith : 0 < R) hs).mpr
    dsimp [R]
    linarith
  filter_upwards [h.eventually_assignment_level hs hsU, h.atlas R hR] with k lev hatlas
  have hk := hatlas s hRs hsU
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hn : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hH : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  intro i
  refine ⟨(hk.2.2.1 i).2.1, ?_⟩
  have hmu : ENNReal.ofReal (cfg.timeLength k s / cfg.K k) * cfg.ν k (cfg.A k s i) ≤
      cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) := by
    simpa only [timeLength, zpow_neg, zpow_natCast] using (hk.2.2.2.2.1 i).2.2.1
  have hprior : ENNReal.ofReal
      (cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2) ≤
      cfg.ν k (cfg.A k s i) := by
    have hh := ENNReal.ofReal_le_ofReal (lev.critical_prior_bounds h i).1
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top (cfg.ν k) _)] using hh
  calc
    _ = ENNReal.ofReal (cfg.timeLength k s / cfg.K k) * ENNReal.ofReal
        (cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ cfg.timeLength k s / cfg.K k)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal (cfg.timeLength k s / cfg.K k) * cfg.ν k (cfg.A k s i) :=
      mul_le_mul_of_nonneg_left hprior zero_le
    _ ≤ _ := hmu

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
