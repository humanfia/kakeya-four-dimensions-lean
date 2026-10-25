import Submission.Obl.k4_finite_affine_parent_sources.SourceBuildNumerators
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionPowerBudget
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionMass

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

local instance optMeasSM (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance optSingSM (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

/-- The appended native state is measurable whenever its base and signal are. -/
theorem measurable_state_code {Ω : Type} [MeasurableSpace Ω]
    {base : Ω → EuclideanSpace ℝ (Fin 3)} {signal : Ω → ℝ}
    (hb : Measurable base) (hs : Measurable signal) (mesh : ℝ) :
    Measurable (stateCode base signal mesh) := by
  apply measurable_pi_iff.mpr
  intro e
  apply Int.measurable_floor.comp
  apply Measurable.div_const
  fin_cases e
  · exact (by fun_prop : Measurable (fun x => base x 0))
  · exact (by fun_prop : Measurable (fun x => base x 1))
  · exact (by fun_prop : Measurable (fun x => base x 2))
  · exact hs

/-- A finite original history partition preserves the whole original reference mass. -/
theorem sum_reference_history_mass {Ω H : Type*} [MeasurableSpace Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H] [Fintype H]
    (μ : Measure Ω) (R : Set Ω) (endL : Ω → H) (hend : Measurable endL) :
    ∑ h, μ (R ∩ {x | endL x = h}) = μ R := by
  classical
  have hh := sum_measure_preimage_singleton (μ := μ.restrict R) Finset.univ
    (fun h _ => hend (measurableSet_singleton h))
  have hterm : ∀ h, μ (R ∩ {x | endL x = h}) = μ.restrict R (endL ⁻¹' {h}) := by
    intro h
    rw [Measure.restrict_apply (hend (measurableSet_singleton h))]
    congr 1
    ext x
    exact and_comm
  have hsum : (∑ h, μ (R ∩ {x | endL x = h})) = ∑ h, μ.restrict R (endL ⁻¹' {h}) :=
    Finset.sum_congr rfl (fun h _ => hterm h)
  exact hsum.trans (by
    simpa only [Finset.coe_univ, preimage_univ, Measure.restrict_apply_univ] using hh)

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The common original end-state cutoff leaves a positive set with at least half
of the window mass. The reference weights are kept unchanged throughout. -/
theorem sample_kept_state_mass (w₀ : Fin W) (e C : ℕ) (A : ℝ) (hA : 10000 ≤ A)
    (S1 S2 : Set Incidence) (hS2m : MeasurableSet S2) (hS21 : S2 ⊆ S1)
    (hfin : ((ν w₀).prod volume) S1 ≠ ⊤) (hpos : 0 < ((ν w₀).prod volume).real S1)
    (code : Incidence → Fin 4 → ℤ) (hcode : Measurable code)
    (wt : Option (Fin p.C) → ENNReal)
    (hwt : ∑ h, wt h ≤ ENNReal.ofReal 8 * ((ν w₀).prod volume) S1)
    (hV : ∀ h : Option (Fin p.C), ∃ V : Finset (Fin 4 → ℤ), (V.card : ℝ) ≤ 81 * A ^ (6 * C) ∧
      ∀ x ∈ S2, p.history m e (w₀, x) = h → code x ∈ V)
    (hdel : ((ν w₀).prod volume).real (S1 \ S2) ≤ ((ν w₀).prod volume).real S1 / 4) :
    let F := keptSet (((ν w₀).prod volume).restrict S2)
      (fun x => p.history m e (w₀, x)) code wt (ENNReal.ofReal ((A ^ (6 * C + 2))⁻¹))
    MeasurableSet (S2 ∩ F) ∧
      ((ν w₀).prod volume).real S1 / 2 ≤ ((ν w₀).prod volume).real (S2 ∩ F) ∧
      0 < ((ν w₀).prod volume).real (S2 ∩ F) := by
  classical
  intro F
  have hA0 : 0 < A := by linarith
  have hend : Measurable (fun x : Incidence => p.history m e (w₀, x)) :=
    (hp.measurable_history _).comp measurable_prodMk_left
  have hFm : MeasurableSet F := measurableSet_keptSet hend hcode wt _
  have hdeleted := kept_deleted_le hp w₀ e S2 hS2m code hcode wt
    (ENNReal.ofReal ((A ^ (6 * C + 2))⁻¹)) hV
  have hcoeff : ENNReal.ofReal (81 * A ^ (6 * C) * (A ^ (6 * C + 2))⁻¹ * 8) =
      ENNReal.ofReal (81 * A ^ (6 * C)) * ENNReal.ofReal ((A ^ (6 * C + 2))⁻¹) *
        ENNReal.ofReal 8 := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  have hmass : ((ν w₀).prod volume) (S2 \ F) ≤
      ENNReal.ofReal (1 / 8) * ((ν w₀).prod volume) S1 := by
    apply hdeleted.trans
    calc ENNReal.ofReal (81 * A ^ (6 * C)) * ENNReal.ofReal ((A ^ (6 * C + 2))⁻¹) * ∑ h, wt h
        ≤ ENNReal.ofReal (81 * A ^ (6 * C)) * ENNReal.ofReal ((A ^ (6 * C + 2))⁻¹) *
          (ENNReal.ofReal 8 * ((ν w₀).prod volume) S1) := by gcongr
      _ = ENNReal.ofReal (81 * A ^ (6 * C) * (A ^ (6 * C + 2))⁻¹ * 8) *
          ((ν w₀).prod volume) S1 := by
            rw [hcoeff]
            ring
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (kept_state_power_loss hA C)) le_rfl
  have hdel2 : ((ν w₀).prod volume).real (S2 \ F) ≤ ((ν w₀).prod volume).real S1 / 4 := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hmass
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 8)] at h
    change ((ν w₀).prod volume).real (S2 \ F) ≤ (1 / 8) * ((ν w₀).prod volume).real S1 at h
    linarith
  exact ⟨hS2m.inter hFm, source_two_deletions _ hS21 hS2m hFm hfin hpos hdel hdel2⟩

end Path

end

end Submission.Obl.k4_finite_affine_parent_sources
