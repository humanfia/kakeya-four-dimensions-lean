import Submission.Obl.k4_marked_scalar_grid_selection.VaryingSelection
import Submission.Obl.k4_tempered_grid_selection.Exponents
import Submission.Lib.K4Homogenization.ProfileCompactness

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter Set
open scoped ENNReal Topology

/-- A finite weighted table, considered as a measure on its labels. -/
noncomputable def finiteLabelLaw {C : ℕ} (w : Fin C → ENNReal) : Measure (Fin C) :=
  Measure.sum fun b => w b • Measure.dirac b

theorem finiteLabelLaw_apply {C : ℕ} (w : Fin C → ENNReal) (T : Set (Fin C))
    [DecidablePred (fun b => b ∈ T)] :
    finiteLabelLaw w T = ∑ b ∈ Finset.univ.filter (fun b => b ∈ T), w b := by
  classical
  rw [finiteLabelLaw, Measure.sum_apply_of_countable, tsum_fintype]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b ∈ T <;> simp [hb]

/-- Select whole labels so their polynomially bounded positive ratios have
one common limiting logarithmic exponent, losing only a subpower of the mass. -/
theorem select_finite_ratios
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (C : ℕ → ℕ) (w : (k : ℕ) → Fin (C k) → ENNReal)
    (ratio : (k : ℕ) → Fin (C k) → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hratio : ∀ k b, N k ^ (-A) ≤ ratio k b ∧ ratio k b ≤ N k ^ A) :
    ∃ (ψ : ℕ → ℕ) (S : (k : ℕ) → Finset (Fin (C (ψ k))))
      (loss : ℕ → ℝ) (α : ℝ), StrictMono ψ ∧
      Submission.Obl.k4_tempered_grid_selection.Subpower (N ∘ ψ) loss ∧
      (∀ k, (∑ b, w (ψ k) b) ≤ ENNReal.ofReal (loss k) *
        ∑ b ∈ S k, w (ψ k) b) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b ∈ S k,
        N (ψ k) ^ (α - ε) ≤ ratio (ψ k) b ∧
          ratio (ψ k) b ≤ N (ψ k) ^ (α + ε) := by
  classical
  let f (k : ℕ) (_j : ℕ) (b : Fin (C k)) : ℝ :=
    Submission.Obl.k4_tempered_grid_selection.boundedExponent A (N k) (ratio k b)
  obtain ⟨B, T, a, δ, hB, hBsub, ha, hδpos, hδ, hfit, hmass⟩ :=
    Submission.Obl.k4_marked_scalar_grid_selection.countable_type_selection_varying
      N hN hNt (fun k => finiteLabelLaw (w k)) f A hA
      (fun k j b => Submission.Obl.k4_tempered_grid_selection.abs_boundedExponent
        _ _ _ hA)
  obtain ⟨z, ψ, hψ, hz, _⟩ := Submission.Lib.K4Homogenization.bounded_profile_subsequence
    (fun k (_ : Unit) => a k 0) A (fun k _ => ha k 0)
  let S (k : ℕ) : Finset (Fin (C (ψ k))) := Finset.univ.filter (fun b => b ∈ T (ψ k))
  refine ⟨ψ, S, (fun k => (B (ψ k) : ℝ)), -z (), hψ, ?_, ?_, ?_⟩
  · exact ⟨fun k => hBsub.1 (ψ k),
      fun ε hε => hψ.tendsto_atTop.eventually (hBsub.2 ε hε)⟩
  · intro k
    have h := hmass (ψ k)
    rw [finiteLabelLaw_apply, finiteLabelLaw_apply] at h
    simpa only [mem_univ, Finset.filter_true, S, ENNReal.ofReal_natCast] using h
  · intro ε hε
    have hδ' : ∀ᶠ k in atTop, δ (ψ k) < ε / 2 :=
      (hδ.comp hψ.tendsto_atTop).eventually (gt_mem_nhds (half_pos hε))
    have ha' : ∀ᶠ k in atTop, |a (ψ k) 0 - z ()| < ε / 2 := by
      simpa only [Real.dist_eq] using (hz ()).eventually
        (Metric.ball_mem_nhds (z ()) (half_pos hε))
    filter_upwards [hψ.tendsto_atTop.eventually (hfit 0), hδ', ha'] with k hk hδk hak b hb
    have hbT : b ∈ T (ψ k) := (Finset.mem_filter.mp hb).2
    have hN1 : 1 < N (ψ k) := by linarith [hN (ψ k)]
    have hlog := hk b hbT
    have heq := Submission.Obl.k4_tempered_grid_selection.boundedExponent_eq hN1
      (hratio (ψ k) b).1 (hratio (ψ k) b).2
    dsimp only [f] at hlog
    rw [heq] at hlog
    have hclose : |Submission.Obl.k4_tempered_grid_selection.logarithmicExponent
        (N (ψ k)) (ratio (ψ k) b) - z ()| ≤ ε := by
      have htri := abs_sub_le
        (Submission.Obl.k4_tempered_grid_selection.logarithmicExponent (N (ψ k)) (ratio (ψ k) b))
        (a (ψ k) 0) (z ())
      linarith
    exact Submission.Obl.k4_tempered_grid_selection.power_band_of_exponent_fit hN1
      ((Real.rpow_pos_of_pos (by linarith) _).trans_le (hratio (ψ k) b).1) hclose

end Submission.Obl.k4_remainder_pure_profile_normalization
