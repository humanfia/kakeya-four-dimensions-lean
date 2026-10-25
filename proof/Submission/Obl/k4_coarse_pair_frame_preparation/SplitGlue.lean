import Submission.Obl.k4_coarse_pair_frame_preparation.SplitStatements

namespace Submission.Obl.k4_coarse_pair_frame_preparation

/-- Extract the pure-density and global-data clauses needed by the frame step. -/
theorem frameData_of_prob : ∀ N K L d S η W ω ν E P B f g G,
    prob N K L d S η W ω ν E P B f g G →
    FrameData N W ω ν E P B f g L d := by
  intro N K L d S η W ω ν E P B f g G hp
  rcases hp with ⟨hN, hlim, hK, hL, hd, hd1, hS, hη,
    ⟨M, D, hs⟩, hpure, hang, hmono, htyp, hcap, hatyp⟩
  have hw : ∀ k γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧
      0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧
      (P k γ).totalDegree ≤ 2 ∧ MeasurableSet (E k γ) ∧
      ∀ i, fmt 7 (N k ^ M) D {r : Fin 7 → ℝ |
        ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ E k γ} := by
    intro k γ
    rcases (hs k).2.2.2.1 γ with
      ⟨hv, hB, hBu, hBi, hP, hPc, hrep, hEm, hEs, hEb, hEf, hAE, hfloor⟩
    exact ⟨hv, hB, hBu, hBi, hP, hEm, hEf⟩
  refine ⟨hN, hlim, hL, (fun k => (hs k).2.1), (fun k => (hs k).2.2.1),
    (fun k γ => (hw k γ).1), ⟨M, ?_⟩, ⟨M, D, ?_⟩,
    (fun k γ => (hw k γ).2.2.2.2.1), hpure, hd.le, hd1.le, hcap⟩
  · intro k γ
    exact ⟨(hw k γ).2.1, (hw k γ).2.2.1, (hw k γ).2.2.2.1⟩
  · intro k γ
    exact (hw k γ).2.2.2.2.2

/-- Choose the native loss first, then the angular depth, and finally the frame loss. -/
theorem preparation_of_stages
    (hnative : NativePreparationStatement)
    (hnormal : NormalPreparationStatement)
    (hframe : FramePreparationStatement) : PreparationStatement := by
  rcases hnative with ⟨A, hA, hnative⟩
  rcases hframe with ⟨Cf, hCf, hframe⟩
  intro d₀ S η hd₀ hS hη
  obtain ⟨R, hR, hAR, hnormal⟩ := hnormal A S hA hS
  refine ⟨Cf * (R + 1), η / R, mul_pos hCf (by linarith), div_pos hη hR, ?_⟩
  intro N K L d W ω ν E P B f g G hp hdd h e he heh heL hk
  have hu : 0 < R * e := mul_pos hR he
  have huL : R * e ≤ η * L := by
    have ht := mul_lt_mul_of_pos_left heL hR
    have hc : R * (η / R * L) = η * L := by
      field_simp
    rw [hc] at ht
    exact ht.le
  have hn := hnative N K L d S η W ω ν E P B f g G hp
    h e (R * e) he heh hu huL hk
  have ha := hnormal N K L d η W ω ν E P B f g G hp (h - e) e he huL hn
  have hdata := frameData_of_prob N K L d S η W ω ν E P B f g G hp
  have hf := hframe N W ω ν E P B f g G L d hdata
    S (R * e) e (R * e) (h - e) hu he ha
  convert hf using 1
  ring

end Submission.Obl.k4_coarse_pair_frame_preparation
