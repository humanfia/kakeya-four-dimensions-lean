/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit 22cc6cc,
Submission/Obl/k4_scalar_mesh_projection/SwitchConservativity.lean.
-/

import Submission.Lib.K4ScalarSwitching.SwitchExceptional

namespace Submission.Lib.K4ScalarSwitching.Switching

open Set MeasureTheory MvPolynomial

/-- High curl makes the inverse image of a small endpoint support small.
The first term discards a polynomial sublevel set; the second retains the
full base-area times height-width factor from the selected regular minor. -/
theorem exists_switching_endpoint_volume_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (K q κ η ε : ℝ),
        1 ≤ K → 0 < q → 0 < κ → 0 < η → η ≤ 1 → 0 ≤ ε →
        (∀ i, |v i| ≤ K) → 1 / K ≤ |v 1 - v 0| → 1 / K ≤ |v 3 - v 2| →
        8 * K ^ 4 * κ < |eval x (pderiv 0 B - pderiv 1 A)| →
        ∀ (ι : Type*) (S : Set (Fin 4 → ℝ)) (F : Finset ι)
          (E : Fin 2 → ℝ → ι → Set (Fin 2 → ℝ))
          (c : Fin 2 → ℝ → ι → ℝ) (area : ENNReal),
          MeasurableSet S → S ⊆ Icc (fun _ => -q) (fun _ => q) →
          (∀ last, ∀ w ∈ Icc (-q) q, ∀ i ∈ F, MeasurableSet (E last w i)) →
          (∀ last, ∀ w ∈ Icc (-q) q, (∑ i ∈ F, volume (E last w i)) ≤ area) →
          (∀ last, ∀ w ∈ Icc (-q) q, ∀ δ : Fin 3 → ℝ, slicePoint last w δ ∈ S →
            ∃ i ∈ F,
              (![δ 0 + δ 1 + δ 2,
                v 0 * δ 0 + v 1 * δ 1 + v (Fin.natAdd 2 last) * δ 2]) ∈ E last w i ∧
              |eval (slicePoint last w δ) (brokenHeight A B x v) - c last w i| ≤ ε) →
          volume S ≤ ENNReal.ofReal (q ^ 4 * η) +
            ENNReal.ofReal (2 * q) * area *
              ENNReal.ofReal (4 * ((D : ℝ) + 2) * ε /
                ((q * κ) * η ^ (4 * D) /
                  (2 * C * (512 * ((D : ℝ) + 1)) ^ (4 * D)))) := by
  obtain ⟨C, hC, hsub⟩ := exists_small_cube_switching_sublevel_constant D
  refine ⟨C, hC, ?_⟩
  intro A B hA hB x v K q κ η ε hK hq hκ hη hη1 hε hv hI hJ hcurl
    ι S F E c area hS hbox hE harea hcover
  let R := brokenHeight A B x v
  let threshold := (q * κ) * η ^ (4 * D) / (2 * C * (512 * ((D : ℝ) + 1)) ^ (4 * D))
  have hthreshold : 0 < threshold := by dsimp [threshold]; positivity
  obtain ⟨last, hsmall⟩ := hsub A B hA hB x v K q κ η hK hq hκ hη hη1 hv hI hJ hcurl
  let minor := endpointMinor R v (Fin.natAdd 2 last)
  let Bad : Set (Fin 4 → ℝ) :=
    {δ | δ ∈ Icc (fun _ => -q) (fun _ => q) ∧ |eval δ minor| ≤ threshold}
  let Good : Set (Fin 4 → ℝ) := {δ | δ ∈ S ∧ threshold ≤ |eval δ minor|}
  have hBad : volume Bad ≤ ENNReal.ofReal (q ^ 4 * η) := hsmall.le
  have hGood : MeasurableSet Good :=
    hS.inter (isClosed_le continuous_const (MvPolynomial.continuous_eval minor).abs).measurableSet
  have hdet : v 1 - v 0 ≠ 0 := by
    apply abs_pos.mp
    exact (one_div_pos.mpr (by linarith : 0 < K)).trans_le hI
  have hR : R.totalDegree ≤ D + 1 :=
    (brokenHeight_degree A B x v).trans (Nat.add_le_add_right (max_le hA hB) 1)
  have hregular := four_parameter_endpoint_volume_le v hdet R last (D + 1) hR
    Good (Icc (-q) q) F (E last) (c last) area hε hthreshold hGood measurableSet_Icc
    (hE last) (harea last)
    (fun δ hδ => ⟨(hbox hδ.1).1 _, (hbox hδ.1).2 _⟩)
    (fun w hw δ hδ => hcover last w hw δ hδ.1) (fun _ hδ => hδ.2)
  have hvolI : volume (Icc (-q) q) = ENNReal.ofReal (2 * q) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have hregular' : volume Good ≤ ENNReal.ofReal (2 * q) * area *
      ENNReal.ofReal (4 * ((D : ℝ) + 2) * ε / threshold) := by
    simpa only [hvolI, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hregular
  have hcov : S ⊆ Bad ∪ Good := by
    intro δ hδ
    by_cases hδ' : threshold ≤ |eval δ minor|
    · exact Or.inr ⟨hδ, hδ'⟩
    · exact Or.inl ⟨hbox hδ, (lt_of_not_ge hδ').le⟩
  exact (measure_mono hcov).trans ((measure_union_le Bad Good).trans (add_le_add hBad hregular'))

end Submission.Lib.K4ScalarSwitching.Switching
