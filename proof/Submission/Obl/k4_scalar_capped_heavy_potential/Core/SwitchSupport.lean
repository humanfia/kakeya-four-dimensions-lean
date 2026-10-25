/- Adapted (namespace renamed) from LOT tree oai_074 (this tree), obligation o062,
session x0511, branch x0511, commit f33e26edad,
Submission/Lib/K4ScalarCoreTools/Simulation/SwitchSupport.lean (an unadmitted lib candidate).
Its own credits follow unchanged. -/

/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/SwitchSupport.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit 778c2ed,
Submission/Obl/k4_scalar_mesh_projection/SwitchSupport.lean.
-/

import Submission.Lib.K4ScalarSwitching.SwitchConservativity

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching

def switchedBaseEndpoint (x : Fin 2 → ℝ) (v δ : Fin 4 → ℝ) : Fin 2 → ℝ :=
  fun d => x d + ∑ k : Fin 4, ((![1, v k] : Fin 2 → ℝ) d) * δ k

def frozenBaseTranslation (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (last : Fin 2) (w : ℝ) :
    Fin 2 → ℝ := x + w • ![1, v (complementaryControl last)]

theorem switchedBaseEndpoint_slice (x : Fin 2 → ℝ) (v : Fin 4 → ℝ)
    (last : Fin 2) (w : ℝ) (δ : Fin 3 → ℝ) :
    switchedBaseEndpoint x v (slicePoint last w δ) =
      ![δ 0 + δ 1 + δ 2,
        v 0 * δ 0 + v 1 * δ 1 + v (Fin.natAdd 2 last) * δ 2] +
          frozenBaseTranslation x v last w := by
  ext d
  fin_cases last <;> fin_cases d <;>
    norm_num [switchedBaseEndpoint, slicePoint, frozenBaseTranslation,
      complementaryControl, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Approximate simulated endpoints lie in the correspondingly enlarged
physical support cell, coordinate by coordinate. -/
theorem simulated_endpoint_mem_enlarged_cell
    (actual simulated center : Fin 2 → ℝ) (height predicted c r e a h : ℝ)
    (hbase : ∀ d, |actual d - center d| ≤ r)
    (herror : ∀ d, |simulated d - actual d| ≤ e)
    (hheight : |height - c| ≤ a) (hprediction : |predicted - height| ≤ h) :
    simulated ∈ Icc (fun d => center d - (r + e)) (fun d => center d + (r + e)) ∧
      |predicted - c| ≤ a + h := by
  have hb (d : Fin 2) : |simulated d - center d| ≤ r + e := by
    have h := abs_add_le (simulated d - actual d) (actual d - center d)
    have heq : simulated d - actual d + (actual d - center d) = simulated d - center d := by ring
    rw [heq] at h
    linarith [hbase d, herror d]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro d
    have hh := (abs_le.mp (hb d)).1
    linarith
  · intro d
    have hh := (abs_le.mp (hb d)).2
    linarith
  · have hh := abs_add_le (predicted - height) (height - c)
    have heq : predicted - height + (height - c) = predicted - c := by ring
    rw [heq] at hh
    linarith

theorem volume_scalar_base_cell (center : Fin 2 → ℝ) (r : ℝ) :
    volume (Icc (fun d => center d - r) (fun d => center d + r)) =
      ENNReal.ofReal (2 * r) ^ 2 := by
  rw [Real.volume_Icc_pi]
  have hw (d : Fin 2) : center d + r - (center d - r) = 2 * r := by ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The high-curl endpoint-volume bound in ordinary physical endpoint
coordinates. Every translated slice uses exactly the original sum of
base-cell areas; the starting height is subtracted from the target centers. -/
theorem exists_switching_support_volume_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (K q κ η ε X₀ : ℝ),
        1 ≤ K → 0 < q → 0 < κ → 0 < η → η ≤ 1 → 0 ≤ ε →
        (∀ i, |v i| ≤ K) → 1 / K ≤ |v 1 - v 0| → 1 / K ≤ |v 3 - v 2| →
        8 * K ^ 4 * κ < |eval x (pderiv 0 B - pderiv 1 A)| →
        ∀ (ι : Type*) (S : Set (Fin 4 → ℝ)) (F : Finset ι)
          (E : ι → Set (Fin 2 → ℝ)) (c : ι → ℝ),
          MeasurableSet S → S ⊆ Icc (fun _ => -q) (fun _ => q) →
          (∀ i ∈ F, MeasurableSet (E i)) →
          (∀ δ ∈ S, ∃ i ∈ F, switchedBaseEndpoint x v δ ∈ E i ∧
            |X₀ + eval δ (brokenHeight A B x v) - c i| ≤ ε) →
          volume S ≤ ENNReal.ofReal (q ^ 4 * η) +
            ENNReal.ofReal (2 * q) * (∑ i ∈ F, volume (E i)) *
              ENNReal.ofReal (4 * ((D : ℝ) + 2) * ε /
                ((q * κ) * η ^ (4 * D) /
                  (2 * C * (512 * ((D : ℝ) + 1)) ^ (4 * D)))) := by
  obtain ⟨C, hC, hvolume⟩ := exists_switching_endpoint_volume_constant D
  refine ⟨C, hC, ?_⟩
  intro A B hA hB x v K q κ η ε X₀ hK hq hκ hη hη1 hε hv hI hJ hcurl
    ι S F E c hS hbox hE hcover
  let E' : Fin 2 → ℝ → ι → Set (Fin 2 → ℝ) := fun last w i =>
    (fun z => z + frozenBaseTranslation x v last w) ⁻¹' E i
  have hE' (last : Fin 2) (w : ℝ) (i : ι) : volume (E' last w i) = volume (E i) :=
    measure_preimage_add_right volume _ _
  apply hvolume A B hA hB x v K q κ η ε hK hq hκ hη hη1 hε hv hI hJ hcurl
    ι S F E' (fun _ _ i => c i - X₀) (∑ i ∈ F, volume (E i)) hS hbox
  · intro last w hw i hi
    exact (hE i hi).preimage (by fun_prop)
  · intro last w hw
    simp only [hE', le_refl]
  · intro last w hw δ hδ
    obtain ⟨i, hi, hb, hh⟩ := hcover _ hδ
    refine ⟨i, hi, ?_, ?_⟩
    · change _ + frozenBaseTranslation x v last w ∈ E i
      rw [← switchedBaseEndpoint_slice]
      exact hb
    · convert hh using 2
      ring

end Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching
