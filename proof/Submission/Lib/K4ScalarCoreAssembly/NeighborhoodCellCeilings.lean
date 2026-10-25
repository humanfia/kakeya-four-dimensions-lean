/-
Adapted from: here:o062
Original proof: o062/x0212, 71f65b82, Submission/Obl/k4_scalar_mesh_projection/NeighborhoodCellCeilings.lean.
Original law, observed physical palettes and witness rows remain unnormalized.
-/

import Submission.Lib.K4ScalarCoreAssembly.NeighborhoodPalettes
import Submission.Lib.K4ScalarCoreAssembly.CartesianFrame
import Submission.Lib.K4ScalarCoreAssembly.Support

namespace Submission.Lib.K4ScalarCoreAssembly

open Submission.Lib.K4ScalarCoreTools.Finalization
open Submission.Lib.K4ScalarCoreTools.Simulation.Switching
open Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarSwitching.Switching

open Set MeasureTheory
open scoped ENNReal

/-- A new mesh cell meets only the derived finite neighborhood of old
cells, so the ORIGINAL old-cell ceiling controls its original mass. -/
theorem original_neighborhood_cell_ceiling {Ω J : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (d : ℕ) (A : Set Ω) (obs : Ω → J)
    (physical : Ω → Fin d → ℝ) (center : J → Fin d → ℝ)
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 ≤ R) (M : ℝ≥0∞)
    (hcap : ∀ q : Fin d → ℤ,
      μ (A ∩ {ω | (fun j => ⌊physical ω j/ε⌋)=q}) ≤ M)
    (hnear : ∀ ω ∈ A, ∀ j, |physical ω j-center (obs ω) j| ≤ R*ε) :
    ∀ i, μ (A ∩ {ω | obs ω=i}) ≤ ENNReal.ofReal ((4*R+11)^d)*M := by
  classical
  let code : Ω → Fin d → ℤ := fun ω j => ⌊physical ω j/ε⌋
  obtain ⟨F,hFcard,hknown⟩ := exists_neighborhood_field_palettes d A obs physical center code
    ε R 1 hε hR (by norm_num) (fun q => {q}) (fun _ => by simp)
    (fun _ _ => by simp [code]) hnear
  intro i
  have hcover : A ∩ {ω | obs ω=i} ⊆ ⋃ q : F i, A ∩ {ω | code ω=q.val} := by
    intro ω hω
    have hmem := hknown ω hω.1
    have hobs : obs ω=i := hω.2
    rw [hobs] at hmem
    exact mem_iUnion.mpr ⟨⟨code ω,hmem⟩,hω.1,rfl⟩
  have hcard : ((F i).card : ℝ≥0∞) ≤ ENNReal.ofReal ((4*R+11)^d) := by
    simpa only [mul_one,ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hFcard i)
  calc
    _ ≤ μ (⋃ q : F i, A ∩ {ω | code ω=q.val}) := measure_mono hcover
    _ ≤ ∑ q : F i, μ (A ∩ {ω | code ω=q.val}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _q : F i, M := Finset.sum_le_sum fun q _ => hcap q.val
    _ = ((F i).card : ℝ≥0∞)*M := by simp
    _ ≤ _ := mul_le_mul' hcard le_rfl

/-- The actual two-velocity grid inherits the original normalized
base-cell ceiling with an explicit polynomial frame loss. -/
theorem original_two_velocity_grid_cell_ceiling {Ω X Y : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (cell : Ω → X × Y) (base : Ω → Fin 2 → ℝ)
    (x : X → ℝ) (y : Y → ℝ) (t0 y0 vr vc K ξ : ℝ)
    (hK : 1 ≤ K) (hξ : 0 < ξ) (hvr : |vr| ≤ K) (hvc : |vc| ≤ K) (hsep : vc ≠ vr)
    (hquant0 : ∀ ω ∈ A,
      |cartesianFrameCoordinates t0 y0 vr vc (base ω 0) (base ω 1) 0-x (cell ω).1| ≤ ξ)
    (hquant1 : ∀ ω ∈ A,
      |cartesianFrameCoordinates t0 y0 vr vc (base ω 0) (base ω 1) 1-y (cell ω).2| ≤ ξ)
    (M : ℝ≥0∞) (hcap : ∀ q : Fin 2 → ℤ,
      μ (A ∩ {ω | (fun j => ⌊base ω j/ξ⌋)=q}) ≤ M) :
    ∀ c, μ (A ∩ {ω | cell ω=c}) ≤ ENNReal.ofReal ((8*K+11)^2)*M := by
  let center (c : X × Y) : Fin 2 → ℝ :=
    ![t0+x c.1+y c.2,y0+vr*x c.1+vc*y c.2]
  have hnear (ω : Ω) (hω : ω ∈ A) (j : Fin 2) :
      |base ω j-center (cell ω) j| ≤ (2*K)*ξ := by
    let c := cartesianFrameCoordinates t0 y0 vr vc (base ω 0) (base ω 1)
    have hq0 : |c 0-x (cell ω).1| ≤ ξ := hquant0 ω hω
    have hq1 : |c 1-y (cell ω).2| ≤ ξ := hquant1 ω hω
    have ht := cartesianFrame_time_reconstruction t0 y0 vr vc (base ω 0) (base ω 1) hsep
    have hy := cartesianFrame_space_reconstruction t0 y0 vr vc (base ω 0) (base ω 1) hsep
    change t0+c 0+c 1=base ω 0 at ht
    change y0+vr*c 0+vc*c 1=base ω 1 at hy
    fin_cases j
    · change |base ω 0-(t0+x (cell ω).1+y (cell ω).2)| ≤ (2*K)*ξ
      rw [show base ω 0-(t0+x (cell ω).1+y (cell ω).2)=
        (c 0-x (cell ω).1)+(c 1-y (cell ω).2) by linarith]
      have h := (abs_add_le _ _).trans (add_le_add hq0 hq1)
      nlinarith
    · change |base ω 1-(y0+vr*x (cell ω).1+vc*y (cell ω).2)| ≤ (2*K)*ξ
      rw [show base ω 1-(y0+vr*x (cell ω).1+vc*y (cell ω).2)=
        vr*(c 0-x (cell ω).1)+vc*(c 1-y (cell ω).2) by nlinarith]
      apply (abs_add_le _ _).trans
      simp only [abs_mul]
      have h0 := mul_le_mul hvr hq0 (abs_nonneg _) (by linarith : 0 ≤ K)
      have h1 := mul_le_mul hvc hq1 (abs_nonneg _) (by linarith : 0 ≤ K)
      nlinarith
  have h := original_neighborhood_cell_ceiling μ 2 A cell base center ξ (2*K) hξ
    (by positivity) M hcap hnear
  simpa only [show (4*(2*K)+11 : ℝ)=8*K+11 by ring] using h

end Submission.Lib.K4ScalarCoreAssembly
