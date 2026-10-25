/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at a653e9614f679c1b36a9606abd448afbd7b87d1f, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeComparisonPreparation.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeComparisonContext
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeFineNumerics

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- Prepare the ACTUAL native comparison from one old engine layer. Only one
finest-width mesh inequality remains numerical; it implies every cell/jitter
roundoff and geometric support condition. All assignments and laws are original. -/
def prepare_native_comparison {k : ℕ} {s ε D A ζ R : ℝ}
    (lev : cfg.AssignmentLevel k s) (hbasic : cfg.Basic)
    (hN : 1 ≤ cfg.N k) (hK : 1 ≤ cfg.K k)
    (hκ : 0 ≤ cfg.κ) (hκ1 : 2 * cfg.κ ≤ 1) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ cfg.μ k) (hσ0 : σ univ ≠ 0)
    {m : ℕ} (AH : Fin m → Set α) (group : Fin m → Fin 3 → ℤ) (hH : Fin m → Fin 6 → ℝ)
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D (cfg.N k ^ (-s)) m AH group hH)
    (caps : OriginalWidthCapsAt (cfg.N k) (cfg.K k) cfg.d R (cfg.μ k) (cfg.π k) (cfg.b k))
    (hR : 1 < R) (he₀ : R⁻¹ ≤ cfg.e₀) (he₀' : cfg.e₀ ≤ R)
    (hA : cfg.N k ^ (-R) ≤ A) (hA1 : A ≤ 1)
    (hD : 0 < D) (hD1 : D ≤ 1) (hDq : D ≤ cfg.timeLength k s ^ 2)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hsource : cfg.N k ^ ε * cfg.N k ^ (-s) ≤ A)
    (hwitness : cfg.K k * cfg.N k ^ (-s) +
      16 * cfg.K k ^ 4 * cfg.N k ^ (-cfg.e₀) ≤ A)
    (hfine : let B := cfg.N k ^ ε + 8 * cfg.K k ^ 4 * (1 + 6 * cfg.K k)
      (200 * B / D) * (cfg.N k ^ (-cfg.e₀) + cfg.K k * cfg.N k ^ (-R)) ≤
        cfg.N k ^ (-s) * ζ) : NativeComparisonData cfg k s σ := by
  classical
  have hNp : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  letI := (hbasic k).2.1
  letI := (hbasic k).2.2.1
  have hmu := Submission.Obl.k4_horizontal_coefficient_count.current_total_mass_le
    (cfg.ν k) (cfg.μ k) (hbasic k).2.2.2.1 (hbasic k).2.2.2.2.2.1
  have hfinite : IsFiniteMeasure σ := ⟨((hσ univ).trans hmu).trans_lt ENNReal.ofReal_lt_top⟩
  let pack := cfg.affine_table lev hN hK hκ hκ1 hs
  let L := Classical.choose pack
  have hL := (Classical.choose_spec pack).1
  have hfit := (Classical.choose_spec pack).2
  let S := Classical.choice (cfg.exists_comparison_support lev hbasic hKp.le σ hσ hσ0 H)
  let B := cfg.N k ^ ε + 8 * cfg.K k ^ 4 * (1 + 6 * cfg.K k)
  have hNε : 1 ≤ cfg.N k ^ ε := Real.one_le_rpow hN hε
  have hB : 1 ≤ B := by
    dsimp [B]
    have hh : 0 ≤ 8 * cfg.K k ^ 4 * (1 + 6 * cfg.K k) := by positivity
    linarith
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hNp _
  have ha1 : cfg.N k ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hq1 : cfg.timeLength k s ≤ 1 := by
    unfold Data.timeLength
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hAZ : cfg.N k ^ (-s) * ζ ≤ A := by
    have hh := mul_le_mul_of_nonneg_right hNε ha.le
    have hz := mul_le_mul_of_nonneg_left hζ1 ha.le
    nlinarith
  have hc := finest_mesh_control hK hB hD hD1
    (Real.rpow_pos_of_pos hNp _) (Real.rpow_pos_of_pos hNp _) ha ha1 hζ hζ1 hq hq1 hDq hfine
  exact {
    ε := ε
    D := D
    a := cfg.N k ^ (-s)
    M := 8 * cfg.K k ^ 4
    R := R
    re := R
    A := A
    m := m
    AH := AH
    group := group
    hH := hH
    support := S
    layer := H
    measurable_b := (hbasic k).1
    dominated := hσ
    finite_original := hfinite
    finite_palette := inferInstance
    caps := caps
    re_lower := (inv_le_one_of_one_le₀ hR.le).trans hR.le
    re_upper := le_rfl
    velocity_lower := he₀
    velocity_upper := he₀'
    width_lower := hA
    width_upper := hA1
    L := L
    slopes := hL
    true_fit := hfit
    N_pos := hNp
    K_one := hK
    M_nonneg := by positivity
    D_pos := hD
    D_one := hD1
    mesh_one := hc.2.2.1
    mesh_time := hc.2.2.2.1
    mesh_room := hc.2.2.2.2.1
    source_fit := hsource
    witness_fit := by nlinarith [hwitness]
    round_cell := hc.2.2.2.2.2.1.trans hAZ
    round_jitter := hc.2.2.2.2.2.2.trans hAZ }

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
