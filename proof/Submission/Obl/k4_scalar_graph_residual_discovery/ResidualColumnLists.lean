/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ResidualColumnLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ResidualLists
import Submission.Obl.k4_scalar_graph_residual_discovery.FiniteRecords

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation

namespace Zoom

noncomputable section

/-- Build the actual residual column list from current coefficient-entry
floors and the ORIGINAL fine-velocity palette. The parameter list is
constructed from actual retained points. Its palette factor cancels
before the per-piece residual variation estimate is used. -/
theorem residual_column_list_of_final_parameter_floors
    (μ : Measure ScalarIncidence) [IsFiniteMeasure μ] (θ : Measure ScalarLine)
    {R E : Set ScalarIncidence} (hR : MeasurableSet R) (hRE : R ⊆ E)
    {ρ β h A H η s C Hrow L ζ : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hh : 0 < h) (hscale : β ≤ ρ * h)
    (hA : 0 < A) (hH : 0 < H) (hη : 0 < η) (hs : 0 < s) (hC : 0 ≤ C)
    (hHrow : 0 ≤ Hrow) (hL : 0 ≤ L) (hζh : ζ ≤ h)
    (q : Fin 5 → ℤ) (z : Fin 3 → ℤ) (c : ℤ) (p : ℝ≥0∞) (hpt : p ≠ ∞)
    (hworld : ∀ v ∈ R, cell ρ v.1.2 = q)
    (hcoeff : ∀ v ∈ R, ∀ e, |v.1.2 e| ≤ H)
    (htime : ∀ v ∈ R, |v.2| ≤ 1)
    (hfloor : ∀ b,
      R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q b) h z = ∅ ∨
        ENNReal.ofReal (h / A) * θ (parameterPiece ρ β q b) <
          μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q b) h z))
    (hprior : ∀ b,
      μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q b) h z) ≠ 0 →
      b 1 = c → ENNReal.ofReal (η * s / H) * p ≤ θ (parameterPiece ρ β q b))
    (hcap : μ {v | v ∈ E ∧ (⌊v.1.2 1 / β⌋ : ℤ) = c ∧ cell h (position ρ q v) = z} ≤
      ENNReal.ofReal (H ^ 2 * h * C * s) * p)
    (F : ℝ → ℝ) (S : ScalarIncidence → ℝ)
    (hrow : ∀ v ∈ R, |F v.2| ≤ Hrow)
    (hrowvar : ∀ v ∈ R, ∀ v' ∈ R, |F v.2 - F v'.2| ≤ L * (|v.2 - v'.2| + ζ))
    (hnear : ∀ v ∈ R, |S v - residual ρ q F v.1 v.2| ≤ h) :
    ∃ Q : Finset ℤ,
      (Q.card : ℝ) ≤ (A * H ^ 3 * C / η) * (2 * (7 + Hrow + 2 * L) + 2) ∧
      ∀ v ∈ R, cell h (position ρ q v) = z → (⌊v.1.2 1 / β⌋ : ℤ) = c → ⌊S v / h⌋ ∈ Q := by
  classical
  let T := {v : ScalarIncidence | v ∈ R ∧ cell h (position ρ q v) = z ∧
    (⌊v.1.2 1 / β⌋ : ℤ) = c}
  have hfinite : ((fun v : ScalarIncidence => cell β v.1.2) '' T).Finite :=
    finite_original_coefficient_records T hH.le hβ (fun v hv => hcoeff v hv.1)
  let B := hfinite.toFinset
  have hwitness (b : Fin 5 → ℤ) (hb : b ∈ B) : ∃ v ∈ T, cell β v.1.2 = b :=
    hfinite.mem_toFinset.mp hb
  have hvel (b : Fin 5 → ℤ) (hb : b ∈ B) : b 1 = c := by
    obtain ⟨v, hv, hbin⟩ := hwitness b hb
    exact (congrFun hbin 1).symm.trans hv.2.2
  have hpoint (b : Fin 5 → ℤ) (hb : b ∈ B) :
      (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q b) h z).Nonempty := by
    obtain ⟨v, hv, hbin⟩ := hwitness b hb
    refine ⟨v, hv.1, ⟨hworld v hv.1, hbin⟩, ?_⟩
    rw [quadraticCoordinateCode_normalizedCoeff hρ (hworld v hv.1)]
    exact hv.2.1
  have hpositive (b : Fin 5 → ℤ) (hb : b ∈ B) :
      μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q b) h z) ≠ 0 := by
    rcases hfloor b with hempty | hpos
    · exact False.elim ((hpoint b hb).ne_empty hempty)
    · exact ne_of_gt (lt_of_le_of_lt zero_le hpos)
  have hcurrent (b : Fin 5 → ℤ) (hb : b ∈ B) :
      ENNReal.ofReal (h / A) * θ (parameterPiece ρ β q b) ≤
        μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q b) h z) := by
    rcases hfloor b with hempty | hpos
    · exact False.elim ((hpoint b hb).ne_empty hempty)
    · exact hpos.le
  have hBcard := fine_parameter_piece_count μ θ hR hRE hρ hh hA hH hη hs hC q z c B
    hvel p hpt hpositive (fun b hb => hprior b (hpositive b hb) (hvel b hb)) hcurrent hcap
  have hvariation (v : ScalarIncidence) (hv : v ∈ T) (v' : ScalarIncidence) (hv' : v' ∈ T) :
      |F v.2 - F v'.2| ≤ (2 * L) * h := by
    have hgap : |v.2 - v'.2| ≤ h :=
      (norm_le_pi_norm (position ρ q v - position ρ q v') 0).trans
        (norm_sub_lt_of_cell_eq hh (hv.2.1.trans hv'.2.1.symm)).le
    apply (hrowvar v hv.1 v' hv'.1).trans
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hgap hζh) hL]
  obtain ⟨Q, hQcard, hQmem⟩ := residual_bins_of_parameter_list hρ hβ hh hscale hHrow
    (by positivity : 0 ≤ 2 * L) q z F S T B
    (fun v hv => hfinite.mem_toFinset.mpr ⟨v, hv, rfl⟩)
    (fun v hv => ⟨hworld v hv.1, hv.2.1⟩) (fun v hv => htime v hv.1)
    (fun v hv => hrow v hv.1) hvariation (fun v hv => hnear v hv.1)
  refine ⟨Q, hQcard.trans (mul_le_mul_of_nonneg_right hBcard (by positivity)), ?_⟩
  intro v hv hz hc
  exact hQmem v ⟨hv, hz, hc⟩

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
