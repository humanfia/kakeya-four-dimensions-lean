-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.CurrentReferenceCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Lib.K4ReferenceMeshPreparation.ReferenceFloors

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette

open Set MeasureTheory
open Submission.Lib.K4FinalLawSelection
open scoped ENNReal

noncomputable section

/-- Keep both legal reference numerators and current-record conditional
ratios from the SAME original floor pruning. The test family may contain
all Borel velocity events and is queried only after the retained set. -/
theorem exists_record_reference_and_current_restriction
    {Ω Rec Tests : Type*} [MeasurableSpace Ω] [Fintype Rec]
    (ν μ : Measure Ω) (hμ : μ ≤ ν)
    (piece : Rec → Set Ω) (hm : ∀ r, MeasurableSet (piece r))
    (weight : Rec → ENNReal) (C cut : ℝ) (hcut : 0 < cut)
    (test : Tests → Set Ω) (factor : Tests → ENNReal)
    (hnum : ∀ r t, μ (piece r∩test t) ≤ ENNReal.ofReal C*weight r*factor t) :
    ∃ G : Set Ω, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal cut*∑ r, weight r ∧
      (∀ r, (μ.restrict G) (piece r)=0 ∨
        ENNReal.ofReal cut*weight r ≤ (μ.restrict G) (piece r)) ∧
      (∀ r t, (μ.restrict G) (piece r∩test t) ≤
        ENNReal.ofReal (C/cut)*ν (piece r)*factor t) ∧
      ∀ r t, (μ.restrict G) (piece r∩test t) ≤
        ENNReal.ofReal (C/cut)*(μ.restrict G) (piece r)*factor t := by
  classical
  obtain ⟨G,hG,hloss,hfloor⟩ := simultaneous_reference_floors Finset.univ piece hm
    (fun r => ENNReal.ofReal cut*weight r) μ
  have hcurrent (r : Rec) (t : Tests) : (μ.restrict G) (piece r∩test t) ≤
      ENNReal.ofReal (C/cut)*(μ.restrict G) (piece r)*factor t := by
    rcases hfloor r (Finset.mem_univ r) with hz | hf
    · exact ((measure_mono inter_subset_left).trans_eq hz).trans zero_le
    · have hw : weight r ≤ (ENNReal.ofReal cut)⁻¹*(μ.restrict G) (piece r) := by
        calc
          _ = (ENNReal.ofReal cut)⁻¹*(ENNReal.ofReal cut*weight r) := by
            rw [←mul_assoc,ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hcut).ne'
              ENNReal.ofReal_ne_top,one_mul]
          _ ≤ _ := mul_le_mul' le_rfl hf
      calc
        _ ≤ μ (piece r∩test t) := Measure.restrict_le_self _
        _ ≤ ENNReal.ofReal C*weight r*factor t := hnum r t
        _ ≤ ENNReal.ofReal C*((ENNReal.ofReal cut)⁻¹*(μ.restrict G) (piece r))*factor t :=
          mul_le_mul' (mul_le_mul' le_rfl hw) le_rfl
        _ = _ := by rw [ENNReal.ofReal_div_of_pos hcut,div_eq_mul_inv]; ac_rfl
  refine ⟨G,hG,?_,(fun r => hfloor r (Finset.mem_univ r)),?_,hcurrent⟩
  · simpa only [Finset.mul_sum] using hloss
  · intro r t
    exact (hcurrent r t).trans (mul_le_mul'
      (mul_le_mul' le_rfl ((Measure.restrict_le_self.trans hμ) _)) le_rfl)

/-- The same retained record floor passes ANY original-history ratio
to the current record. In particular this carries strip breadth without
an additional state-renewal deletion. -/
theorem current_record_ratio_of_history_cap
    {Ω : Type*} [MeasurableSpace Ω]
    (ν μ : Measure Ω) (hμ : μ ≤ ν) (piece history B : Set Ω)
    (hsub : piece⊆history) {cut cap : ENNReal} (hcut : cut≠0) (hcutTop : cut≠⊤)
    (hfloor : μ piece=0 ∨ cut*ν history ≤ μ piece)
    (hcap : ν (history∩B) ≤ cap*ν history) :
    μ (piece∩B) ≤ (cap/cut)*μ piece := by
  rcases hfloor with hz | hf
  · exact ((measure_mono inter_subset_left).trans_eq hz).trans zero_le
  · have hw : ν history ≤ cut⁻¹*μ piece := by
      calc
        _ = cut⁻¹*(cut*ν history) := by rw [←mul_assoc,ENNReal.inv_mul_cancel hcut hcutTop,one_mul]
        _ ≤ _ := mul_le_mul' le_rfl hf
    calc
      _ ≤ ν (piece∩B) := hμ _
      _ ≤ ν (history∩B) := measure_mono (inter_subset_inter_left B hsub)
      _ ≤ cap*ν history := hcap
      _ ≤ cap*(cut⁻¹*μ piece) := mul_le_mul' le_rfl hw
      _ = _ := by rw [div_eq_mul_inv,mul_assoc]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
