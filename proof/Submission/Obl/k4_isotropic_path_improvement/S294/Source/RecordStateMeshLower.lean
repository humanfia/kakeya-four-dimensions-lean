-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordStateMeshLower, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordPaletteResolution

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- A tight lower power for the literal final state mesh. In
particular, its exponent does not acquire the front palette's tunable
depth factor. This is the physical floor of the record references. -/
theorem epsOf_lower_power
    {N L rA rB precision loss gain : ℝ} (Ep TA TB : ℕ) (hN : 0 < N) :
    N^(-((rB-rA)+((Ep:ℝ)+1)*(precision*gain*L)+
      (2*(Ep:ℝ)+2)*(loss*gain*L/((Ep:ℝ)+1))))/2 ≤
        epsOf Ep precision loss gain N L rA rB TA TB := by
  let pgl := precision*gain*L
  let kexp := loss*gain*L/((Ep:ℝ)+1)
  let pvExponent := (rB-rA)+(Ep:ℝ)*pgl+(2*(Ep:ℝ)+2)*kexp
  have hpv : N^(-pvExponent)/2 ≤ pvOf Ep precision loss gain N L rA rB TA TB :=
    pvOf_lower_power Ep TA TB hN
  have hz : N^(-pgl) ≤ zetaOf precision gain N L :=
    (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN pgl).1
  have hpv0 : 0 ≤ pvOf Ep precision loss gain N L rA rB TA TB :=
    (by positivity : (0:ℝ) ≤ N^(-pvExponent)/2).trans hpv
  have hidentity : epsOf Ep precision loss gain N L rA rB TA TB=
      pvOf Ep precision loss gain N L rA rB TA TB*zetaOf precision gain N L := by
    unfold epsOf pvOf
    ring
  calc
    _ = (N^(-pvExponent)/2)*N^(-pgl) := by
      rw [div_mul_eq_mul_div,←Real.rpow_add hN]
      congr 2
      dsimp only [pvExponent,pgl,kexp]
      ring
    _ ≤ pvOf Ep precision loss gain N L rA rB TA TB*zetaOf precision gain N L :=
      mul_le_mul hpv hz (Real.rpow_nonneg hN.le _) hpv0
    _ = _ := hidentity.symm

/-- A uniform physical depth bound pays the state-mesh floor. The
half-dyadic rounding is absorbed by one explicit positive margin. -/
theorem state_mesh_lower_of_depth_bound
    {N L rA rB precision loss gain depthBound margin : ℝ}
    (Ep TA TB : ℕ) (hN : 1 ≤ N) (hdepth : rB-rA ≤ depthBound)
    (hconstant : 2 ≤ N^margin) :
    N^(-(depthBound+((Ep:ℝ)+1)*(precision*gain*L)+
      (2*(Ep:ℝ)+2)*(loss*gain*L/((Ep:ℝ)+1))+margin)) ≤
        epsOf Ep precision loss gain N L rA rB TA TB := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  apply le_trans _ (epsOf_lower_power Ep TA TB hNp)
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ N^(-(depthBound+((Ep:ℝ)+1)*(precision*gain*L)+
        (2*(Ep:ℝ)+2)*(loss*gain*L/((Ep:ℝ)+1))+margin))*N^margin :=
      mul_le_mul_of_nonneg_left hconstant (Real.rpow_nonneg hNp.le _)
    _ = N^(-(depthBound+((Ep:ℝ)+1)*(precision*gain*L)+
        (2*(Ep:ℝ)+2)*(loss*gain*L/((Ep:ℝ)+1)))) := by
      rw [←Real.rpow_add hNp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
