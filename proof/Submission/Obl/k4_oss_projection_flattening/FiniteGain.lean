import Submission.Obl.k4_oss_projection_flattening.Interfaces
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.UniformWeakCoordinates

set_option linter.unusedVariables false

namespace Submission.Obl.k4_oss_projection_flattening

open WangZahlLot.Obl.wz_nonconcentrated_dot_products
open WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

/-- Robust expansion rules out the finite obstruction supplied by bad directions. -/
theorem finite_energy_gain (hbad : BadDirectionOutput)
    (b g : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) (hg : 0 < g) :
    FiniteEnergyGain b g := by
  classical
  obtain ⟨η, rP, hη, hrP, hrP1, hexpand⟩ :=
    uniform_weak_coordinate_expansion g b b hg hb hb
  obtain ⟨θ, rO, hθ, hθη, hrO, hrO1, hobstruct⟩ := hbad b η hb hb1 hη
  refine ⟨θ, min rP rO, hθ, lt_min hrP hrO,
    (min_le_left _ _).trans hrP1, ?_⟩
  intro δ hδ hδr d hd hdg A B hA hB hAsep hBsep hAF hBF hAlo hAhi hBlo hBhi
    ν hν hνsupp hνF
  have hδP : δ ≤ rP := (hδr.trans_le (min_le_left _ _)).le
  have hδO : δ < rO := hδr.trans_le (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδP.trans hrP1
  have hpow : δ ^ (-θ) ≤ δ ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hC : 1 ≤ δ ^ (-η) := by
    simpa using (Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -η ≤ 0 by linarith))
  have hratio : (B.card : ℝ) ≤ δ ^ (-2 * θ) * (A.card : ℝ) := by
    calc
      (B.card : ℝ) ≤ δ ^ (-d - θ) := hBhi
      _ = δ ^ (-2 * θ) * δ ^ (θ - d) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ δ ^ (-2 * θ) * (A.card : ℝ) :=
        mul_le_mul_of_nonneg_left hAlo (Real.rpow_nonneg hδ.le _)
  by_contra hlarge
  obtain ⟨S, hS, hSunit, hSF, hrelations⟩ :=
    hobstruct δ hδ hδO A B hA hB hAsep hBsep hratio ν hν hνsupp hνF hlarge
  have hAF' : RealFiniteFrostman δ (δ ^ (-η)) b A := by
    intro x u hu
    exact (hAF x u hu).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (hδ.le.trans hu) _))
        (Nat.cast_nonneg _))
  have hBF' : RealFiniteFrostman δ (δ ^ (-η)) b B := by
    intro x u hu
    exact (hBF x u hu).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (hδ.le.trans hu) _))
        (Nat.cast_nonneg _))
  have hAlo' : δ ^ (η - d) ≤ (A.card : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show θ - d ≤ η - d by linarith)).trans hAlo
  have hBlo' : δ ^ (η - d) ≤ (B.card : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show θ - d ≤ η - d by linarith)).trans hBlo
  have hAhi' : (A.card : ℝ) ≤ δ ^ (-d - η) := hAhi.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hBhi' : (B.card : ℝ) ≤ δ ^ (-d - η) := hBhi.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  obtain ⟨t, ht, htexpand⟩ := hexpand δ b b d (δ ^ (-η)) hδ hδP
    le_rfl le_rfl hd hdg hC le_rfl A B S hA hB hS hSunit
    hAF' hBF' hSF hAsep hBsep hAhi' hBhi' hAlo' hBlo'
  obtain ⟨R, hRdense, m, z, hmsmall, hcover⟩ := hrelations t ht
  have hset : {p : A × B | R p.1 p.2} =
      (↑(Finset.univ.filter (fun p : A × B => R p.1 p.2)) : Set (A × B)) := by
    ext p
    simp
  rw [hset, Set.ncard_coe_finset] at hRdense
  have hcov : Covers δ
      ((fun q : A × B => (q.1 : ℝ) + t * (q.2 : ℝ)) ''
        (↑(Finset.univ.filter (fun q : A × B => R q.1 q.2)) : Set (A × B))) z := by
    rintro x ⟨q, hq, rfl⟩
    have hR : R q.1 q.2 := by simpa using hq
    obtain ⟨i, hi⟩ := hcover q.1 q.2 hR
    exact Set.mem_iUnion.mpr ⟨i, by simpa [Metric.mem_closedBall] using hi⟩
  exact (not_lt_of_ge ((htexpand R hRdense) m z hcov)) hmsmall

end Submission.Obl.k4_oss_projection_flattening
