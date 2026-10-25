-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.DenseResidual.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.DenseInput
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.ResidualPrism
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.DensityAlgebra
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.DensityMass

/-! Quantitative local extraction in an arbitrary half-mass residual. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- The input to dense broad subprism extraction is available in every
substantial residual of the old shading. -/
theorem dense_prism_in_residual {ω ζ η b d h ρ a c g : ℝ} {n N : ℕ}
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hη : 0 < η)
    (hηω : η ≤ ω/1000) (hηβ : η ≤ (ω*ζ/100)*ω/1000) (hb : b ≤ ω/1000)
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ η/4)
    (hsmall : (10:ℝ)^40*d^(η/2) ≤ 1)
    (x v : Fin n → V) (Y : Fin n → Set V)
    (hA : A d h (d^(-h)) (d^(-h)) n x v Y)
    (S : Finset (Fin n)) (Z : Fin n → Set V) (y w : Fin N → V) (f : Fin n → Fin N)
    (hC : C d h n x v Y S Z ρ N y w f True)
    (hH : H d h n x v S Z ρ N y w f a c 0 g)
    (hBr : Broad ω ζ d h ρ n N v S Z f)
    (hρ : d^(ω/100) ≤ ρ) (ha : a ≤ 2*d^(1-b)) (hc : c ≤ d^(9*ω/20))
    (hhigh : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
      d^(-24*ω/25) ≤ ({i | i ∈ S ∧ f i = k ∧ p ∈ Z i}.ncard : ℝ))
    (R : Fin n → Set V) (hRm : ∀ i, MeasurableSet (R i)) (hRZ : ∀ i, R i ⊆ Z i)
    (hRmass : (∑ i, volume.real (Z i))/2 ≤ ∑ i, volume.real (R i)) :
    Nonempty (DensePrismInput ω d (d^η) (10000*a)
      (10000*enlargedSlope (ρ*c) c*(d^(-ω/100)*c)) (d^(-ω/100)*c) ρ x v y w R) := by
  obtain ⟨J, z, e, G, γ, m₀, hHB⟩ := wz_move_two_long_grains_gain.H_iff.mp hH
  have hdc : d ≤ c := hHB.1.trans (hHB.2.1.trans hHB.2.2.1)
  have hcp : 0 < c := hd.trans_le hdc
  have hρp : 0 < ρ := (Real.rpow_pos_of_pos hd _).trans_le hρ
  have hρ1 : ρ ≤ 1 := (mul_le_mul_iff_left₀ hcp).mp (by simpa using hHB.2.2.1)
  have hβ : 0 < ω*ζ/100 := by positivity
  have hp := prep_powers hω hω1 hβ hη hηω hηβ hd hd1 hh hsmall hρ hρ1 hdc hc
  have hZT (i) : Z i ⊆ T d (x i) (v i) := (hC.1 i).2.1.trans (hA.2.1 i).2.2.2
  have hZfin (i) : volume (Z i) ≠ ∞ := measure_ne_top_of_subset (hC.1 i).2.1 (admissible_finite_mass hA i)
  have hRfin (i) : volume (R i) ≠ ∞ := measure_ne_top_of_subset (hRZ i) (hZfin i)
  have hZmass : O (32*d^η*(n : ℝ)*d^2) ≤ ∑ i, volume (Z i) := by
    refine (ENNReal.ofReal_le_ofReal ?_).trans (cover_incidence_lower hd hA hC)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp.mass_cost (Nat.cast_nonneg n)) (sq_nonneg d)
  obtain ⟨k, z', e', F, Q, hF, hcard, hdA, hAB, hBL, hQ, hends, hzero, hgood⟩ :=
    residual_enlarged_prism hA.1 hd hp.lambda_pos hp.lambda_one (Real.rpow_pos_of_pos hd _)
      hp.angle_low hp.angle_high hp.length_gain hp.length_pos hp.length_small hp.radius_small
      hp.endpoint_radius hp.endpoint_clearance hp.endpoint_budget hp.fibre_cost hp.cap_cost
      x v (fun i => (hA.2.1 i).1) (fun i => (hA.2.1 i).2.1) S Z R f y w z e G γ hHB
      (fun i => (hC.1 i).2.2) (fun i => (hC.1 i).1) hRm hZT hRZ
      (half_mass_of_real hZfin hRfin hRmass) hZmass hBr hhigh hC.2.2.2.1
  let L := d^(-ω/100)*c
  let B := 10000*enlargedSlope (ρ*c) c*L
  have hAp : 0 < 10000*a := hd.trans_le hdA
  have hBp : 0 < B := hAp.trans_le hAB
  have hQfin (i) : volume (Q i) ≠ ∞ := measure_ne_top_of_subset
    ((hQ i).2.1.trans inter_subset_left) (hRfin i)
  have hPvol : volume (P (10000*a) B L z' e') = O (10000*a*B*L) :=
    wz_clustered_cover_volume_gain.frozen_prism_volume hAp.le hBp.le hp.length_pos.le z' e'
  have hPfin : volume (P (10000*a) B L z' e') ≠ ∞ := by rw [hPvol]; exact ENNReal.ofReal_ne_top
  have hbudget := enlarged_density_budget hd hd1 hcp hρp.le hω hβ hη hηω hηβ hb ha hsmall
  have hdense : O (d^(-ω/2))*volume (P (10000*a) B L z' e') ≤ ∑ i, volume (Q i) := by
    apply incidence_density_of_cardinal F Q hQfin _ hPfin (by positivity)
      (show 0 < 320000000000000000000*d*(L/c)^3 by dsimp [L]; positivity)
      (Real.rpow_nonneg hd.le _) hcard (fun i hi => (hgood i hi).1)
    rw [Measure.real, hPvol, ENNReal.toReal_ofReal (by positivity)]
    exact hbudget
  have hlongfactor : 10000000000 ≤ d^(-ω/100) := by
    have hbudget' := small_power_budget hd hd1 hsmall (by linarith : η/2 ≤ ω/100)
      (by norm_num : (0:ℝ) ≤ 10000000000) (by norm_num : (10000000000:ℝ) ≤ 10^40)
    have hprod : d^(ω/100)*d^(-ω/100) = 1 := by
      rw [← Real.rpow_add hd, show ω/100 + -ω/100 = 0 by ring, Real.rpow_zero]
    nlinarith [Real.rpow_pos_of_pos hd (-ω/100)]
  have haL : 10000*a ≤ (d^(-ω/100)*c)/1000000 := by
    have hh' := mul_le_mul_of_nonneg_right hlongfactor hcp.le
    have hac := hHB.2.1.trans hHB.2.2.1
    nlinarith
  have hbL : B ≤ L/100 := by
    have hh' : enlargedSlope (ρ*c) c ≤ 1/1000000 := min_le_right _ _
    dsimp [B]
    have hLp : 0 < L := hp.length_pos
    nlinarith
  have hactive (i) (hi : (Q i).Nonempty) : i ∈ F := by
    by_contra hh
    exact hi.ne_empty (hzero i hh)
  exact ⟨{
    coarse := k
    center := z'
    frame := e'
    shading := Q
    delta_le_thickness := hdA
    thickness_le_width := hAB
    width_le_length := hBL
    length_le_one := by have hh' := hp.output_length; linarith
    ten_length_le_one := hp.output_length
    thickness_small := haL
    width_small := hbL
    measurable := fun i => (hQ i).1
    subset := fun i => (hQ i).2.1
    in_tube := fun i => ((hQ i).2.1.trans inter_subset_left).trans ((hRZ i).trans (hZT i))
    in_ball := fun i => (hQ i).2.2
    endpoints := hends
    incidence := hdense
    tube_mass := fun i hi => (hgood i (hactive i hi)).1
    crossing := fun i hi => (hgood i (hactive i hi)).2
  }⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
