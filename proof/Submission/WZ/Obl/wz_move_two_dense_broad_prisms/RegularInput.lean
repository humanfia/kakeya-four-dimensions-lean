-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.RegularInput.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PreparedDense
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PreparationFinite
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RegularPowers

/-! A dense local prism with a globally regular shading available for extension. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- The enlarged-prism input can be extracted inside one shading that remains
regular at every prescribed extension radius. -/
theorem regular_dense_prism_in_residual {ω ζ η b d h ρ a c g : ℝ} {n N J : ℕ} (hJ : 0 < J)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hη : 0 < η)
    (hηω : η ≤ ω/1000) (hηβ : η ≤ (ω*ζ/100)*ω/1000) (hb : b ≤ ω/1000)
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ η/8)
    (hsmall : (10:ℝ)^40*d^(η/4) ≤ 1)
    (radii : Fin J → ℝ) (hr : ∀ j, 0 < radii j) (hr1 : ∀ j, radii j ≤ 1)
    (hdr : ∀ j, d ≤ radii j/8) (j₀ : Fin J) (hr₀ : radii j₀ = (d^(-ω/100)*c)/8)
    (hpalette : (J:ℝ)*d^η ≤ d^(η/2))
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
    ∃ U : Fin n → Set V,
      (∀ i, MeasurableSet (U i) ∧ U i ⊆ R i) ∧
      (∀ i p, p ∈ U i → d^(ω/1000) < dist p (x i) ∧ d^(ω/1000) < dist p (x i+v i)) ∧
      (∀ i p, p ∈ U i → ∀ j, O (d^η*radii j*d^2/32) ≤ volume (U i ∩ ball p (radii j))) ∧
      Nonempty (DensePrismInput ω d (d^η) (10000*a)
        (10000*enlargedSlope (ρ*c) c*(d^(-ω/100)*c)) (d^(-ω/100)*c) ρ x v y w U) := by
  obtain ⟨J₀, z, e, G, γ, m₀, hHB⟩ := wz_move_two_long_grains_gain.H_iff.mp hH
  have hdc : d ≤ c := hHB.1.trans (hHB.2.1.trans hHB.2.2.1)
  have hcp : 0 < c := hd.trans_le hdc
  have hρ1 : ρ ≤ 1 := (mul_le_mul_iff_left₀ hcp).mp (by simpa using hHB.2.2.1)
  have hs0 : (10:ℝ)^40*d^((η/2)/2) ≤ 1 := by
    convert hsmall using 1 <;> congr 1 <;> ring
  have hs1 : (10:ℝ)^40*d^(η/2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hd hd1
      (by linarith : η/4 ≤ η/2)) (by positivity)).trans hsmall
  have hp0 := prep_powers hω hω1 (by positivity : 0 < ω*ζ/100)
    (by positivity : 0 < η/2) (by linarith : η/2 ≤ ω/1000)
    (by nlinarith : η/2 ≤ (ω*ζ/100)*ω/1000) hd hd1
    (by linarith : h ≤ (η/2)/4) hs0 hρ hρ1 hdc hc
  obtain ⟨hdR, hend, hLR, _⟩ := regular_endpoint_budgets hd hd1 hω hω1 hη hηω hc hsmall
  have hZT (i) : Z i ⊆ T d (x i) (v i) := (hC.1 i).2.1.trans (hA.2.1 i).2.2.2
  have hZfin (i) : volume (Z i) ≠ ∞ := measure_ne_top_of_subset (hC.1 i).2.1 (admissible_finite_mass hA i)
  have hRfin (i) : volume (R i) ≠ ∞ := measure_ne_top_of_subset (hRZ i) (hZfin i)
  have hZmass : O (32*d^(η/2)*(n:ℝ)*d^2) ≤ ∑ i, volume (Z i) := by
    refine (ENNReal.ofReal_le_ofReal ?_).trans (cover_incidence_lower hd hA hC)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp0.mass_cost (Nat.cast_nonneg n)) (sq_nonneg d)
  obtain ⟨U, W, hU, hW, hends, hreg, hmass, hcount⟩ := prepare_dense_residual_finite
    hJ radii hd hr hr1 hdr hdR hend (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos hd _)
    hpalette x v (fun i => (hA.2.1 i).1) f Z R (fun i => (hC.1 i).1) hRm hZT hRZ
    (half_mass_of_real hZfin hRfin hRmass) hZmass
  refine ⟨U, hU, hends, hreg, ?_⟩
  apply dense_prism_of_prepared_fibres hω hω1 hζ hη hηω hηβ hb hd hd1
    (by linarith : h ≤ η/4) hs1 x v Y hA S Z y w f hC hH hBr hρ ha hc hhigh
    U W (fun i => (hU i).1) (fun i => (hW i).1) (fun i => (hU i).2.trans (hRZ i))
    (fun i => (hW i).2) ?_ ?_ hmass hcount
  · intro i p hp
    exact ⟨hLR.trans_lt (hends i p hp).1, hLR.trans_lt (hends i p hp).2⟩
  · intro i p hp
    have hh' := hreg i p hp j₀
    rw [hr₀] at hh'
    convert hh' using 1 <;> congr 1 <;> ring

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
