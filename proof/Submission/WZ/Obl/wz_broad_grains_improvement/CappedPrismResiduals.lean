-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedPrismResiduals.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.RoundedLocalPrism
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedResidualSelection
import Submission.WZ.Obl.wz_broad_grains_initialization.PolynomialCount
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RealMass

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms
  (G PrismPiece admissible_finite_mass admissible_real_mass_pos)
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale (dyExp)

/-- A stage-zero prism constructor on every half-mass residual automatically
supplies normalized caps. Its output length is fixed, while its radius may
vary above any prescribed lower bound. -/
theorem capped_prisms_of_residual_prisms {ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {ω ζ d h r₀ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ 1 → 0 ≤ ω*ζ/100 → ω*ζ/100 ≤ 1 →
      A d h (d^(-h)) (d^(-h)) n x v Y →
      (∀ i,MeasurableSet (Z i)) → (∀ i,Z i ⊆ Y i) →
      d^(ε/4)*(∑ i,volume.real (Y i)) ≤ ∑ i,volume.real (Z i) →
      (∀ R : Fin n → Set V, (∀ i,MeasurableSet (R i)) → (∀ i,R i ⊆ Z i) →
        (∑ i,volume.real (Z i))/2 ≤ ∑ i,volume.real (R i) →
        ∃ ρ, r₀ ≤ ρ ∧ G ω ζ d (ε/4) ρ c n x v R 0) →
      ∃ ρ, r₀ ≤ ρ ∧ ∃ P : PrismData n,
        P.Valid ω ζ d ε ρ c x v Y 0 ∧ P.HasCaps d ε ρ c := by
  obtain ⟨dP,hdP,HP⟩ := prism_width_class_budget (by positivity : 0<ε/4)
  obtain ⟨dC,hdC,_,HC⟩ := capped_stage_zero_of_good_selector hε (by norm_num : (0:ℝ)<4)
  obtain ⟨dK,hdK,HK⟩ :=
    WangZahlLot.Obl.wz_normalized_projection_coarse_fine.exists_power_absorption
      (C := 4) (p := ε/4) (r := 0) (by norm_num) (by positivity)
  refine ⟨min (1/100) (min dP (min dC dK)),by positivity,min_le_left _ _,?_⟩
  intro ω ζ d h r₀ c n x v Y Z hd hdd hh hβ hβ1 hA hZm hZY hretain hselect
  have hd100 := hdd.trans (min_le_left _ _)
  have hd1 : d ≤ 1 := hd100.trans (by norm_num)
  have hdP' := hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdC' := hdd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdK' := hdd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsmall : 4*d^(ε/4) ≤ 1 := by simpa only [Real.rpow_zero] using HK d hd hdK'
  have htwo : 2*d^(ε/4) ≤ 1 := by linarith [Real.rpow_nonneg hd.le (ε/4)]
  have htwo' : 2*d^(ε/2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith : ε/4≤ε/2)) (by norm_num)).trans htwo
  have hden : 4*d^(ε/2) ≤ d^(ε/4) := by
    calc
      _ = (4*d^(ε/4))*d^(ε/4) := by
        rw [mul_assoc,← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ _ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hd.le (ε/4))
  have hbr : 2*d^(-(ε/4)) ≤ d^(-(ε/2)) := by
    calc
      _ = (2*d^(ε/4))*d^(-(ε/2)) := by
        rw [mul_assoc,← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ _ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hd.le (-(ε/2)))
  let J := (dyExp 1 d+1)*(dyExp 1 d+1)
  have hJ : 0 < J := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hJbound : (J:ℝ) ≤ d^(-(ε/4)) := by
    simpa only [J,pow_two] using HP d hd hd1 hdP'
  have hbudget : 2*(J:ℝ)*d^ε ≤ d^(ε/4) := by
    calc
      _ ≤ 2*d^(-(ε/4))*d^ε :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJbound (by norm_num)) (by positivity)
      _ = (2*d^(ε/2))*d^(ε/4) := by
        rw [mul_assoc,← Real.rpow_add hd,mul_assoc,← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ _ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right htwo' (Real.rpow_nonneg hd.le (ε/4))
  have hn4 := WangZahlLot.Obl.wz_broad_grains_initialization.normalized_polynomial_count hd hd100 hh hA
  have hYfin := admissible_finite_mass hA
  have hYpos := admissible_real_mass_pos hd hA
  have hZpos : 0 < ∑ i,volume.real (Z i) :=
    (mul_pos (Real.rpow_pos_of_pos hd (ε/4)) hYpos).trans_le hretain
  let u : V := EuclideanSpace.single 2 1
  let valid : Fin J → Prop := fun k => r₀ ≤ transverseRadiusPalette d c k
  obtain ⟨k,hk,P,HP,Hcaps⟩ := HC hJ valid hd hdC' le_rfl hn4 hYfin hZm hZY hYpos
    hretain hbudget (N := 1) (y := fun _ => 0) (w := fun _ => u) (s := 1)
    (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
    (by intro k; simp [u]) (a := fun k => (transverseWidthPalette d c k).1)
    (c := fun _ => c) (ρ := transverseRadiusPalette d c) (by
      intro R hRm hRZ hRmass
      have hRfin (i) : volume (R i) ≠ ⊤ := measure_ne_top_of_subset ((hRZ i).trans (hZY i)) (hYfin i)
      have hRpos : 0 < ∑ i,volume (R i) := by
        have hp : 0 < (∑ i,volume (R i)).toReal := by
          rw [ENNReal.toReal_sum (fun i _ => hRfin i)]
          exact (half_pos hZpos).trans_le hRmass
        exact (ENNReal.toReal_pos_iff.mp hp).1
      obtain ⟨ρ,hρ,hG⟩ := hselect R hRm hRZ hRmass
      obtain ⟨B,HB,hρB,hBR⟩ := good_piece_in_width_palette_of_prisms u hd hd1
        (by positivity : 0≤ε/4) hβ hβ1 (fun i => (hA.2.1 i).2.1) hRpos hden hbr hG
      exact ⟨B,HB,hρ.trans hρB,hBR⟩)
  exact ⟨_,hk,P,HP,Hcaps⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
