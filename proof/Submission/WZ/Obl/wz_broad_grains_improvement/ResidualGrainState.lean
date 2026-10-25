-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.ResidualGrainState.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.RefinedGrainState
import Submission.WZ.Obl.wz_broad_grains_improvement.HalfResidualRefinement
import Submission.WZ.Obl.wz_broad_grains_improvement.LongLevelTerminal
import Submission.WZ.Obl.wz_broad_grains_initialization.PolynomialCount
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.DyadicPower
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Budgets

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Broad)

/-- Every half-mass fine residual can be restored to the complete old grain
geometry. Only the error changes; the original fine axes, coarse cover,
dimensions and local convex coefficient are all retained. -/
theorem residual_grain_state_of_budgets
    {ω ζ d h ε τ ρ a c b g : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ ε)
    (hA : A d h (d^(-h)) (d^(-h)) n x v Y)
    (hC : C d h n x v Y S Z ρ N y w f True)
    (hBr : Broad ω ζ d h ρ n N v S Z f)
    (hH : H d h n x v S Z ρ N y w f a c b g)
    (hlog : 4*((Nat.log 2 n+1:ℕ):ℝ)*d^τ ≤ 1)
    (hbudget : d^ε ≤ (d^τ/2)*d^h)
    (hbrbudget : 4*d^(-h) ≤ d^(-ε))
    (hAbudget : 2*d^ε ≤ d^(2*h))
    (R : Fin n → Set V) (hRm : ∀ i, MeasurableSet (R i)) (hRZ : ∀ i,R i ⊆ Z i)
    (hretain : (1/2:ENNReal)*∑ i,volume (Z i) ≤ ∑ i,volume (R i)) :
    A d ε (d^(-ε)) (d^(-ε)) n x v R ∧
    ∃ W : Fin n → Set V,
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ R i) ∧
      O (d^τ)*∑ i,volume (Z i) ≤ ∑ i,volume (W i) ∧
      C d ε n x v Y S W ρ N y w f True ∧
      C d ε n x v R S W ρ N y w f True ∧
      Broad ω ζ d ε ρ n N v S W f ∧ H d ε n x v S W ρ N y w f a c b g := by
  have hRY (i) : R i ⊆ Y i := (hRZ i).trans (hC.1 i).2.1
  have hZfin (i) : volume (Z i) ≠ ⊤ := measure_ne_top_of_subset
    (((hC.1 i).2.1.trans (hA.2.1 i).2.2.2).trans (hA.2.1 i).2.1)
    (measure_ball_lt_top (μ := volume) (x := (0:V)) (r := 1)).ne
  have hZm (i) : MeasurableSet (Z i) := (hC.1 i).1
  have hZoff (i) : i ∉ S → Z i = ∅ := (hC.1 i).2.2
  have hZsum : (∑ i ∈ S,volume (Z i)) = ∑ i,volume (Z i) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [hZoff i hi]
  have hbase : O (d^(2*h)*n*d^2) ≤ ∑ i,volume (Z i) := by
    calc
      _ = O (d^h)*O (d^h*n*d^2) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le h),
          show 2*h=h+h by ring,Real.rpow_add hd]
        congr 1
        ring
      _ ≤ O (d^h)*∑ i,volume (Y i) := mul_le_mul' le_rfl hA.2.2.2.1
      _ ≤ _ := by simpa only [hZsum] using hC.2.1
  have hAm := admissible_mono hd hd1 hh hA
  have hAR : A d ε (d^(-ε)) (d^(-ε)) n x v R := by
    refine ⟨hA.1,fun i => ⟨(hA.2.1 i).1,(hA.2.1 i).2.1,hRm i,
      (hRY i).trans (hA.2.1 i).2.2.2⟩,hA.2.2.1,?_,hAm.2.2.2.2⟩
    apply le_trans (b := (1/2:ENNReal)*O (d^(2*h)*n*d^2))
    · rw [show (1/2:ENNReal)=O (1/2) by
          norm_num [O,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)],
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/2)]
      apply ENNReal.ofReal_le_ofReal
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [mul_le_mul_of_nonneg_right hAbudget (show 0≤(n:ℝ)*d^2 by positivity)]
    · exact (mul_le_mul' le_rfl hbase).trans hretain
  obtain ⟨W,m',hm',hW,hWmass,hWfrac,hWlevel⟩ :=
    half_residual_uniform_refinement S f hZm hRm hZfin hRZ hZoff hretain
  have hmass : O (d^τ)*∑ i,volume (Z i) ≤ ∑ i,volume (W i) := by
    have hKpos : (0:ENNReal) < (Nat.log 2 n+1:ℕ) := by exact_mod_cast Nat.succ_pos (Nat.log 2 n)
    apply (ENNReal.mul_le_mul_iff_right hKpos.ne' (by simp)).mp
    calc
      (Nat.log 2 n+1:ℕ)*(O (d^τ)*∑ i,volume (Z i))
          ≤ O (1/4)*∑ i,volume (Z i) := by
        rw [← mul_assoc,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
        apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        linarith
      _ ≤ _ := hWmass
  obtain ⟨L,z,e,G,γ,m,hHB⟩ := H_iff.mp hH
  have hm : 0 < m := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2)
    (half_le_grain_level hd hA hC hHB)
  have hρ : 0 < ρ := by
    have ha := hd.trans_le hHB.1
    have hac := ha.trans_le hHB.2.1
    have hc := hac.trans_le hHB.2.2.1
    exact pos_of_mul_pos_left hac hc.le
  obtain ⟨hC',hBr',hH'⟩ := shading_refine_stage_data hd hd1 hρ hh hm
    (Real.rpow_nonneg hd.le τ) hC hBr hHB (fun i => (hW i).1)
    (fun i => (hW i).2.1.trans (hRZ i)) hmass hbudget hWfrac hbrbudget hWlevel
  have hCR : C d ε n x v R S W ρ N y w f True := by
    refine ⟨fun i => ⟨(hW i).1,(hW i).2.1,(hW i).2.2⟩,?_,hC'.2.2⟩
    exact (mul_le_mul' le_rfl (Finset.sum_le_sum (fun i _ => measure_mono (hRY i)))).trans hC'.2.1
  exact ⟨hAR,W,fun i => ⟨(hW i).1,(hW i).2.1⟩,hmass,hC',hCR,hBr',hH'⟩

/-- Restoring a half-mass residual costs arbitrarily little error, uniformly in
all the fine and coarse indices and in the grain dimensions. -/
theorem residual_grain_state {ε : ℝ} (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {ω ζ d h ρ a c b g : ℝ} {n N : ℕ}
        {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
        {y w : Fin N → V} {f : Fin n → Fin N},
      0 < d → d ≤ d₀ → h ≤ η →
      A d h (d^(-h)) (d^(-h)) n x v Y →
      C d h n x v Y S Z ρ N y w f True → Broad ω ζ d h ρ n N v S Z f →
      H d h n x v S Z ρ N y w f a c b g →
      ∀ R : Fin n → Set V, (∀ i, MeasurableSet (R i)) → (∀ i,R i ⊆ Z i) →
      (1/2:ENNReal)*∑ i,volume (Z i) ≤ ∑ i,volume (R i) →
      A d ε (d^(-ε)) (d^(-ε)) n x v R ∧
      ∃ W : Fin n → Set V,
        (∀ i, MeasurableSet (W i) ∧ W i ⊆ R i) ∧
        O (d^(ε/4))*∑ i,volume (Z i) ≤ ∑ i,volume (W i) ∧
        C d ε n x v Y S W ρ N y w f True ∧
        C d ε n x v R S W ρ N y w f True ∧
        Broad ω ζ d ε ρ n N v S W f ∧ H d ε n x v S W ρ N y w f a c b g := by
  obtain ⟨dL,hdL,HL⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.logarithmic_count_power
      (by norm_num : (0:ℝ)<4) (by positivity : 0<ε/8)
  obtain ⟨dC,hdC,HC⟩ :=
    WangZahlLot.Obl.wz_normalized_projection_coarse_fine.exists_power_absorption
      (C := 4) (p := ε/8) (r := 0) (by norm_num) (by positivity)
  refine ⟨min (ε/8) 1,min (1/100) (min dL dC),by positivity,
    (min_le_left _ _).trans (by linarith),by positivity,min_le_left _ _,?_⟩
  intro ω ζ d h ρ a c b g n N x v Y Z S y w f hd hdd hh hA hC hBr hH R hRm hRZ hretain
  have hd100 := hdd.trans (min_le_left _ _)
  have hd1 : d ≤ 1 := hd100.trans (by norm_num)
  have hhε : h ≤ ε/8 := hh.trans (min_le_left _ _)
  have hn4 := WangZahlLot.Obl.wz_broad_grains_initialization.normalized_polynomial_count
    hd hd100 (hh.trans (min_le_right _ _)) hA
  have hlog := HL d hd (hdd.trans ((min_le_right _ _).trans (min_le_left _ _))) n hn4
  have hsmall : 4*d^(ε/8) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      HC d hd (hdd.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpower {p r : ℝ} (hpr : ε/8 ≤ p-r) : 4*d^p ≤ d^r := by
    calc
      _ = (4*d^(p-r))*d^r := by
        rw [mul_assoc,← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ 1*d^r := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hd hd1 hpr) (by norm_num)).trans hsmall)
        (Real.rpow_nonneg hd.le r)
      _ = _ := one_mul _
  apply residual_grain_state_of_budgets hd hd1 (by linarith) hA hC hBr hH
    (τ := ε/4) ?_ ?_ ?_ ?_ R hRm hRZ hretain
  · calc
      _ ≤ 4*d^(-(ε/8))*d^(ε/4) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hlog) (by norm_num)) (by positivity)
      _ = 4*d^(ε/8) := by
        rw [mul_assoc,← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ 1 := hsmall
  · have hp := hpower (p := ε) (r := ε/4+h) (by linarith)
    rw [Real.rpow_add hd] at hp
    nlinarith [Real.rpow_nonneg hd.le ε]
  · exact hpower (by linarith)
  · have hp := hpower (p := ε) (r := 2*h) (by linarith)
    linarith [Real.rpow_nonneg hd.le ε]

end WangZahlLot.Obl.wz_broad_grains_improvement
