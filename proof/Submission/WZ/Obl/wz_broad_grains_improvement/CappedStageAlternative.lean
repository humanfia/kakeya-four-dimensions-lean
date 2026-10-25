-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedStageAlternative.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedPrismResiduals
import Submission.WZ.Obl.wz_broad_grains_improvement.ResidualStage
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.DensityMass

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms
  (G admissible_finite_mass half_mass_of_real)
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- A geometric stage-two alternative may be rerun on every substantial
residual. Gains and terminal states return to the original family; otherwise
the uncapped prism outputs automatically give a capped original family. -/
theorem capped_prisms_of_stage_alternative {ε θ : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθε : θ ≤ ε/4) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ θ ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {σ ω ζ α κ d h ρ c r₀ c₀ : ℝ} {n : ℕ}
        {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ η → 0 ≤ ω*ζ/100 → ω*ζ/100 ≤ 1 →
      A d h (d^(-h)) (d^(-h)) n x v Y → J ω ζ d h ρ c n x v Y 2 →
      (∀ R : Fin n → Set V,
        A d θ (d^(-θ)) (d^(-θ)) n x v R → J ω ζ d θ ρ c n x v R 2 →
        O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,R i) ∨
          (∃ ρ' c',J ω ζ d (ε/4) ρ' c' n x v R 3) ∨
          ∃ ρ', r₀ ≤ ρ' ∧ G ω ζ d (ε/4) ρ' c₀ n x v R 0) →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        (∃ ρ' c',J ω ζ d ε ρ' c' n x v Y 3) ∨
        ∃ ρ', r₀ ≤ ρ' ∧ ∃ P : PrismData n,
          P.Valid ω ζ d ε ρ' c₀ x v Y 0 ∧ P.HasCaps d ε ρ' c₀ := by
  obtain ⟨ηR,dR,hηR,hηRθ,hdR,_,HR⟩ := residual_stage hθ
  obtain ⟨dC,hdC,hdC100,HC⟩ := capped_prisms_of_residual_prisms hε
  obtain ⟨dK,hdK,HK⟩ :=
    WangZahlLot.Obl.wz_normalized_projection_coarse_fine.exists_power_absorption
      (C := 2) (p := ε/2) (r := 0) (by norm_num) (by positivity)
  refine ⟨min ηR 1,min dC (min dR dK),by positivity,
    (min_le_left _ _).trans hηRθ,by positivity,(min_le_left _ _).trans hdC100,?_⟩
  intro σ ω ζ α κ d h ρ c r₀ c₀ n x v Y hd hdd hh hβ hβ1 hA hJ hlocal
  have hdC' := hdd.trans (min_le_left _ _)
  have hdR' := hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdK' := hdd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 : d ≤ 1 := (hdC'.trans hdC100).trans (by norm_num)
  have hhR := hh.trans (min_le_left _ _)
  have hhε : h ≤ ε/4 := (hhR.trans hηRθ).trans hθε
  have hsmall : 2*d^(ε/2) ≤ 1 := by simpa only [Real.rpow_zero] using HK d hd hdK'
  have hbudget : d^ε ≤ (d^h/2)*d^(ε/4) := by
    have hp : 2*d^ε ≤ d^(ε/2) := by
      calc
        _ = (2*d^(ε/2))*d^(ε/2) := by
          rw [mul_assoc,← Real.rpow_add hd]
          congr 2
          ring
        _ ≤ _ := by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hd.le (ε/2))
    have hpow := Real.rpow_le_rpow_of_exponent_ge hd hd1
      (by linarith : h+ε/4≤ε/2)
    rw [Real.rpow_add hd] at hpow
    nlinarith
  classical
  by_cases hg : O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i)
  · exact Or.inl hg
  by_cases ht : ∃ ρ' c',J ω ζ d ε ρ' c' n x v Y 3
  · exact Or.inr (Or.inl ht)
  refine Or.inr (Or.inr ?_)
  obtain ⟨Z,hZ,hZmass,HZ⟩ := HR hd hdR' hhR hA hJ
  have hYfin := admissible_finite_mass hA
  have hZfin (i) : volume (Z i) ≠ ⊤ := measure_ne_top_of_subset (hZ i).2 (hYfin i)
  have hretain : d^(ε/4)*(∑ i,volume.real (Y i)) ≤ ∑ i,volume.real (Z i) := by
    have hm := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hZfin i)) hZmass
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.rpow_nonneg hd.le h),
      ENNReal.toReal_sum (fun i _ => hYfin i),ENNReal.toReal_sum (fun i _ => hZfin i)] at hm
    exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hd hd1 hhε)
      (Finset.sum_nonneg (fun i _ => measureReal_nonneg))).trans hm
  apply HC hd hdC' (hh.trans (min_le_right _ _)) hβ hβ1 hA
    (fun i => (hZ i).1) (fun i => (hZ i).2) hretain
  intro R hRm hRZ hRmass
  have hRY (i) : R i ⊆ Y i := (hRZ i).trans (hZ i).2
  have hRfin (i) : volume (R i) ≠ ⊤ := measure_ne_top_of_subset (hRY i) (hYfin i)
  have hhalf := half_mass_of_real hZfin hRfin hRmass
  obtain ⟨hAR,hJR⟩ := HZ R hRm hRZ hhalf
  rcases hlocal R hAR hJR with hgR | htR | hpR
  · exact (hg (hgR.trans (measure_mono (iUnion_mono hRY)))).elim
  · obtain ⟨ρ',c',hJR'⟩ := htR
    have hmass : O (d^h/2)*∑ i,volume (Y i) ≤ ∑ i,volume (R i) := by
      calc
        _ = (1/2:ENNReal)*(O (d^h)*∑ i,volume (Y i)) := by
          dsimp only [O]
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
          norm_num only [ENNReal.ofReal_ofNat]
          simp only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,one_mul]
        _ ≤ (1/2:ENNReal)*∑ i,volume (Z i) := mul_le_mul' le_rfl hZmass
        _ ≤ _ := hhalf
    exact (ht ⟨ρ',c',stage_of_retained_source hd hd1 (by linarith) (by positivity)
      hRY hmass hbudget hJR'⟩).elim
  · exact hpR

end WangZahlLot.Obl.wz_broad_grains_improvement
