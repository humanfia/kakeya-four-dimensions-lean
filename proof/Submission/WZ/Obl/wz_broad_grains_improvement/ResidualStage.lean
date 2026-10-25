-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.ResidualStage.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.ResidualGrainState

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory

/-- All stopping conditions survive the residual-state restoration: none of
their scale, cardinality, or local-convex-count witnesses changes. -/
theorem residual_stage {ε : ℝ} (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {ω ζ d h ρ c : ℝ} {n j : ℕ}
        {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ η →
      A d h (d^(-h)) (d^(-h)) n x v Y → J ω ζ d h ρ c n x v Y j →
      ∃ Z : Fin n → Set V,
        (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
        O (d^h)*∑ i,volume (Y i) ≤ ∑ i,volume (Z i) ∧
        ∀ R : Fin n → Set V, (∀ i, MeasurableSet (R i)) → (∀ i,R i ⊆ Z i) →
          (1/2:ENNReal)*∑ i,volume (Z i) ≤ ∑ i,volume (R i) →
          A d ε (d^(-ε)) (d^(-ε)) n x v R ∧
            J ω ζ d ε ρ c n x v R j := by
  obtain ⟨η,d₀,hη,hηε,hd₀,hd₀100,H⟩ := residual_grain_state hε
  refine ⟨η,d₀,hη,hηε,hd₀,hd₀100,?_⟩
  intro ω ζ d h ρ c n j x v Y hd hdd hh hA hJ
  obtain ⟨S,Z,N,y,w,f,a,g,hC,hbase,hg,hBr,hH,hstop⟩ := hJ
  refine ⟨Z,fun i => ⟨(hC.1 i).1,(hC.1 i).2.1⟩,
    hC.2.1.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ S)),?_⟩
  intro R hRm hRZ hretain
  obtain ⟨hAR,W,hW,hWmass,hCY,hCR,hBr',hH'⟩ :=
    H hd hdd hh hA hC hBr hH R hRm hRZ hretain
  exact ⟨hAR,S,W,N,y,w,f,a,g,hCR,hbase,hg,hBr',hH',hstop⟩

/-- A cover relative to a retained shading becomes a cover relative to its
original source, after paying just the retained mass fraction. -/
theorem cover_of_retained_source {d h h' t ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y R Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {b : Prop}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h') (ht : 0 ≤ t)
    (hRY : ∀ i,R i ⊆ Y i) (hretain : O t*∑ i,volume (Y i) ≤ ∑ i,volume (R i))
    (hbudget : d^h' ≤ t*d^h) (hC : C d h n x v R S Z ρ N y w f b) :
    C d h' n x v Y S Z ρ N y w f b := by
  refine ⟨fun i => ⟨(hC.1 i).1,(hC.1 i).2.1.trans (hRY i),(hC.1 i).2.2⟩,
    ?_,(cover_mono hd hd1 hh hC).2.2⟩
  calc
    _ ≤ O (t*d^h)*∑ i,volume (Y i) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hbudget) le_rfl
    _ = O (d^h)*(O t*∑ i,volume (Y i)) := by
      dsimp only [O]
      rw [ENNReal.ofReal_mul ht,mul_comm (O t),mul_assoc]
    _ ≤ O (d^h)*∑ i,volume (R i) := mul_le_mul' le_rfl hretain
    _ ≤ _ := hC.2.1

/-- A state built on any substantial residual is still a state of the
original fine family; the stopping data and geometry are unchanged. -/
theorem stage_of_retained_source {ω ζ d h h' t ρ c : ℝ} {n j : ℕ}
    {x v : Fin n → V} {Y R : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h') (ht : 0 ≤ t)
    (hRY : ∀ i,R i ⊆ Y i) (hretain : O t*∑ i,volume (Y i) ≤ ∑ i,volume (R i))
    (hbudget : d^h' ≤ t*d^h) (hJ : J ω ζ d h ρ c n x v R j) :
    J ω ζ d h' ρ c n x v Y j := by
  obtain ⟨S,Z,N,y,w,f,a,g,hC,hbase,hg,hBr,hH,hstop⟩ := hJ
  refine ⟨S,Z,N,y,w,f,a,g,cover_of_retained_source hd hd1 hh ht hRY hretain hbudget hC,
    hbase,hg,?_,grains_mono hd hd1 hh hH,hstop⟩
  intro k p u r hu hdr hrρ
  have hr : 0 < r := hd.trans_le hdr
  have hρ : 0 < ρ := hr.trans_le hrρ
  apply (hBr k p u r hu hdr hrρ).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hh))
      (Real.rpow_nonneg (div_nonneg hr.le hρ.le) _)) (Nat.cast_nonneg _)

end WangZahlLot.Obl.wz_broad_grains_improvement
