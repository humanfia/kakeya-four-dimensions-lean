-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedCappedLengthening.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedLengthening
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedCappedCover
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedAllScaleState

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_multiscale_finite_tower (axisMidpoint)
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Broad)
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- The dense high-count regime on scalar-aligned fine axes yields either a
volume gain or a full grain state with a definite increase in length. -/
theorem aligned_capped_lengthening_state {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) (hε : 0 < ε) :
    ∃ b α κ η d₀ : ℝ, 0 < b ∧ b ≤ 1 ∧ 0 < α ∧ 0 < κ ∧
      0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
        {u : V} {t : ℝ},
      0 < d → d ≤ d₀ → h ≤ η → A d h (d^(-h)) (d^(-h)) n x v Y →
      (∀ i, ‖v i-u‖ ≤ 1/10) →
      (∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1) →
      (∀ i, inner ℝ (v i) (axisMidpoint (x i) (v i)) = t) →
      ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ)
        (y w : Fin N → V) (f : Fin n → Fin N) (a c g : ℝ),
      C d h n x v Y S Z ρ N y w f True → Broad ω ζ d h ρ n N v S Z f →
      H d h n x v S Z ρ N y w f a c 0 g →
      d^(ω/100) < ρ → a < 2*d^(1-b) →
      (∀ k p, (∃ i ∈ S, f i=k ∧ p ∈ Z i) →
        d^(-(24*ω/25)) < q n {i | i ∈ S ∧ f i=k ∧ p ∈ Z i}) →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        ∃ ρ' c', d^(-ω/200)*c ≤ c' ∧ J ω ζ d ε ρ' c' n x v Y 0 := by
  have hβ : 0 < ω*ζ/100 := by positivity
  have hβ1 : ω*ζ/100 ≤ 1 := by nlinarith
  obtain ⟨α,κ,ηS,dS,hα,hκ,hηS,hηSε,hdS,hdS100,HS⟩ :=
    capped_prisms_gain_or_state hσ hσ2 hω hω1 hE hζ hζω hε
      (by positivity : 0 < ω/1200)
  obtain ⟨ηC,dC,hηC,hηCS,hdC,hdC100,HC⟩ :=
    aligned_exact_capped_prism_cover (τ := ω/100)
      (by positivity) (by linarith) hβ hβ1 hηS
  obtain ⟨b,ηL,dL,hb,hb1,hηL,_,hdL,_,HL⟩ :=
    capped_dense_broad_lengthening hω hω1 hζ hζω hηC
  refine ⟨b,α,κ,min ηS (min ηC ηL),min dS (min dC dL),hb,hb1,hα,hκ,
    by positivity,(min_le_left _ _).trans hηSε,
    by positivity,(min_le_left _ _).trans hdS100,?_⟩
  intro d h n x v Y u t hd hdd hh hA hcap hmid halign S Z ρ N y w f a c g
    hC hBr hH hρ ha hhigh
  have hdS' := hdd.trans (min_le_left _ _)
  have hdC' := hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdL' := hdd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hhS := hh.trans (min_le_left _ _)
  have hhC := hh.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhL := hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 : d ≤ 1 := (hdS'.trans hdS100).trans (by norm_num)
  obtain ⟨ρ₁,c₁,hbase,hlength,D,HD,Hcaps⟩ := HL hd hdL' hhL hA
    S Z ρ N y w f a c g hC hBr hH hρ ha hhigh
  have hAC : A d ηC (d^(-ηC)) (d^(-ηC)) n x v Y := admissible_mono hd hd1 hhC hA
  obtain ⟨ρ₂,hρ₂,D₂,HD₂,Hcaps₂,_⟩ := HC hd hdC' hηC.le le_rfl
    hAC hcap hmid halign ρ₁ c₁ hbase D HD Hcaps
  have hAS : A d ηS (d^(-ηS)) (d^(-ηS)) n x v Y := admissible_mono hd hd1 hhS hA
  rcases HS hd hdS' le_rfl hAS ρ₂ c₁ D₂ HD₂ Hcaps₂ (hbase.trans hρ₂) with hg | hs
  · exact Or.inl hg
  · obtain ⟨ρ₃,c₃,_,hc₃,hJ⟩ := hs
    have hc : 0 ≤ c := by
      obtain ⟨L,z,e,B,γ,m,hda,hab,hbc,_⟩ := hH
      exact hd.le.trans (hda.trans (hab.trans hbc))
    have hgain : d^(-ω/200)*c ≤ d^(ω/1200)*c₁ := by
      calc
        _ ≤ d^(ω/1200-ω/150)*c := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)) hc
        _ = d^(ω/1200)*(d^(-ω/150)*c) := by
          rw [show ω/1200-ω/150 = ω/1200 + -ω/150 by ring, Real.rpow_add hd]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlength (by positivity)
    exact Or.inr ⟨ρ₃,c₃,hgain.trans hc₃,hJ⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
