-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.Lengthening.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.LocalSelector
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RegularInput
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.UniformCutoffs
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.VariableExtraction
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.VeryShortGrains

/-! Uniform dense broad lengthening and its finite residual iteration. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- In the thin, high-multiplicity regime the stage-zero lengthening conclusion
holds directly. The volume-gain alternative in the frozen theorem is unnecessary here. -/
theorem dense_broad_lengthening {ω ζ ε : ℝ}
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) (hε : 0 < ε) :
    ∃ b h₀ d₀ : ℝ, 0 < b ∧ b ≤ 1 ∧ 0 < h₀ ∧ 0 < d₀ ∧
    ∀ d h : ℝ, 0 < d → d ≤ d₀ → h ≤ h₀ →
    ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A d h (d^(-h)) (d^(-h)) n x v Y →
    ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ)
      (y w : Fin N → V) (f : Fin n → Fin N) (a c g : ℝ),
      C d h n x v Y S Z ρ N y w f True →
      Broad ω ζ d h ρ n N v S Z f →
      H d h n x v S Z ρ N y w f a c 0 g →
      d^(ω/100) < ρ → a < 2*d^(1-b) →
      (∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
        d^(-(24*ω/25)) < q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}) →
      ∃ ρ' c', d^(1-ω/100) ≤ ρ' ∧ d^(-ω/150)*c ≤ c' ∧
        G ω ζ d ε ρ' c' n x v Y 0 := by
  obtain ⟨par⟩ := lengthening_parameters hω hω1 hζ hε
  have hη := par.eta_pos
  obtain ⟨hs, ds, hhs, hds, hds100, hshort⟩ := high_multiplicity_grains_very_short hω hω1
  obtain ⟨dg, hdg, hdg100, hgeom⟩ := uniform_geometric_cutoffs par.eta_pos hε
  refine ⟨par.thin, min hs (par.eta/8), min ds dg,
    par.thin_pos, par.thin_le_one, lt_min hhs (by positivity), lt_min hds hdg, ?_⟩
  intro d h hd hdd hh n x v Y hA S Z ρ N y w f a c g hC hBr hH hρ ha hhigh
  have hdds : d ≤ ds := hdd.trans (min_le_left _ _)
  have hddg : d ≤ dg := hdd.trans (min_le_right _ _)
  have hd100 : d ≤ 1/100 := hddg.trans hdg100
  have hd1 : d ≤ 1 := hd100.trans (by norm_num)
  have hhe : h ≤ par.eta/8 := hh.trans (min_le_right _ _)
  have hc := hshort d h hd hdds (hh.trans (min_le_left _ _)) n x v Y hA
    S Z ρ N y w f a c g hC hH hhigh
  obtain ⟨hsmall, hlog, K, hdK, hK2, hcount⟩ := hgeom d hd hddg
  obtain ⟨J₀, z₀, e₀, G₀, γ₀, m₀, hHB⟩ := wz_move_two_long_grains_gain.H_iff.mp hH
  have hdc : d ≤ c := hHB.1.trans (hHB.2.1.trans hHB.2.2.1)
  have hcp : 0 < c := hd.trans_le hdc
  have hρ1 : ρ ≤ 1 := (mul_le_mul_iff_left₀ hcp).mp (by simpa using hHB.2.2.1)
  have hβ : 0 < ω*ζ/100 := by positivity
  have hs1 : (10:ℝ)^40*d^(par.eta/2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hd hd1
      (by linarith [par.eta_pos] : par.eta/4 ≤ par.eta/2)) (by positivity)).trans hsmall
  have hp := prep_powers hω hω1 hβ par.eta_pos par.eta_omega par.eta_beta_omega
    hd hd1 (by linarith : h ≤ par.eta/4) hs1 hρ.le hρ1 hdc hc
  have hpalette := palette_count_budget hd hd1 par.eta_pos par.eta_epsilon hsmall hcount
  have hradii := radiusPalette_bounds (K := K) hd hd100 hp.length_pos hp.length_small hp.radius_small
  let valid : Fin ((K+1)+(K+1)) → Prop := fun k =>
    d^(1-ω/100) ≤ broadnessPalette d a (d^(-ω/100)*c) K k ∧
      d^(-ω/150)*c ≤ lengthPalette d (d^(-ω/100)*c) K k
  have hselect : ∀ R : Fin n → Set V, (∀ i, MeasurableSet (R i)) →
      (∀ i, R i ⊆ Z i) → (∑ i, volume.real (Z i))/2 ≤ ∑ i, volume.real (R i) →
      ∃ Q : PrismPiece n N ((K+1)+(K+1)),
        Q.Good ω ζ d ε (thicknessPalette d a K Q.scale)
          (lengthPalette d (d^(-ω/100)*c) K Q.scale) ρ
          (broadnessPalette d a (d^(-ω/100)*c) K) x v y w ∧
        valid Q.scale ∧ ∀ i, Q.piece i ⊆ R i := by
    intro R hRm hRZ hRmass
    obtain ⟨U, hU, hends, hreg, ⟨B⟩⟩ := regular_dense_prism_in_residual
      (by omega : 0 < K+2) hω hω1 hζ par.eta_pos par.eta_omega par.eta_beta_omega par.thin_omega
      hd hd1 hhe hsmall (radiusPalette d (d^(-ω/100)*c) K)
      hradii.1 hradii.2.1 hradii.2.2 0 rfl hpalette.1 x v Y hA S Z y w f hC hH hBr
      hρ.le ha.le hc (fun k p hpk => by
        have hh' := (hhigh k p hpk).le
        convert hh' using 1 <;> congr 1 <;> ring) R hRm hRZ hRmass
    obtain ⟨Q, hQ, hQU, hQρ, hQc⟩ := regular_dense_local_selector par hω hω1 hζ hζω hε
      hd hd100 hhe hdc hc ha.le hsmall hlog hdK hK2 hcount x v (fun i => (hA.2.1 i).1)
      hA.1 y w U (fun i => (hU i).1)
      (fun i => (hU i).2.trans ((hRZ i).trans ((hC.1 i).2.1.trans (hA.2.1 i).2.2.2)))
      hends hreg B hA.2.2.2.2.1
    exact ⟨Q, hQ, ⟨hQρ, hQc⟩, fun i => (hQU i).trans (hU i).2⟩
  obtain ⟨k, hk, hG⟩ := stage_zero_of_variable_selector (by omega : 0 < (K+1)+(K+1)) valid
    hd (admissible_finite_mass hA) (fun i => (hC.1 i).1) (fun i => (hC.1 i).2.1)
    (admissible_real_mass_pos hd hA)
    (cover_real_retention hd hd1 (by linarith [par.eta_epsilon] : h ≤ ε/2) hA hC)
    hpalette.2.2 hC.2.2.2.2.2.2.2.1 hC.2.2.1 hselect
  exact ⟨_, _, hk.1, hk.2, hG⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
