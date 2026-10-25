-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedLengthening.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedResidualSelection
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Lengthening
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainCardinality
import Submission.WZ.Obl.wz_tower_balanced_refinement.Arithmetic

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms
  (Broad PrismPiece lengthening_parameters high_multiplicity_grains_very_short
   uniform_geometric_cutoffs prep_powers palette_count_budget radiusPalette_bounds
   regular_dense_prism_in_residual regular_dense_local_selector radiusPalette
   broadnessPalette lengthPalette thicknessPalette admissible_finite_mass
   admissible_real_mass_pos cover_real_retention)
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- The actual dense broad lengthening construction supplies normalized caps
when its local outputs are capped before residual extraction. -/
theorem capped_dense_broad_lengthening {ω ζ ε : ℝ}
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) (hε : 0 < ε) :
    ∃ b η d₀ : ℝ, 0 < b ∧ b ≤ 1 ∧ 0 < η ∧ η ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ η → A d h (d^(-h)) (d^(-h)) n x v Y →
      ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ)
        (y w : Fin N → V) (f : Fin n → Fin N) (a c g : ℝ),
      C d h n x v Y S Z ρ N y w f True → Broad ω ζ d h ρ n N v S Z f →
      H d h n x v S Z ρ N y w f a c 0 g →
      d^(ω/100) < ρ → a < 2*d^(1-b) →
      (∀ k p, (∃ i ∈ S, f i=k ∧ p ∈ Z i) →
        d^(-(24*ω/25)) < q n {i | i ∈ S ∧ f i=k ∧ p ∈ Z i}) →
      ∃ ρ' c', d^(1-ω/100) ≤ ρ' ∧ d^(-ω/150)*c ≤ c' ∧
        ∃ D : PrismData n, D.Valid ω ζ d ε ρ' c' x v Y 0 ∧ D.HasCaps d ε ρ' c' := by
  obtain ⟨par⟩ := lengthening_parameters hω hω1 hζ (half_pos hε)
  obtain ⟨ηS,dS,hηS,hdS,_,HS⟩ := high_multiplicity_grains_very_short hω hω1
  obtain ⟨dG,hdG,hdG100,HG⟩ := uniform_geometric_cutoffs par.eta_pos (half_pos hε)
  obtain ⟨dC,hdC,_,HC⟩ := capped_stage_zero_of_good_selector hε (by norm_num : (0:ℝ)<5)
  have hparη := par.eta_pos
  let η := min ηS (min (par.eta/8) (min 1 ε))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηS' : η ≤ ηS := min_le_left _ _
  have hηpar : η ≤ par.eta/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηε : η ≤ ε := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨par.thin,η,min dG (min dS dC),par.thin_pos,par.thin_le_one,hη,hηε,
    by positivity,(min_le_left _ _).trans hdG100,?_⟩
  intro d h n x v Y hd hdd hh hA S Z ρ N y w f a c g hC hBr hH hρ ha hhigh
  have hdG' := hdd.trans (min_le_left _ _)
  have hdS' := hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdC' := hdd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd100 := hdG'.trans hdG100
  have hd1 : d ≤ 1 := hd100.trans (by norm_num)
  have hhpar := hh.trans hηpar
  have hcshort := HS d h hd hdS' (hh.trans hηS') n x v Y hA S Z ρ N y w f a c g hC hH hhigh
  have hn5 : (n:ℝ) ≤ d^(-(5:ℝ)) := by
    have hncount := WangZahlLot.Obl.wz_clustered_cover_volume_gain.admissible_count_eight hd hA
    have hn := WangZahlLot.Obl.wz_tower_balanced_refinement.cardinal_lt_power
      (q := 1) (ε := 5) hd hd1 (hh.trans hη1) (by norm_num : (0:ℝ)≤8)
      (by linarith : 8*d<1) (by norm_num : (4:ℝ)<5*(1:ℕ))
      (by simpa only [mul_comm] using hncount)
    simpa only [pow_one] using hn.le
  obtain ⟨hsmall,hlog,K,hdK,hK2,hcount⟩ := HG d hd hdG'
  have hdc : d ≤ c := by
    obtain ⟨L,z,e,B,γ,m,hda,hab,hbc,_⟩ := hH
    exact hda.trans (hab.trans hbc)
  have hcpos : 0 < c := hd.trans_le hdc
  have hρ1 : ρ ≤ 1 := by
    obtain ⟨L,z,e,B,γ,m,hda,hab,hbc,_⟩ := hH
    nlinarith only [hbc,hcpos]
  have hβ : 0 < ω*ζ/100 := by positivity
  have hsmall' : (10:ℝ)^40*d^(par.eta/2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hd hd1
      (by linarith [par.eta_pos] : par.eta/4 ≤ par.eta/2)) (by positivity)).trans hsmall
  have hprep := prep_powers hω hω1 hβ par.eta_pos par.eta_omega par.eta_beta_omega
    hd hd1 (by linarith : h≤par.eta/4) hsmall' hρ.le hρ1 hdc hcshort
  have hpalette := palette_count_budget hd hd1 par.eta_pos par.eta_epsilon hsmall hcount
  have hradii := radiusPalette_bounds (K := K) hd hd100
    hprep.length_pos hprep.length_small hprep.radius_small
  let valid : Fin ((K+1)+(K+1)) → Prop := fun k =>
    d^(1-ω/100) ≤ broadnessPalette d a (d^(-ω/100)*c) K k ∧
      d^(-ω/150)*c ≤ lengthPalette d (d^(-ω/100)*c) K k
  have hretain : d^(ε/4)*(∑ i,volume.real (Y i)) ≤ ∑ i,volume.real (Z i) :=
    cover_real_retention hd hd1 (by linarith [par.eta_epsilon] : h≤ε/4) hA hC
  have hbudget : 2*(((K+1)+(K+1):ℕ):ℝ)*d^ε ≤ d^(ε/4) := by
    have hp := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (show ε/2≤ε by linarith))
      (by positivity : (0:ℝ)≤2*((K+1)+(K+1):ℕ))
    apply hp.trans
    convert hpalette.2.2 using 1 <;> congr 1 <;> ring
  obtain ⟨k,hk,D,HD,Hcaps⟩ := HC (by omega : 0<(K+1)+(K+1)) valid hd hdC' le_rfl hn5
    (admissible_finite_mass hA) (fun i => (hC.1 i).1) (fun i => (hC.1 i).2.1)
    (admissible_real_mass_pos hd hA) hretain hbudget hC.2.2.2.2.2.2.2.1 hC.2.2.1 (by
      intro R hRm hRZ hRmass
      obtain ⟨U,hU,hends,hreg,⟨B⟩⟩ := regular_dense_prism_in_residual
        (by omega : 0<K+2) hω hω1 hζ par.eta_pos par.eta_omega par.eta_beta_omega par.thin_omega
        hd hd1 hhpar hsmall (radiusPalette d (d^(-ω/100)*c) K)
        hradii.1 hradii.2.1 hradii.2.2 0 rfl hpalette.1 x v Y hA S Z y w f hC hH hBr
        hρ.le ha.le hcshort (fun k p hp => by
          have hh' := (hhigh k p hp).le
          convert hh' using 1 <;> congr 1 <;> ring) R hRm hRZ hRmass
      obtain ⟨Q,HQ,hQU,hbase,hlength⟩ := regular_dense_local_selector par hω hω1 hζ hζω (half_pos hε)
        hd hd100 hhpar hdc hcshort ha.le hsmall hlog hdK hK2 hcount
        x v (fun i => (hA.2.1 i).1) hA.1 y w U (fun i => (hU i).1)
        (fun i => (hU i).2.trans ((hRZ i).trans ((hC.1 i).2.1.trans (hA.2.1 i).2.2.2)))
        hends hreg B hA.2.2.2.2.1
      exact ⟨Q,HQ,⟨hbase,hlength⟩,fun i => (hQU i).trans (hU i).2⟩)
  exact ⟨_,_,hk.1,hk.2,D,HD,Hcaps⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
