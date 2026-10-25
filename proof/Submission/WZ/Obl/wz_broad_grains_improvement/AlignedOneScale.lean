-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedOneScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedTermination
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Proof
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.RefineCount
import Submission.WZ.Obl.wz_multiscale_finite_tower.Local
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Budgets

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory
open WangZahlLot.Obl.wz_multiscale_finite_tower (Factorization VolumeBound)

/-- The accepted one-scale conclusion, required only on aligned fine axes. -/
def AlignedOneScale (σ ω : ℝ) : Prop :=
  ∀ ζ : ℝ,0<ζ → ∃ α : ℝ,0<α ∧ ∃ κ : ℝ,0<κ ∧ ∃ η : ℝ,0<η ∧
    ∀ d : ℝ,0<d → d≤1/100 → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
    A d η (d^(-η)) (d^(-η)) n x v Y → AlignedAxes x v →
    VolumeBound σ ω κ α d n Y ∨ Factorization d d ζ ω n x v Y

/-- A restored grain configuration either has a heavy Katz--Tao subcover or
falls under the accepted clustered-cover volume gain. -/
theorem aligned_one_scale_of_grains {σ ω : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hGrains : ∀ h : ℝ,0<h → ∃ α : ℝ,0<α ∧ ∃ κ : ℝ,0<κ ∧ ∃ η : ℝ,0<η ∧ η≤h ∧
      ∀ d : ℝ,0<d → d≤1/100 → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
      A d η (d^(-η)) (d^(-η)) n x v Y → AlignedAxes x v →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        ∃ S Z ρ N y w f,RestoredGrains ω d h n x v Y S Z ρ N y w f) :
    AlignedOneScale σ ω := by
  classical
  have hflat : WangZahlLot.Obl.wz_clustered_cover_volume_gain.J σ ω :=
    WangZahlLot.wz_two_scale_flat_box_estimate σ ω hσ hσ2 hω hω1
      O rfl q rfl I rfl T rfl Q rfl X rfl K rfl F rfl A rfl P rfl B rfl
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.C rfl E rfl
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.J rfl hE
  intro ζ hζ
  obtain ⟨h,hh,hhζ,αC,hαC,κC,hκC,HC⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.clustered_gain hσ hσ2 hω hω1 hE hflat hζ
  obtain ⟨αG,hαG,κG,hκG,η,hη,hηh,HG⟩ := hGrains h hh
  obtain ⟨d₀,hd₀,Hbudget⟩ :=
    WangZahlLot.Obl.wz_normalized_projection_coarse_fine.exists_power_absorption
      (C := 384) (p := ζ-ζ/2-4*h) (r := 0) (by norm_num) (by linarith)
  obtain ⟨α,hα,κ,hκ,η',hη',_,H⟩ := aligned_alternative_remove_cutoff hσ hσ2 hω hω1 hζ
    (fun d n x v Y => Factorization d d ζ ω n x v Y) (by
      refine ⟨min αG αC,min κG κC,η,min d₀ (1/100),by positivity,by positivity,hη,
        by positivity,min_le_right _ _,?_⟩
      intro d hd hdd n x v Y hA haxes
      have hd100 := hdd.trans (min_le_right _ _)
      have hd1 : d ≤ 1 := hd100.trans (by norm_num)
      have hgainG := gain_mono (ω := ω) (σ := σ) (n := n) hd hd1
        (min_le_left αG αC) (min_le_left κG κC) (le_min hκG.le hκC.le)
      have hgainC := gain_mono (ω := ω) (σ := σ) (n := n) hd hd1
        (min_le_right αG αC) (min_le_right κG κC) (le_min hκG.le hκC.le)
      rcases HG d hd hd100 n x v Y hA haxes with hg | ⟨S,Z,ρ,N,y,w,f,hG⟩
      · exact Or.inl (hgainG.trans hg)
      have hAh := admissible_mono hd hd1 hηh hA
      by_cases hex : ∃ U : Finset (Fin N),
          O (d^(ζ/2))*∑ i∈S,volume (Z i) ≤ ∑ i∈S.filter (fun i => f i∈U),volume (Z i) ∧
          ∀ W,Convex ℝ W → O (q N {k | k∈U ∧ T ρ (y k) (w k)⊆W}*ρ^2) ≤ O (d^(-ζ))*volume W
      · obtain ⟨U,hmassU,hKU⟩ := hex
        have hbudget : 384*d^(ζ-ζ/2-4*h) ≤ 1 := by
          simpa only [Real.rpow_zero] using Hbudget d hd (hdd.trans (min_le_left _ _))
        have href := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces.refined_of_mass
          hd hd1 (by positivity : 0≤ζ/2) (by linarith : h+ζ/2≤ζ) hbudget hAh hG.1 U hmassU hKU
        obtain ⟨S',Z',N',y',w',f',_,hZ',hmass,hw',hcover,hK,hF,hB⟩ := href
        exact Or.inr ⟨S',Z',ρ,N',y',w',f',
          fun i => ⟨(hZ' i).1,(hZ' i).2.trans (hG.1.1 i).2.1⟩,
          hmass,hG.2.1,hG.2.2.1,hw',hcover,hK,hF,hB⟩
      · have hno : ∀ U : Finset (Fin N),
            O (d^(ζ/2))*∑ i∈S,volume (Z i) ≤ ∑ i∈S.filter (fun i => f i∈U),volume (Z i) →
            ¬ ∀ W,Convex ℝ W → O (q N {k | k∈U ∧ T ρ (y k) (w k)⊆W}*ρ^2) ≤ O (d^(-ζ))*volume W :=
          fun U hmassU hKU => hex ⟨U,hmassU,hKU⟩
        exact Or.inl (hgainC.trans (HC d hd hd100 n x v Y hAh S Z ρ N y w f hG hno)))
  exact ⟨α,hα,κ,hκ,η',hη',H⟩

/-- The uncapped geometric prism endpoint implies the complete aligned
one-scale coarse-factorization alternative. -/
theorem aligned_one_scale_of_prisms {σ ω : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hR : R σ ω)
    (hPrism : ∀ ζ : ℝ,0<ζ → ζ≤ω/1000 → PrismImprovement σ ω ζ) :
    AlignedOneScale σ ω := by
  apply aligned_one_scale_of_grains hσ hσ2 hω hω1 hE
  intro h hh
  exact aligned_grains_of_prisms hσ hσ2 hω hω1 hE hR hPrism hh

end WangZahlLot.Obl.wz_broad_grains_improvement
