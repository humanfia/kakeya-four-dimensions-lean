-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedPrismState.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CapsBridge
import Submission.WZ.Obl.wz_move_two_prism_fan_avoidance.Assembly
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.NormalizedTransfer

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- Capped stage-two data is precisely the normalized input to fan avoidance. -/
theorem normalized_input_of_capped_prisms {ω ζ d h ρ c : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (H : D.Valid ω ζ d h ρ c x v Y 2) (Hcaps : D.HasCaps d h ρ c) :
    WangZahlLot.Obl.wz_move_two_prism_fan_avoidance.R ω ζ d h ρ c n x v Y 1 := by
  obtain ⟨ha,hab,hbc,hc,hW,hmass,hdense,hcross,hbroad,hX,hw,hcover,hdisj⟩ := H
  have hs := (hcover (by decide)).1
  rw [hs] at hcross hX
  obtain ⟨m,hm,hcount,haverage⟩ := Hcaps
  exact ⟨D.a,D.L,D.N,D.z,D.e,D.W,D.y,D.w,D.γ,m,ha,hab,hbc,hc,hW,hmass,hdense,
    hcross,hbroad,hX,hw,(hcover (by decide)).2,hdisj (by decide),
    fun _ j => ⟨hm j,hcount j,haverage j⟩,by omega⟩

/-- Compose accepted fan avoidance and normalized prism transfer. The same
fine family, coarse radius, and grain length are retained. -/
theorem state_of_capped_prisms {ω ζ ε : ℝ} (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ η → A d h (d^(-h)) (d^(-h)) n x v Y →
      ∀ D : PrismData n, D.Valid ω ζ d h ρ c x v Y 2 → D.HasCaps d h ρ c →
      ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ)
        (y w : Fin N → V) (f : Fin n → Fin N) (a g : ℝ),
        C d ε n x v Y S Z ρ N y w f True ∧ 0 < g ∧
        WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.Broad ω ζ d ε ρ n N v S Z f ∧
        H d ε n x v S Z ρ N y w f a c 0 g := by
  obtain ⟨s,dT,hs,hsε,hdT,HT⟩ :=
    WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.normalized_prism_transfer
      (ω := ω) (ζ := ζ) hε
  obtain ⟨dA,hdA,HA⟩ :=
    WangZahlLot.Obl.wz_move_two_prism_fan_avoidance.avoidance_main (ω := ω) (ζ := ζ) hs
  refine ⟨s/4,min (1/100) (min dT dA),by positivity,by linarith,by positivity,min_le_left _ _,?_⟩
  intro d h ρ c n x v Y hd hdd hh hAd D HD Hcaps
  have hcut : d ≤ 1/100 ∧ d ≤ dT ∧ d ≤ dA := by simpa only [le_min_iff] using hdd
  have hd1 : d ≤ 1 := hcut.1.trans (by norm_num)
  have Hnormalized := normalized_input_of_capped_prisms D
    (D.valid_mono hd hd1 hh le_rfl HD) (D.hasCaps_mono hd hd1 hh Hcaps)
  have Havoid := HA d hd hcut.2.2 n x v Y ρ c Hnormalized
  obtain ⟨a,L,N,z,e,W,y,w,γ,m,ha,hab,hbc,hc,hW,hmass,hdense,hcross,hbroad,hX,hw,
    hgeom,hdisj,hcap,havoid⟩ := Havoid
  let D' : WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.PrismData ω ζ d s ρ c n x v Y :=
    ⟨a,L,N,z,e,W,y,w,γ,ha,hab,hbc,hc,hW,hmass,hdense,hcross,hbroad,hX,hw,hgeom,hdisj⟩
  obtain ⟨S,Z,N',y',w',f,g,hC,hg,hbr,hH⟩ := HT d hd hcut.2.1 n x v Y
    (admissible_mono hd hd1 (show h ≤ s by linarith) hAd) ρ c D' m
    (fun j => (hcap (by decide) j).1) (fun j => (hcap (by decide) j).2.1)
    (fun j => (hcap (by decide) j).2.2) (havoid (by decide))
  exact ⟨S,Z,N',y',w',f,a,g,hC,hg,hbr,hH⟩

/-- Capped stage two produces the full stage-zero state without a separate
normalization theorem. -/
theorem stage_zero_of_capped_prisms {ω ζ ε : ℝ} (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ η → A d h (d^(-h)) (d^(-h)) n x v Y →
      (∃ D : PrismData n, D.Valid ω ζ d h ρ c x v Y 2 ∧ D.HasCaps d h ρ c) →
      d^(1-ω/100) ≤ ρ → J ω ζ d ε ρ c n x v Y 0 := by
  obtain ⟨η,d₀,hη,hηε,hd₀,hd₀small,Hstate⟩ := state_of_capped_prisms (ω := ω) (ζ := ζ) hε
  refine ⟨η,d₀,hη,hηε,hd₀,hd₀small,?_⟩
  rintro d h ρ c n x v Y hd hdd hh hA ⟨D,HD,Hcaps⟩ hbase
  obtain ⟨S,Z,N,y,w,f,a,g,hC,hg,hbr,hH⟩ := Hstate hd hdd hh hA D HD Hcaps
  exact ⟨S,Z,N,y,w,f,a,g,hC,hbase,hg,hbr,hH,by omega,by omega,by omega⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
