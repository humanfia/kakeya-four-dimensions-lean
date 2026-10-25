-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.OrientedWindow.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.GlobalUnion
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactBandArea
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactPowerLoss

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set MeasureTheory
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- Refined curvature-ordered windows satisfy the uniform area estimate after
absorbing both the finite contact losses and the dyadic slope count. -/
theorem exists_oriented_window_estimate (ε : ℝ) (hε : 0 < ε) :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1/10000 ∧ 0 < C ∧ OrientedWindowEstimate ε θ C := by
  obtain ⟨base, θ, C₀, hbase, hθ, hθsmall, hC₀, hratio, hloss⟩ :=
    exists_contact_loss_parameters (ε/2) (by positivity)
  refine ⟨θ, 30000000000000000*C₀*(6*(1+1/(ε/2))), hθ, hθsmall, by positivity, ?_⟩
  intro n q g hq hg hjet δ hδ hδ100 hsep A B D κ l u hδD hD20 hκ hnatural hκsmall
    hl hu hlu hshort hA hB hcross horder
  have hD : 0 < D := hδ.trans_le hδD
  have hδ1 : δ ≤ 1 := by linarith
  have hwidth : u-l ≤ 1 := by linarith
  have hinterval : Icc l u ⊆ Icc (-1:ℝ) 1 := fun _ ht => ⟨hl.trans ht.1, ht.2.trans hu⟩
  have hwithinA := within_curvature_le_of_coefficient_diameter hjet A hA
  have hwithinB := within_curvature_le_of_coefficient_diameter hjet B hB
  let N : ℝ := (A.card:ℝ)+(B.card:ℝ)
  let V : ℝ := 30000000000000000*C₀*δ^(-(ε/2))*δ*Real.sqrt (δ/D)*N*Real.sqrt N
  have hV : 0 ≤ V := by dsimp [V,N]; positivity
  have hbandbound (lower s : ℝ) (hs : 0 < s) (hnat : δ*D ≤ s^2)
      (hband : lower=s/2 ∨ s^2 ≤ δ*D) :
      volume (slopeBandUnion A B g δ l u lower s) ≤ ENNReal.ofReal V := by
    have harea := volume_contact_band_le hg hjet
      (fun i j hij => hδ.trans_le (hsep i j hij)) A B hδ hD hs
      hl hu hlu hshort hbase (hratio D hD.le)
      (fun i hi j hj => (hA i hi j hj).trans (by nlinarith [mul_le_mul_of_nonneg_right hθsmall hD.le]))
      hcross
      (fun i hi j hj x hx => hwithinA i hi j hj x (hinterval hx))
      (fun i hi j hj x hx => hwithinB i hi j hj x (hinterval hx)) horder hnat hband
      (slopeBandUnion A B g δ l u lower s) (by
        intro p hp
        obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hp
        obtain ⟨j, hj, hpi, hpj, ht, hlo, hhi⟩ := mem_iUnion₂.mp hp
        exact ⟨ht,i,hi,j,hj,hpi.2,hpj.2,hlo,hhi⟩)
    have hpow := contact_rank_degree_loss_of_coefficient_packing hloss hδ hδ1
      (resolution_le_contact_separation hδ hδD hD20 hs hnat) hlu hwidth q hq hsep A B
    apply harea.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ = 30000000000000000 *
          (((4:ℝ)^(windowLensHeight base (10000*s/D) l u+1)+1)*
            (((Nat.log 2 (A.card+B.card)+1:ℕ):ℝ)^3))*δ*Real.sqrt (δ/D)*N*Real.sqrt N := by
        dsimp [N]
        ring
      _ ≤ 30000000000000000*(C₀*δ^(-(ε/2)))*δ*Real.sqrt (δ/D)*N*Real.sqrt N := by
        gcongr
      _ = V := by dsimp [V]; ring
  let s₀ := Real.sqrt (δ*D)
  have hs₀ : 0 < s₀ := Real.sqrt_pos.mpr (mul_pos hδ hD)
  have hs₀sq : s₀^2=δ*D := Real.sq_sqrt (mul_pos hδ hD).le
  have hnatband := hbandbound 0 s₀ hs₀ hs₀sq.ge (Or.inr hs₀sq.le)
  have hdyband : ∀ k < Nat.log 2 ⌈2*κ*D/s₀⌉₊+1,
      volume (slopeBandUnion A B g δ l u (s₀*2^k) (s₀*2^(k+1))) ≤ ENNReal.ofReal V := by
    intro k hk
    have hpow : (1:ℝ) ≤ 2^(k+1) := one_le_pow₀ (by norm_num)
    have hs : s₀ ≤ s₀*2^(k+1) := by nlinarith
    refine hbandbound _ _ (by positivity) ?_ ?_
    · have hh := pow_le_pow_left₀ hs₀.le hs 2
      rwa [hs₀sq] at hh
    · left
      rw [pow_succ]
      ring
  have hcap0 : 0 ≤ 2*κ*D := by positivity
  have hcapD : 2*κ*D ≤ D := by nlinarith [mul_lt_mul_of_pos_right hκsmall hD]
  have hvol := volume_narrowWindowUnion_le_log A B g δ l u hs₀ hcap0 hV hnatband hdyband
  have hfac := bandFactor_le_rpow hδ hδ1 hδD hD20 hcap0 hcapD (show 0 < ε/2 by positivity)
  apply hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (6*(1+1/(ε/2))*δ^(-(ε/2)))*V := mul_le_mul_of_nonneg_right hfac hV
    _ = _ := by
      rw [show -ε=-(ε/2)+-(ε/2) by ring, Real.rpow_add hδ]
      dsimp [V,N]
      ring

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
