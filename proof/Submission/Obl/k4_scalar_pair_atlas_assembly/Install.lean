import Submission.Obl.k4_scalar_pair_atlas_assembly.Tables
import Submission.Obl.k4_scalar_pair_atlas_assembly.Static
import Submission.Obl.k4_scalar_pair_atlas_assembly.Numerics
import Submission.Obl.k4_scalar_pair_atlas_assembly.Mass
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Submission.Obl.k4_scalar_pair_atlas_assembly
open MeasureTheory Set Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
noncomputable section

/-- Installation of a sparse geometric table in the original incidence law. -/
theorem install_tables : InstallTables := by
  classical
  intro p hp B G hB hG
  refine ⟨installComplexity B G, installComplexity_pos B G, ?_⟩
  intro h₀ h₁ r ε σ a e hε hσ hσε k T T₁ n γ j A C u v J P Λ
    hold hT₁ htime m g b code u' v' J' P' R htable hmass
  have hN : 2 ≤ N p k := hp.1.1 k
  have hN₁ : 1 ≤ N p k := by linarith
  have hN₀ : 0 < N p k := by linarith
  have hBpow : N p k ^ (B : ℝ) ≤ N p k ^ (installComplexity B G : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN₁ (Nat.cast_le.mpr (old_le_installComplexity B G))
  have hGpow : N p k ^ (G : ℝ) ≤ N p k ^ (installComplexity B G : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN₁ (Nat.cast_le.mpr (table_le_installComplexity B G))
  have hσpow : N p k ^ σ ≤ N p k ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)
  obtain ⟨hOldtime, hOldcount, hOldmeas, hOlddis, hOldsub, hOldbounds,
    hOldcard, hOldlistmeas, hOldrecover, hOldmass⟩ := hold
  obtain ⟨hcount, hcode, hnewbounds, hfit, hRcard, hR, hcover⟩ := htable
  have hAf (i z) : Format 5 (N p k ^ (B : ℝ)) B {a | (z, a) ∈ A i} := by
    obtain ⟨_, _, _, _, _, _, _, _, h, _, _, _⟩ := hOldbounds i
    exact h z
  have hCf (i z) : Format 6 (N p k ^ (B : ℝ)) B
      {a | ((z, fun e : Fin 5 => a e.castSucc), a 5) ∈ C i} := by
    obtain ⟨_, _, _, _, _, _, _, _, _, h, _, _⟩ := hOldbounds i
    exact h z
  choose source hsource hblockmass using
    fun w bb => exists_source_block p k T n γ j A C u v P a e T₁ hT₁ w bb
      (fun i => (hOldmeas i).1) (fun i => (hOldmeas i).2) hOldsub
  let D := Static.assigned g b code j A source
  let F := Static.selected g b code j A C R source
  let lists := fun w => transportList (Λ w) R
  have hbudget := install_format_budget hN B G n hOldcount
  have hsmallbudget : (n : ℝ) * N p k ^ (B : ℝ) ≤
      N p k ^ (installComplexity B G : ℝ) := by
    have hnH : 0 ≤ (n : ℝ) * N p k ^ (B : ℝ) := by positivity
    nlinarith
  have hselectedmass : pairMass p k T n γ j C u v P a e T₁ ≤
      ∑ w : Fin (W p k), ENNReal.ofReal (ω p k w) *
        mu p k w {q | ∃ o : Fin m, g o = w ∧ q ∈ F o} := by
    have hsum (w : Fin (W p k)) :
        (∑ bb : Fin (2 ^ T₁), mu p k w
          (laterEvent p k T n γ j A C u v P a e T₁ w bb (source w bb))) ≤
        mu p k w {q | ∃ o : Fin m, g o = w ∧ q ∈ F o} := by
      apply sum_coarse_mass_le (ν p k w) (E p k w)
        (fun bb => laterEvent p k T n γ j A C u v P a e T₁ w bb (source w bb))
        (fun bb => measurable_laterEvent p k T n γ j A C u v P a e T₁ w bb _
          (fun i => (hOldmeas i).1) (fun i => (hOldmeas i).2))
        (fun bb => laterEvent_subset p k T n γ j A C u v P a e T₁ w bb _ hOldsub)
      intro bb q hq
      obtain ⟨⟨i, i', hγi, hγi', hji, hIs, hIw, hAi, hCi', hAg⟩, hqt⟩ := hq
      have hgw : g (code i) = w := (hcode i).1.trans hγi
      have hbc : b (code i) = bb := coarse_unique (j i) _ _ (hcode i).2 hIs
      have hcompat : code i ∈ R i' :=
        hcover i i' (hγi.trans hγi'.symm) bb hIs hIw
          ⟨q.1, hAi, (hOldsub i' hCi').2.1⟩ hAg
      refine ⟨code i, hgw, ?_⟩
      refine ⟨⟨i, rfl, ?_, hAi⟩, ?_, i', hcompat, hCi'⟩
      · simpa only [hgw, hbc] using hji
      · simpa only [hbc, mem_ofPred_eq] using hqt
    unfold pairMass
    calc
      (∑ w : Fin (W p k), ∑ bb : Fin (2 ^ T₁),
        ENNReal.ofReal (ω p k w) * ENNReal.ofReal ((2 : ℝ) ^ T₁) *
        ((ν p k w).prod (volume.prod volume))
          (goodPairs p k T n γ j C u v P a e T₁ w bb)) ≤
        ∑ w : Fin (W p k), ∑ bb : Fin (2 ^ T₁),
          ENNReal.ofReal (ω p k w) * mu p k w
            (laterEvent p k T n γ j A C u v P a e T₁ w bb (source w bb)) := by
        apply Finset.sum_le_sum
        intro w _
        apply Finset.sum_le_sum
        intro bb _
        simpa only [mul_assoc] using
          mul_le_mul_right (hblockmass w bb) (ENNReal.ofReal (ω p k w))
      _ = ∑ w : Fin (W p k), ENNReal.ofReal (ω p k w) *
          ∑ bb : Fin (2 ^ T₁), mu p k w
            (laterEvent p k T n γ j A C u v P a e T₁ w bb (source w bb)) := by
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ w : Fin (W p k), ENNReal.ofReal (ω p k w) *
          mu p k w {q | ∃ o : Fin m, g o = w ∧ q ∈ F o} :=
        Finset.sum_le_sum (fun w _ => mul_le_mul_right (hsum w) _)
  let s : Candidate p (installComplexity B G) r (L p) h₁ ε k T₁ (Fin m) :=
    { world := g
      block := b
      assigned := D
      selected := F
      u := u'
      v := v'
      J := J'
      poly := P'
      lists := lists
      time := htime
      count := by simpa using hcount.trans hGpow
      measurable := fun o =>
        ⟨Static.measurable_assigned g b code j A source (fun i => (hOldmeas i).1) o,
          Static.measurable_selected g b code j A C R source
            (fun i => (hOldmeas i).1) (fun i => (hOldmeas i).2) o⟩
      disjoint := Static.assigned_disjoint γ g b code j A source
        (fun i => (hcode i).1) hOlddis
      subset := by
        intro o q hq
        obtain ⟨hqd, hqt, i, hoi, hCi⟩ := hq
        refine ⟨?_, hqd, halfI_subset T₁ (b o) hqt⟩
        simpa only [(hR i o hoi).1] using (hOldsub i hCi).1
      bounds := by
        intro o
        obtain ⟨hJpos, hJinv, hJmax, hcenter, hdegree, hcoeff⟩ := hnewbounds o
        refine ⟨hJpos, hJinv.trans hGpow, hJmax, hcenter, hdegree,
          (fun c => (hcoeff c).trans hGpow), ?_, ?_, ?_, ?_⟩
        · rintro l ⟨i, hi, hji, hli⟩
          obtain ⟨_, _, _, _, _, _, _, hcoords, _, _, _, _⟩ := hOldbounds i
          exact ⟨(hcoords l hli).1.trans hBpow,
            fun c => ((hcoords l hli).2 c).trans hσpow⟩
        · intro z
          exact k4_scalar_conditional_crop_worlds.Format.mono
            (Static.format_assigned g b code j A source (by positivity) hAf o z)
            hsmallbudget (old_le_installComplexity B G)
        · intro z
          exact k4_scalar_conditional_crop_worlds.Format.mono
            (Static.format_selected g b code j A C R source (by positivity) hB hAf hCf o z)
            hbudget (old_le_installComplexity B G)
        · rintro l ⟨i, hi, hji, hli⟩ t ht
          simpa only [hi] using hfit i l hli t (by simpa only [hi] using ht)
      list_card := by
        intro w z
        calc
          ((lists w z).card : ℝ) ≤ ((Λ w z).card : ℝ) * N p k ^ (ε / 2) :=
            card_transportList_le _ R z _ hRcard
          _ ≤ N p k ^ σ * N p k ^ (ε / 2) :=
            mul_le_mul_of_nonneg_right (hOldcard w z) (by positivity)
          _ = N p k ^ (σ + ε / 2) := (Real.rpow_add hN₀ _ _).symm
          _ ≤ N p k ^ ε := Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)
      list_measurable := fun w o => measurable_transportList (Λ w) R (hOldlistmeas w) o
      recovers := by
        intro o
        apply world_transport_recovers (mu p k) γ g Λ R
          (fun q => ((![q.2, y q.1 q.2] : Fin 2 → ℝ),
            (⌊x q.1 q.2 / (N p k ^ (-L p))⌋ : ℤ))) C hOldrecover
          (fun i o hoi => (hR i o hoi).1) o (F o)
        intro q hq
        exact hq.2.2
      mass := by
        have hσneg : ENNReal.ofReal (N p k ^ (-ε)) ≤ ENNReal.ofReal (N p k ^ (-σ)) :=
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith))
        exact hσneg.trans (hmass.trans hselectedmass) }
  exact s.to_chart

end
end Submission.Obl.k4_scalar_pair_atlas_assembly
