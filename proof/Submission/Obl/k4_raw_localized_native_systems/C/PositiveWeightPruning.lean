import Submission.Obl.k4_raw_localized_native_systems.C.PrunedSample

/-
Adapted from this LOT tree, o178, session x0596, `PositiveWeightPruning.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
Adapted from this LOT tree, SAME obligation o178, x0596/92b467da,
PrunedSample.lean (generic builder introduced in eb28b809). The extra
zero-world deletion below has exactly zero original weighted mass cost.
-/
namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Delete zero-weight worlds as well as null-prior and light-law charts.
The certificate is only needed on subfamilies with positive original weights
and priors; the final native-sample conclusion and all losses are unchanged. -/
theorem pruned_native_sample_positive_weights (cert : CertPred) {p : Data} (hp : Valid p) {k M D : ℕ}
    {a₀ w loss χ d s m S U g X : ℝ} {C : ℕ} (γC : Fin C → Fin (p.W k)) (n : Fin C → Plane)
    (int sp : Fin C → ℝ) (A : Fin C → Set Line) (F G : Fin C → Set Point)
    (lst : Fin (p.W k) → Observation → Finset (Fin C))
    (hK : p.K k ≤ p.N k ^ loss) (hloss : 0 ≤ loss) (hCM : (C : ℝ) ≤ p.N k ^ M)
    (hM : 1 ≤ p.N k ^ M)
    (hdisj : ∀ c c', c ≠ c' → γC c = γC c' → Disjoint (A c) (A c'))
    (hlst : ∀ γ o, ((lst γ o).card : ℝ) ≤ p.N k ^ loss)
    (hlstm : ∀ γ c, MeasurableSet {o | c ∈ lst γ o})
    (hchart : ∀ c, chart (p.N k) M D (p.N k ^ loss) 0 0 0 (p.B k (γC c)) (p.E k (γC c))
      (int c • n c) (sp c • n c) (stripFrame g (n c)) (p.P k (γC c)) (A c) (F c)
      (∀ z ∈ F c, c ∈ lst (γC c) (obs (p.B k (γC c)) (δ (p.N k) 1) z)))
    (hn : ∀ c, ‖n c‖ = 1) (hg : 0 < g) (hgw : g ≤ p.N k ^ (-w))
    (hGm : ∀ c, MeasurableSet (G c)) (hGF : ∀ c, G c ⊆ F c)
    (hχ : 8 * p.N k ^ loss ≤ p.N k ^ χ)
    (hsig : p.N k ^ loss * δ (p.N k) 1 ≤ p.N k ^ (-1 + χ))
    (hmass : ENNReal.ofReal X ≤
      ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c))
    (hX : p.N k ^ (-loss) ≤ X - p.N k ^ (-χ))
    (homit : ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (F c \ G c) ≤
      ENNReal.ofReal (p.N k ^ (-a₀)))
    (hcert : ∀ (C' : ℕ) (ι : Fin C' → Fin C), Function.Injective ι →
      (∀ c, 0 < p.ν k (γC (ι c)) (A (ι c))) →
      (∀ c, 0 < p.ω k (γC (ι c))) →
      cert (p.N k) χ d s m C' (cR (p.ω k) (p.ν k) (γC ∘ ι) (A ∘ ι))
        (cLaws (p.ν k) (γC ∘ ι) (A ∘ ι) (G ∘ ι)) (cCoeff (p.P k) (γC ∘ ι) (n ∘ ι) (A ∘ ι))) :
    NativeSampleCert cert (p.N k) (p.K k) (p.W k) (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k)
      M D a₀ w loss 1 χ d s m S U := by
  classical
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hN : 0 < p.N k := hp.scale_pos k
  have hprob : ∀ γ, IsProbabilityMeasure (p.ν k γ) := fun γ => ((hfmt k).2.2.2.1 γ).1
  have hAm : ∀ c, MeasurableSet (A c) := fun c => (hchart c).2.2.2.2.2.2.1
  have hFm : ∀ c, MeasurableSet (F c) := fun c => (hchart c).2.2.2.2.2.2.2.1
  have hGA : ∀ c, G c ⊆ A c ×ˢ Set.univ := by
    intro c z hz
    obtain ⟨-, h2, -, -⟩ := (hchart c).2.2.2.2.2.2.2.2.2.2.1 z (hGF c hz)
    exact ⟨h2, Set.mem_univ _⟩
  -- the kept charts
  set keep := Finset.univ.filter (fun c : Fin C => 0 < p.ν k (γC c) (A c) ∧
    0 < p.ω k (γC c) ∧ ENNReal.ofReal (p.N k ^ (-χ)) ≤ cLaws (p.ν k) γC A G c Set.univ) with hkeep
  set e := keep.equivFin with he
  let ι : Fin keep.card → Fin C := fun i => (e.symm i).1
  have hι : Function.Injective ι := by
    intro i j h
    exact e.symm.injective (Subtype.ext h)
  have hιkeep : ∀ i, ι i ∈ keep := fun i => (e.symm i).2
  have hιpos : ∀ i, 0 < p.ν k (γC (ι i)) (A (ι i)) := fun i =>
    (Finset.mem_filter.1 (hιkeep i)).2.1
  have hιfl : ∀ i, ENNReal.ofReal (p.N k ^ (-χ)) ≤ cLaws (p.ν k) γC A G (ι i) Set.univ :=
    fun i => (Finset.mem_filter.1 (hιkeep i)).2.2.2
  have hιωpos : ∀ i, 0 < p.ω k (γC (ι i)) :=
    fun i => (Finset.mem_filter.1 (hιkeep i)).2.2.1
  -- sums over the kept charts
  have hsumι : ∀ f : Fin C → ENNReal, ∑ i, f (ι i) = ∑ c ∈ keep, f c := by
    intro f
    rw [← Finset.sum_coe_sort keep]
    exact Fintype.sum_equiv e.symm _ _ (fun i => rfl)
  -- the discarded good mass
  have hdrop : ∑ c ∈ Finset.univ \ keep,
      ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) ≤
        ENNReal.ofReal (p.N k ^ (-χ)) := by
    have hterm : ∀ c ∈ Finset.univ \ keep,
        ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) ≤
          ENNReal.ofReal (p.N k ^ (-χ)) * (ENNReal.ofReal (p.ω k (γC c)) * p.ν k (γC c) (A c)) := by
      intro c hc
      by_cases hω : 0 < p.ω k (γC c)
      · have hnk : ¬ (0 < p.ν k (γC c) (A c) ∧
            ENNReal.ofReal (p.N k ^ (-χ)) ≤ cLaws (p.ν k) γC A G c Set.univ) := by
          intro h
          exact (Finset.mem_sdiff.1 hc).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h.1, hω, h.2⟩)
        have := hprob (γC c)
        have hGle : ((p.ν k (γC c)).prod volume) (G c) ≤
            p.ν k (γC c) (A c) * cLaws (p.ν k) γC A G c Set.univ := by
          by_cases h0 : p.ν k (γC c) (A c) = 0
          · have hz : ((p.ν k (γC c)).prod volume) (G c) = 0 := by
              refine measure_mono_null (hGA c) ?_
              rw [Measure.prod_prod, h0, zero_mul]
            rw [hz]; exact bot_le
          · rw [cLaws, cLaw_univ, ← mul_assoc,
              ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]
        by_cases h0 : p.ν k (γC c) (A c) = 0
        · have hz : ((p.ν k (γC c)).prod volume) (G c) = 0 := by
            refine measure_mono_null (hGA c) ?_
            rw [Measure.prod_prod, h0, zero_mul]
          rw [hz, mul_zero]; exact bot_le
        · have hlt : cLaws (p.ν k) γC A G c Set.univ < ENNReal.ofReal (p.N k ^ (-χ)) := by
            push Not at hnk
            exact hnk (pos_iff_ne_zero.2 h0)
          calc ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c)
              ≤ ENNReal.ofReal (p.ω k (γC c)) *
                  (p.ν k (γC c) (A c) * cLaws (p.ν k) γC A G c Set.univ) := by gcongr
            _ ≤ ENNReal.ofReal (p.ω k (γC c)) *
                  (p.ν k (γC c) (A c) * ENNReal.ofReal (p.N k ^ (-χ))) := by gcongr
            _ = _ := by ring
      · have hzero : ENNReal.ofReal (p.ω k (γC c)) = 0 :=
          ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hω)
        simp only [hzero, zero_mul, mul_zero, le_refl]
    calc ∑ c ∈ Finset.univ \ keep,
          ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c)
        ≤ ∑ c ∈ Finset.univ \ keep, ENNReal.ofReal (p.N k ^ (-χ)) *
            (ENNReal.ofReal (p.ω k (γC c)) * p.ν k (γC c) (A c)) := Finset.sum_le_sum hterm
      _ = ENNReal.ofReal (p.N k ^ (-χ)) * ∑ c ∈ Finset.univ \ keep,
            ENNReal.ofReal (p.ω k (γC c)) * p.ν k (γC c) (A c) := by rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (p.N k ^ (-χ)) * ∑ c,
            ENNReal.ofReal (p.ω k (γC c)) * p.ν k (γC c) (A c) := by
          gcongr; exact Finset.subset_univ _
      _ ≤ ENNReal.ofReal (p.N k ^ (-χ)) * 1 := by
          gcongr; exact weighted_prior_sum_le hp γC A hAm hdisj
      _ = _ := mul_one _
  -- apply the builder to the kept charts
  refine native_sample_cert_of_family cert hp (γC ∘ ι) (n ∘ ι) (int ∘ ι) (sp ∘ ι) (A ∘ ι) (F ∘ ι)
    (G ∘ ι) (subLst ι lst) hK hloss ?_ hM ?_ ?_ ?_ ?_ (fun i => hn (ι i)) hg hgw
    (fun i => hGm (ι i)) (fun i => hGF (ι i)) hιpos hιfl hχ hsig ?_ ?_
    (hcert _ ι hι hιpos hιωpos)
  · have : (keep.card : ℝ) ≤ C := by
      have := Finset.card_le_univ keep
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    linarith
  · intro i j hij hγ
    exact hdisj (ι i) (ι j) (fun h => hij (hι h)) hγ
  · intro γ o
    exact (Nat.cast_le.2 (card_subLst_le hι lst γ o)).trans (hlst γ o)
  · intro γ i
    have : {o | i ∈ subLst ι lst γ o} = {o | ι i ∈ lst γ o} := by
      ext o; simp only [Set.mem_ofPred_eq, mem_subLst]
    rw [this]; exact hlstm γ (ι i)
  · intro i
    refine chart_ex_mono (hchart (ι i)) ?_
    intro hex z hz
    rw [mem_subLst]
    exact hex z hz
  · -- kept good mass
    have hsplit : ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) =
        ∑ c ∈ keep, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) +
        ∑ c ∈ Finset.univ \ keep,
          ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) := by
      rw [add_comm, Finset.sum_sdiff (Finset.subset_univ keep)]
    have hkept : ENNReal.ofReal X ≤
        ∑ c ∈ keep, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) +
          ENNReal.ofReal (p.N k ^ (-χ)) := by
      rw [hsplit] at hmass
      exact hmass.trans (add_le_add le_rfl hdrop)
    have hX' : ENNReal.ofReal (p.N k ^ (-loss)) + ENNReal.ofReal (p.N k ^ (-χ)) ≤
        ENNReal.ofReal X := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hfin : ENNReal.ofReal (p.N k ^ (-χ)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have := (hX'.trans hkept)
    have h2 := (ENNReal.add_le_add_iff_right hfin).1 this
    calc ENNReal.ofReal (p.N k ^ (-loss)) ≤
          ∑ c ∈ keep, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) := h2
      _ = ∑ i, ENNReal.ofReal (p.ω k ((γC ∘ ι) i)) * ((p.ν k ((γC ∘ ι) i)).prod volume)
            ((G ∘ ι) i) :=
          (hsumι (fun c => ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c))).symm
  · -- kept omission
    have hFG : ∀ c, ((p.ν k (γC c)).prod volume) (F c) =
        ((p.ν k (γC c)).prod volume) (G c) + ((p.ν k (γC c)).prod volume) (F c \ G c) := by
      intro c
      rw [← measure_union Set.disjoint_sdiff_right ((hFm c).diff (hGm c)), Set.union_sdiff_cancel (hGF c)]
    calc ∑ i, ENNReal.ofReal (p.ω k ((γC ∘ ι) i)) * ((p.ν k ((γC ∘ ι) i)).prod volume) ((F ∘ ι) i)
        = ∑ c ∈ keep, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (F c) :=
          hsumι (fun c => ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (F c))
      _ = ∑ c ∈ keep, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) +
          ∑ c ∈ keep, ENNReal.ofReal (p.ω k (γC c)) *
            ((p.ν k (γC c)).prod volume) (F c \ G c) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hFG, mul_add]
      _ ≤ ∑ c ∈ keep, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) +
          ENNReal.ofReal (p.N k ^ (-a₀)) := by
          gcongr
          exact (Finset.sum_le_sum_of_subset (Finset.subset_univ keep)).trans homit
      _ = ∑ i, ENNReal.ofReal (p.ω k ((γC ∘ ι) i)) * ((p.ν k ((γC ∘ ι) i)).prod volume)
            ((G ∘ ι) i) + ENNReal.ofReal (p.N k ^ (-a₀)) := by
          rw [← hsumι (fun c => ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c))]
          rfl

end
end Submission.Obl.k4_raw_localized_native_systems.C
