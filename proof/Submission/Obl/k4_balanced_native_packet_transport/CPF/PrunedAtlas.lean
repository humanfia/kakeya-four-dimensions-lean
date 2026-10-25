/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/PrunedAtlas.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/PrunedAtlas.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.CrossingLoss
import Submission.Obl.k4_balanced_native_packet_transport.CPF.TwoSided
import Submission.Lib.K4Homogenization.DyadicObservations

/-! Assemble a known atlas by retaining only short crossing lists.
The original assignments and every chart's geometric data are retained.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set
open scoped Classical ENNReal

noncomputable section

theorem obs_coarsen {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s) (B : ℝ) (q : Incidence) :
    obs B (δ N r) q = Submission.Lib.K4Homogenization.coarsenObservation N r s
      (obs B (δ N s) q) := by
  apply Prod.ext
  · rfl
  · exact Submission.Lib.K4Homogenization.observation_bin_coarsen hN hrs (B * (x q.1 q.2) 3)

theorem Atlas.measurableSet_crossingKeep {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) {H : ℝ} (hH : 0 ≤ H) (b : Fin a.C) :
    MeasurableSet (a.crossingKeep r bins m H b) := by
  have hmeas : MeasurableSet {q : Incidence | ENNReal.ofReal H <
      finiteCrossingCount (a.crossingSets r bins m (a.γ b))
        (obs (p.B k (a.γ b)) (δ (p.N k) r) q)} := measurableSet_lt measurable_const
    ((measurable_finiteCrossingCount _ (a.measurableSet_crossingSets r bins m (a.γ b))).comp
      (measurable_obs (p.B k (a.γ b)) (δ (p.N k) r)))
  have heq : a.crossingKeep r bins m H b =
      {q | ENNReal.ofReal H < finiteCrossingCount (a.crossingSets r bins m (a.γ b))
        (obs (p.B k (a.γ b)) (δ (p.N k) r) q)}ᶜ := by
    ext q
    simp only [crossingKeep, mem_ofPred_eq, mem_compl_iff,
      finiteCrossingCount_gt_iff _ _ hH, not_lt, crossingList]
  rw [heq]
  exact hmeas.compl

def Atlas.pruneCrossings {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (H κ' : ℝ) : Atlas p k :=
  {a with κ := κ', F := fun b => a.F b ∩ a.crossingKeep r bins m H b}

theorem Atlas.pruneCrossings_charts {p : Data} {k M D M' D' : ℕ} {r H κ' : ℝ}
    (a : Atlas p k) (ha : a.TrueAt M D r) (hN : 1 ≤ p.N k)
    (hM : M ≤ M') (hD : D ≤ D') (h4 : 4 ≤ D') (hκ : 1 ≤ a.κ)
    (hκ' : a.κ ≤ κ') (hB : ∀ γ, 0 < p.B k γ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (hmesh : 4 * a.κ ^ 2 ≤ (m : ℝ))
    (hH : 0 ≤ H)
    (hfmt : ∀ b, p.N k ^ M + (a.C : ℝ) * ((bins (a.γ b)).card * (5 + 4 * m)) ≤ p.N k ^ M')
    (hbin : ∀ b q, q ∈ a.F b →
      (obs (p.B k (a.γ b)) (δ (p.N k) r) q).2 ∈ bins (a.γ b)) :
    ∀ b, Chart (p.N k) M' D' κ' a.T (a.j b : ℝ) r (p.B k (a.γ b))
      (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b)
        ((a.pruneCrossings r bins m H κ').F b)
        (∀ q ∈ (a.pruneCrossings r bins m H κ').F b,
          b ∈ a.shortCrossingList r bins m H (a.γ b)
            (obs (p.B k (a.γ b)) (δ (p.N k) r) q)) := by
  intro b
  have hch := ha.2.2.1 b
  have hκ0 : 0 < a.κ := lt_of_lt_of_le zero_lt_one hκ
  have hR (b : Fin a.C) : (a.R b).totalDegree ≤ 2 := (ha.2.2.1 b).2.2.2.2.1
  obtain ⟨_, _, _, _, _, _, _, _, horigfmt, _⟩ := ha.2.2.1 b
  have hmono := Chart.mono hN hM hD hκ0 hκ' (hB _).le (fun _ => True.intro) hch
  obtain ⟨hQ, hcu, hQsize, hsize, hdeg, hcoeff, hA, hF, hformat, hwhole, hsel, _⟩ := hmono
  refine ⟨hQ, hcu, hQsize, hsize, hdeg, hcoeff, hA,
    hF.inter (a.measurableSet_crossingKeep r bins m hH b), ?_, hwhole, ?_, ?_⟩
  · intro i
    refine ⟨(hformat i).1, ?_⟩
    have hguard := a.format_crossingKeep r bins m H hκ0.le hR b i
    have hnew := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter (horigfmt i).2 hguard
    exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono hnew (hfmt b) (max_le hD h4)
  · intro q hq
    exact hsel q hq.1
  · intro q hq
    exact a.mem_shortCrossingList ((ha.2.2.1 b).crosses_of_mem (hB _) hκ hmesh hq.1)
      (hbin b q hq.1) hq.2

theorem Atlas.pruneCrossings_mass_add_lost {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) {H : ℝ} (hH : 0 ≤ H) (κ' : ℝ) :
    (a.pruneCrossings r bins m H κ').mass + a.crossingLostMass r bins m H = a.mass := by
  unfold Atlas.mass pruneCrossings crossingLostMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_add, measure_inter_add_sdiff _ (a.measurableSet_crossingKeep r bins m hH b)]

theorem Atlas.pruneCrossings_mass_lower {p : Data} {k M D : ℕ} {r H κ' : ℝ}
    (a : Atlas p k) (ha : a.TrueAt M D r) (hκ : 1 ≤ a.κ) (hκ' : 2 * a.κ ≤ κ')
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (hH : 0 ≤ H)
    (hlost : a.crossingLostMass r bins m H ≤ ENNReal.ofReal (2 * a.κ)⁻¹) :
    ENNReal.ofReal κ'⁻¹ ≤ (a.pruneCrossings r bins m H κ').mass := by
  have hκ0 : 0 < a.κ := lt_of_lt_of_le zero_lt_one hκ
  have hstart : ENNReal.ofReal (2 * a.κ)⁻¹ + ENNReal.ofReal (2 * a.κ)⁻¹ ≤ a.mass := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    have heq : (2 * a.κ)⁻¹ + (2 * a.κ)⁻¹ = a.κ⁻¹ := by field_simp <;> norm_num
    rw [heq]
    exact ha.2.2.2
  have hretain : ENNReal.ofReal (2 * a.κ)⁻¹ ≤ (a.pruneCrossings r bins m H κ').mass := by
    apply ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top
    calc
      _ ≤ a.mass := hstart
      _ = (a.pruneCrossings r bins m H κ').mass + a.crossingLostMass r bins m H :=
        (a.pruneCrossings_mass_add_lost r bins m hH κ').symm
      _ ≤ _ := add_le_add le_rfl hlost
  exact (ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) hκ')).trans hretain

/-- Fixed-sample conversion: sufficiently small list loss gives the exact known-atlas
predicate, with lists indexed by the original terminal observation. -/
theorem knownAt_of_crossing_loss {p : Data} {k M D M' D' : ℕ} {r h ε H κ' : ℝ}
    (a : Atlas p k) (ha : a.TrueAt M D r) (hN : 1 ≤ p.N k) (hrL : r ≤ p.L)
    (hM : M ≤ M') (hD : D ≤ D') (h4 : 4 ≤ D') (hκ : 1 ≤ a.κ)
    (hκ' : 2 * a.κ ≤ κ') (hκpow : κ' ≤ p.N k ^ ε) (hB : ∀ γ, 0 < p.B k γ)
    (hT : (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε))
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (hmesh : 4 * a.κ ^ 2 ≤ (m : ℝ))
    (hH : 0 ≤ H) (hHκ : H ≤ κ')
    (hfmt : ∀ b, p.N k ^ M + (a.C : ℝ) * ((bins (a.γ b)).card * (5 + 4 * m)) ≤ p.N k ^ M')
    (hbin : ∀ b q, q ∈ a.F b →
      (obs (p.B k (a.γ b)) (δ (p.N k) r) q).2 ∈ bins (a.γ b))
    (hlost : a.crossingLostMass r bins m H ≤ ENNReal.ofReal (2 * a.κ)⁻¹) :
    KnownAt p M' D' r h ε k := by
  let a' := a.pruneCrossings r bins m H κ'
  let lst := fun γ o => a.shortCrossingList r bins m H γ
    (Submission.Lib.K4Homogenization.coarsenObservation (p.N k) r p.L o)
  have hκκ' : a.κ ≤ κ' := (by linarith [hκ] : a.κ ≤ 2 * a.κ).trans hκ'
  have hcharts := a.pruneCrossings_charts ha hN hM hD h4 hκ hκκ' hB bins m hmesh hH hfmt hbin
  refine ⟨a', lst, ?_, hκpow, hT, ?_, ha.2.1, ?_, ?_,
    a.pruneCrossings_mass_lower ha hκ hκ' bins m hH hlost⟩
  · change 1 ≤ κ'
    linarith
  · exact ha.1.trans (pow_le_pow_right₀ hN hM)
  · intro γ o
    exact (a.shortCrossingList_card r bins m hH γ _).trans hHκ
  · intro b
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hlist⟩ := hcharts b
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
    intro q hq
    have hc := hlist q hq
    change b ∈ a.shortCrossingList r bins m H (a.γ b)
      (Submission.Lib.K4Homogenization.coarsenObservation (p.N k) r p.L
        (obs (p.B k (a.γ b)) (δ (p.N k) p.L) q))
    rw [← obs_coarsen hN hrL]
    exact hc

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
