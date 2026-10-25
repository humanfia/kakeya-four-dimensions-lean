import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Basic
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Monotonicity
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Lists
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Pruning

/-! Install bounded observation lists after a common geometric cutoff. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set
open scoped ENNReal BigOperators

private theorem two_div_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hgap : 2 * b ≤ c) :
    2 * (a / (c * d)) ≤ a / (b * d) := by
  rw [show 2 * (a / (c * d)) = (2 * a) / (c * d) by ring]
  apply (div_le_div_iff₀ (mul_pos hc hd) (mul_pos hb hd)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hgap (mul_nonneg ha hd.le)]

/-- Finite certificate conversion. All losses and format obligations are
explicit; the good event depends only on observed crossing multiplicity. -/
theorem install_finite_lists {p : Data} (hp : Exact p)
    {B B' k T n : ℕ} {r h δ ε R : ℝ}
    {γ : Fin n → Fin (worlds p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Trajectory} {C : Fin n → Set Incidence} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    (hd : RawChartData p B r r h δ true k T n γ j A C u v J P)
    (hB : B ≤ B') (hδε : δ ≤ ε) (hgap : 2 * N p k ^ δ ≤ N p k ^ ε)
    (hR0 : 0 ≤ R) (hR : R ≤ N p k ^ ε)
    (X : Fin n → Set Observation) (hX : ∀ i, MeasurableSet (X i))
    (G : Fin (worlds p k) → Set Incidence) (hG : ∀ a, MeasurableSet (G a))
    (hcross : ∀ i q, q ∈ C i → observation p k r q ∈ X i)
    (hknown : ∀ a q, q ∈ G a →
      ((labelsAt γ X a (observation p k r q)).card : ℝ) ≤ R)
    (hformat : ∀ i z, Format 6 (N p k ^ (B' : ℝ)) B'
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C i ∩ G (γ i)})
    (hbudget : ENNReal.ofReal (N p k ^ (-ε)) +
        3 * (∑ a, ENNReal.ofReal (weight p k a) * mu p k a (G a)ᶜ) ≤
      ∑ a, ENNReal.ofReal (weight p k a) * mu p k a {q | ∃ i, γ i = a ∧ q ∈ C i}) :
    Chart p B' r r h ε true k := by
  classical
  letI : ∀ a : Fin (worlds p k), IsFiniteMeasure (mu p k a) := fun a => hp.mu_finite k a
  have hN : 1 ≤ N p k := le_trans (by norm_num) (hp.resolution_ge k)
  have hN0 : 0 < N p k := zero_lt_one.trans_le hN
  have hbase := hd.mono hN hB le_rfl hδε
  rcases hd with ⟨hT, hn, hm, hdisj, hsub, hchart, hmass⟩
  rcases hbase with ⟨hT', hn', hm', hdisj', hsub', hchart', hmass'⟩
  have hnull := assigned_incidence_inter_null hp γ j A C hdisj
    (fun i => (hsub i).trans inter_subset_right)
  obtain ⟨F, hhalf, hret⟩ := prune_to_common_good
    (fun a => ENNReal.ofReal (weight p k a)) (mu p k) γ C G
    (fun i => (hm i).2) hG hnull
  let e : Fin F.card ≃ F := F.equivFin.symm
  have he : Function.Injective (fun i : Fin F.card => (e i : Fin n)) := by
    intro i i' hii
    exact e.injective (Subtype.ext hii)
  let C' : Fin F.card → Set Incidence := fun i => C (e i) ∩ G (γ (e i))
  let L' : Fin (worlds p k) → Observation → Finset (Fin F.card) :=
    fun a z => Finset.univ.filter (fun i => (e i : Fin n) ∈ boundedLabels γ X R a z)
  have hC'm : ∀ i, MeasurableSet (C' i) := fun i => ((hm (e i)).2).inter (hG _)
  have hC'pos (i : Fin F.card) : 0 < mu p k (γ (e i)) (C' i) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hh := hhalf (e i) (e i).2
    change mu p k (γ (e i)) (C (e i)) ≤ 2 * mu p k (γ (e i)) (C' i) at hh
    rw [hz, mul_zero] at hh
    exact (not_le_of_gt (hchart (e i)).1) hh
  have hEmass : (∑ a, ENNReal.ofReal (weight p k a) * mu p k a (G a)ᶜ) ≤ 1 := by
    apply le_trans _ (hp.weighted_mass_le k)
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_left (measure_mono (subset_univ _)) zero_le
  have hEfin : 3 * (∑ a, ENNReal.ofReal (weight p k a) * mu p k a (G a)ᶜ) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ne_top_of_le_ne_top (by norm_num) hEmass)
  have hretmass : ENNReal.ofReal (N p k ^ (-ε)) ≤
      ∑ a, ENNReal.ofReal (weight p k a) *
        mu p k a {q | ∃ i ∈ F, γ i = a ∧ q ∈ C i ∩ G a} :=
    (ENNReal.add_le_add_iff_right hEfin).mp (hbudget.trans hret)
  have houtmass : ENNReal.ofReal (N p k ^ (-ε)) ≤
      ∑ a, ENNReal.ofReal (weight p k a) *
        mu p k a {q | ∃ i : Fin F.card, γ (e i) = a ∧ q ∈ C' i} := by
    apply hretmass.trans
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left _ zero_le
    apply measure_mono
    intro q hq
    obtain ⟨i, hi, hγ, hq⟩ := hq
    refine ⟨e.symm ⟨i, hi⟩, ?_, ?_⟩
    · simpa using hγ
    · simpa only [C', Equiv.apply_symm_apply] using
        (show q ∈ C i ∩ G (γ i) from ⟨hq.1, by simpa [hγ] using hq.2⟩)
  refine ⟨T, F.card, fun i => γ (e i), fun i => j (e i), fun i => A (e i),
    C', fun i => u (e i), fun i => v (e i), fun i => J (e i), fun i => P (e i), L', ?_⟩
  rw [chartData_iff_raw_and_lists]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨hT', ?_, (fun i => ⟨(hm' (e i)).1, hC'm i⟩), ?_, ?_, ?_, houtmass⟩
    · exact (Nat.cast_le.mpr (by simpa using F.card_le_univ)).trans hn'
    · intro i i' hii hγ hj
      exact hdisj' (e i) (e i') (fun h => hii (he h)) hγ hj
    · intro i q hq
      exact hsub' (e i) hq.1
    · intro i
      rcases hchart' (e i) with ⟨hμ, hJ, hJinv, hJup, hctr, hdeg, hcoef, hA, hAf, hCf, hfit, hfloor⟩
      refine ⟨hC'pos i, hJ, hJinv, hJup, hctr, hdeg, hcoef, hA, hAf,
        (fun z => hformat (e i) z), hfit, ?_⟩
      intro ht
      have hold := (hchart (e i)).2.2.2.2.2.2.2.2.2.2.2 rfl
      have htwo : 2 * ENNReal.ofReal
          (N p k ^ (-profile p r) * J (e i) / (N p k ^ ε * (2 : ℝ) ^ T)) ≤
          ENNReal.ofReal (N p k ^ (-profile p r) * J (e i) / (N p k ^ δ * (2 : ℝ) ^ T)) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (two_div_le
          (mul_nonneg (Real.rpow_pos_of_pos hN0 _).le hJ.le)
          (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos hN0 _) (by positivity) hgap)
      have hh := htwo.trans (hold.trans (hhalf (e i) (e i).2))
      apply (ENNReal.mul_le_mul_iff_left (c := 2) (by norm_num) (by norm_num)).mp
      simpa only [mul_comm] using hh
  · intro a z
    have hc := (Nat.cast_le (α := ℝ)).mpr (reindexed_list_card (fun i => (e i : Fin n)) he
      (boundedLabels γ X R a z))
    exact hc.trans ((boundedLabels_card γ X hR0 a z).trans hR)
  · intro a i
    simpa only [L', Finset.mem_filter, Finset.mem_univ, true_and] using
      boundedLabels_measurable γ X hX R a (e i)
  · intro i
    have hempty : {q | q ∈ C' i ∧
        i ∉ L' (γ (e i)) ((![q.2, y q.1 q.2] : Fin 2 → ℝ), ⌊x q.1 q.2 / (N p k ^ (-r))⌋)} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      apply hq.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (mem_boundedLabels γ X R _ _ _).mpr ?_⟩
      exact ⟨hknown _ q hq.1.2, rfl, hcross (e i) q hq.1.1⟩
    rw [hempty, measure_empty]

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
