/- Adapted from same-tree o093/x0544, FinerKnowledge.lean. -/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartTransport
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GridCaps

/-! A finer original hidden observation retains the same atlas with only a
fixed list factor. In particular terminal lists can be supplied for original
intermediate true layers without altering their assignments or selected sets. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open MeasureTheory Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem chartData_finerKnowledge {p : Code} {B k T n : ℕ}
    {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set (ℕ × (Fin 5 → ℝ))}
    {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    {r b b' h ε ε' : ℝ} {isTrue : Bool}
    (hN : 1 ≤ N p k) (hbb : b ≤ b') (hε : ε ≤ ε')
    (hbudget : 4 * N p k ^ ε ≤ N p k ^ ε')
    (hc : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ) :
    ∃ Λ', ChartData p B r b' h ε' isTrue k T n γ j A C u v J P Λ' := by
  classical
  have hNpos : 0 < N p k := zero_lt_one.trans_le hN
  let bins := overlapBins (N p k ^ (-b)) (N p k ^ (-b'))
    (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hNpos _)
  let Λ' : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n) :=
    fun a => transferGridList bins (Λ a)
  have hlarge := chartData_mono p B k T n γ j A C u v J P Λ r b h h ε ε' isTrue
    hN le_rfl hε hc
  rcases hc with ⟨ht, hn, hm, hd, hC, hg, hsize, hmeas, hlist, hmass⟩
  rcases hlarge with ⟨ht', hn', hm', hd', hC', hg', hsize', hmeas', hlist', hmass'⟩
  refine ⟨Λ', ht', hn', hm', hd', hC', hg', ?_, ?_, ?_, hmass'⟩
  · intro a z
    have hcard : ((bins z.2).card : ℝ) ≤ 4 := by
      exact_mod_cast GridCaps.overlapBins_card_le_four _ _ _ _
        (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hbb)) z.2
    calc
      _ ≤ ((bins z.2).card : ℝ) * N p k ^ ε :=
        transferGridList_card bins (Λ a) z _ (fun c _ => hsize a (z.1, c))
      _ ≤ 4 * N p k ^ ε := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hNpos.le _)
      _ ≤ _ := hbudget
  · intro a i
    exact measurableSet_transferGridList bins (Λ a) (hmeas a) i
  · intro i
    apply le_zero_iff.1
    rw [← hlist i]
    apply measure_mono
    intro q hq
    refine ⟨hq.1, ?_⟩
    intro hold
    apply hq.2
    exact transferGridList_mem bins (Λ (γ i))
      ((![q.2, y q.1 q.2] : Fin 2 → ℝ), ⌊x q.1 q.2 / (N p k ^ (-b'))⌋)
      ⌊x q.1 q.2 / (N p k ^ (-b))⌋ i
      (floor_mem_overlapBins _ _ _ _ _) hold

theorem chart_finerKnowledge {p : Code} {B k : ℕ} {r b b' h ε ε' : ℝ} {isTrue : Bool}
    (hN : 1 ≤ N p k) (hbb : b ≤ b') (hε : ε ≤ ε')
    (hbudget : 4 * N p k ^ ε ≤ N p k ^ ε')
    (hc : Chart p B r b h ε isTrue k) : Chart p B r b' h ε' isTrue k := by
  rcases hc with ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hc⟩
  obtain ⟨Λ', hΛ⟩ := chartData_finerKnowledge hN hbb hε hbudget hc
  exact ⟨T, n, γ, j, A, C, u, v, J, P, Λ', hΛ⟩

/-- Knowledge at any original depth remains knowledge at every finer
depth, with the identical asymptotic horizon and fixed atlas complexity. -/
theorem known_finerKnowledge {p : Code} (hp : Exact p) {r b b' h : ℝ}
    (hbb : b ≤ b') (hk : Known p r b h) : Known p r b' h := by
  rcases hk with ⟨hh, B, hB, hc⟩
  refine ⟨hh, B, hB, ?_⟩
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hlarge : ∀ᶠ k in atTop, 4 ≤ N p k ^ (ε / 2) :=
    ((tendsto_rpow_atTop hhalf).comp hp.1.2.1).eventually_ge_atTop 4
  apply ((hc (ε / 2) hhalf).and_eventually hlarge).mono
  rintro k ⟨hchart, hfour⟩
  have hN : 1 ≤ N p k := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1.1 k)
  have hbudget : 4 * N p k ^ (ε / 2) ≤ N p k ^ ε := by
    calc
      _ ≤ N p k ^ (ε / 2) * N p k ^ (ε / 2) :=
        mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg (by linarith [hp.1.1 k]) _)
      _ = _ := by rw [← Real.rpow_add (by linarith [hp.1.1 k])]; congr 1; ring
  have hnew := chart_finerKnowledge hN hbb (by linarith : ε / 2 ≤ ε) hbudget hchart
  exact chart_mono p B k r b' (h + ε / 2) (h + ε) ε ε false hN (by linarith) le_rfl hnew

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
