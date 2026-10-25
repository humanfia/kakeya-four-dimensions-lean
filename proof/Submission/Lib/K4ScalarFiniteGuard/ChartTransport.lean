/-
Adapted from: here:o093
Original proofs by session x0535 in this LOT workspace. The scalar atlas
interface was written in the same o093 tree by x0364; this package retains
its literal fields while requiring only the sampling hypotheses used here.
-/

import Submission.Lib.K4ScalarFiniteGuard.GridLists
import Submission.Lib.K4ScalarFiniteGuard.ChartMonotonicity

/-!
Transport actual scalar atlases between nearby thickness and observation
exponents. Selected incidences and full assignments remain unchanged.
-/

set_option autoImplicit false

namespace Submission.Lib.K4ScalarFiniteGuard

open MeasureTheory

/-- Transfer observation knowledge by compatible power-grid lists. This
retains the full atlas and selected original incidences. -/
theorem chart_changeKnowledge (p : Code) (B k : ℕ) (r b b' h ε ε' : ℝ) (isTrue : Bool)
    (hN : 1 ≤ N p k) (hε : ε ≤ ε')
    (hbudget : 4 * N p k ^ (ε + |b - b'|) ≤ N p k ^ ε')
    (hc : Chart p B r b h ε isTrue k) : Chart p B r b' h ε' isTrue k := by
  classical
  rcases hc with ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hc⟩
  have hNpos : 0 < N p k := lt_of_lt_of_le zero_lt_one hN
  let bins := overlapBins (N p k ^ (-b)) (N p k ^ (-b'))
    (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hNpos _)
  let Λ' : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n) :=
    fun a => transferGridList bins (Λ a)
  have hlarge := chartData_mono p B k T n γ j A C u v J P Λ r b h h ε ε' isTrue
    hN le_rfl hε hc
  rcases hc with ⟨ht, hn, hm, hd, hC, hg, hsize, hmeas, hlist, hmass⟩
  rcases hlarge with ⟨ht', hn', hm', hd', hC', hg', hsize', hmeas', hlist', hmass'⟩
  refine ⟨T, n, γ, j, A, C, u, v, J, P, Λ', ht', hn', hm', hd', hC', hg',
    ?_, ?_, ?_, hmass'⟩
  · intro a z
    have hc := transferGridList_card bins (Λ a) z (N p k ^ ε)
      (fun c _ => hsize a (z.1, c))
    change ((transferGridList bins (Λ a) z).card : ℝ) ≤ _
    calc
      _ ≤ ((bins z.2).card : ℝ) * N p k ^ ε := hc
      _ ≤ (4 * N p k ^ |b - b'|) * N p k ^ ε :=
        mul_le_mul_of_nonneg_right (power_overlapBins_card (N p k) b b' hN z.2)
          (Real.rpow_nonneg hNpos.le _)
      _ = 4 * N p k ^ (ε + |b - b'|) := by
        rw [Real.rpow_add hNpos]
        ring
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

/-- A known atlas can be moved to a nearby thickness by its actual power
loss. No true-floor condition is asserted in this transport. -/
theorem chart_changeThickness (p : Code) (B k : ℕ) (r r' b h ε ε' : ℝ)
    (hN : 1 ≤ N p k) (hε : ε ≤ ε') (hdepth : ε - r ≤ ε' - r')
    (hc : Chart p B r b h ε false k) : Chart p B r' b h ε' false k := by
  rcases hc with ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hc⟩
  have hNpos : 0 < N p k := lt_of_lt_of_le zero_lt_one hN
  have hlarge := chartData_mono p B k T n γ j A C u v J P Λ r b h h ε ε' false
    hN le_rfl hε hc
  rcases hc with ⟨ht, hn, hm, hd, hC, hg, hsize, hmeas, hlist, hmass⟩
  rcases hlarge with ⟨ht', hn', hm', hd', hC', hg', hsize', hmeas', hlist', hmass'⟩
  refine ⟨T, n, γ, j, A, C, u, v, J, P, Λ, ht', hn', hm', hd', hC',
    ?_, hsize', hmeas', hlist', hmass'⟩
  intro i
  rcases hg' i with ⟨hpos, hJ, hinv, hwidth, hcenter, hdegree, hcoeff, hsupport,
    hAfmt, hCfmt, hfit, hfloor⟩
  refine ⟨hpos, hJ, hinv, hwidth, hcenter, hdegree, hcoeff, hsupport,
    hAfmt, hCfmt, ?_, by simp⟩
  intro l hl t ht
  refine ⟨(hfit l hl t ht).1, ?_⟩
  rcases hg i with ⟨_, _, _, _, _, _, _, _, _, _, hfitOld, _⟩
  apply (hfitOld l hl t ht).2.trans
  rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end Submission.Lib.K4ScalarFiniteGuard
