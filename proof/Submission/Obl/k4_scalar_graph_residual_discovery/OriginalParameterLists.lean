/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalParameterLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.GraphLists
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalRows

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Lib.K4CommonLocalChoice

namespace ScalarData

/-- The frozen parameter lists imply that each original fine state and
coarse velocity bin meets only a bounded list of full coefficient worlds.
This is the count used when summing the OLD posterior reference weights. -/
theorem prepData.original_fine_state_parameter_lists {D : ScalarData}
    {H : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E₀) (hN : ∀ k, 2 ≤ D.N k) :
    ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ D.N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧
      M = D.prepMesh hprep ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ g : Fin (D.W k), ∀ r : ℝ,
        R⁻¹ ≤ r → r ≤ R → (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) →
        ∀ B : ℝ, r ≤ B → ∀ E' : Set ScalarIncidence,
        (∀ z ∈ E', (D.ρ k g).restrict (E₀ k g)
          {p | D.phys k r p = D.phys k r z ∧ D.coeff k r p.1 = D.coeff k r z.1} ≠ 0) →
        ∀ (w : Fin 3 → ℤ) (c : ℤ), ∃ L : Finset (Fin 5 → ℤ),
          (L.card : ℝ) ≤ 8 * H k ∧
          ∀ z ∈ E', D.phys k B z = w → D.coeff k r z.1 1 = c → D.coeff k r z.1 ∈ L := by
  let M := D.prepMesh hprep
  obtain ⟨hM, hdata⟩ := Classical.choose_spec hprep.2
  refine ⟨M, hM, rfl, ?_⟩
  intro R hR
  filter_upwards [hdata R hR] with k hk
  intro g r hrlo hrhi hrgrid B hrB E' hpositive w c
  classical
  obtain ⟨_, _, hEmeas, hbound, _, _, _, hgrid, _⟩ := hk.2 g
  obtain ⟨_, _, _, _, hparam⟩ := hgrid r hrlo hrhi hrgrid
  let μ := (D.ρ k g).restrict (E₀ k g)
  let ρ := D.N k ^ (-r)
  have hN0 : 0 < D.N k := by linarith [hN k]
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hN0 _
  have hcoeffae : ∀ᵐ p ∂μ, ∀ e, |p.1.2 e| ≤ H k := by
    apply (ae_restrict_iff' hEmeas).mpr
    exact Filter.Eventually.of_forall (fun p hp => (hbound p hp).2)
  have hcoeff (l : ScalarLine) : D.coeff k r l = cell ρ l.2 := by funext e; rfl
  let S (q : Fin 3 → ℤ) (v : ℤ) : Set (Fin 5 → ℤ) :=
    {b | μ {p | D.phys k r p = q ∧ D.coeff k r p.1 1 = v ∧ D.coeff k r p.1 = b} ≠ 0}
  have hSeq (q : Fin 3 → ℤ) (v : ℤ) : S q v =
      positiveRowValues μ (fun p => (D.phys k r p, D.coeff k r p.1 1))
        (fun p => p.1.2) ρ (q, v) := by
    ext b
    have heq : {p : ScalarIncidence | D.phys k r p = q ∧
        D.coeff k r p.1 1 = v ∧ D.coeff k r p.1 = b} =
        {p : ScalarIncidence | (D.phys k r p, D.coeff k r p.1 1) = (q, v) ∧
          cell ρ p.1.2 = b} := by
      ext p
      simp only [mem_ofPred_eq, Prod.mk.injEq, hcoeff, and_assoc]
    simp only [S, positiveRowValues, mem_ofPred_eq, heq]
  have hS (q : Fin 3 → ℤ) (v : ℤ) : (S q v).Finite := by
    rw [hSeq]
    exact finite_positiveRowValues μ _ _ hρ hcoeffae (q, v)
  let F (q : Fin 3 → ℤ) (v : ℤ) := (hS q v).toFinset
  have hFcard (q : Fin 3 → ℤ) (v : ℤ) : ((F q v).card : ℝ) ≤ H k := by
    rw [← Set.ncard_eq_toFinset_card _ (hS q v)]
    exact hparam q v
  let Q := successorCells (cell ρ (leftCorner (D.N k ^ (-B)) w))
  let L := Q.biUnion (fun q => F q c)
  have hphys (s : ℝ) (p : ScalarIncidence) :
      D.phys k s p = cell (D.N k ^ (-s)) (scalarPosition p) := by funext e; rfl
  have hb : 0 < D.N k ^ (-B) := Real.rpow_pos_of_pos hN0 _
  have hbρ : D.N k ^ (-B) ≤ ρ :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [hN k]) (by linarith)
  refine ⟨L, ?_, ?_⟩
  · calc
      (L.card : ℝ) ≤ ∑ q ∈ Q, ((F q c).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s := Q) (t := fun q => F q c)
      _ ≤ ∑ _q ∈ Q, H k := Finset.sum_le_sum (fun q _ => hFcard q c)
      _ = 8 * H k := by simp only [Q, card_successorCells, Finset.sum_const, nsmul_eq_mul]; norm_num
  · intro z hz hw hc
    have hcoarse : D.phys k r z ∈ Q := by
      have h := cell_mem_successorCells hb hbρ (scalarPosition z)
      have hw' : cell (D.N k ^ (-B)) (scalarPosition z) = w := by simpa only [hphys] using hw
      simpa only [Q, hphys, hw'] using h
    apply Finset.mem_biUnion.mpr
    refine ⟨D.phys k r z, hcoarse, (hS _ _).mem_toFinset.mpr ?_⟩
    change μ {p | D.phys k r p = D.phys k r z ∧
      D.coeff k r p.1 1 = c ∧ D.coeff k r p.1 = D.coeff k r z.1} ≠ 0
    have heq : {p | D.phys k r p = D.phys k r z ∧
        D.coeff k r p.1 1 = c ∧ D.coeff k r p.1 = D.coeff k r z.1} =
        {p | D.phys k r p = D.phys k r z ∧ D.coeff k r p.1 = D.coeff k r z.1} := by
      ext p
      constructor
      · exact fun hp => ⟨hp.1, hp.2.2⟩
      · rintro ⟨hp, hq⟩
        exact ⟨hp, by rw [hq]; exact hc, hq⟩
    rw [heq]
    exact hpositive z hz

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
