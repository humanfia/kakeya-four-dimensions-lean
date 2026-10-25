-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.TripleRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Refinement
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Basic

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open scoped BigOperators

noncomputable def tripleProjection (i : Fin 6) (p : Triple) : Plane × Plane :=
  ![(p.1, 0), (p.2.1, 0), (p.2.2, 0), (p.1, p.2.1), (p.1, p.2.2), (p.2.1, p.2.2)] i

def tripleFiberCapacity (F G U : Finset Plane) (i : Fin 6) : ℝ :=
  ![(G.card : ℝ) * U.card, (F.card : ℝ) * U.card, (F.card : ℝ) * G.card,
    (U.card : ℝ), (G.card : ℝ), (F.card : ℝ)] i

/-- Uniform lower bounds for all nontrivial coordinate fibers of a triple
hypergraph. The capacities are measured in its specified ambient factors. -/
def TripleUniform (d : ℝ) (F G U : Finset Plane) (H : Finset Triple) : Prop := by
  classical
  exact ∀ i p, p ∈ H → d * tripleFiberCapacity F G U i ≤
    ((H.filter (fun q => tripleProjection i q = tripleProjection i p)).card : ℝ)

/-- All six proper coordinate projections can be made uniform while keeping
at least half the edges. -/
theorem exists_triple_uniform_refinement {F G U : Finset Plane} {H : Finset Triple}
    {d : ℝ} (hd : 0 ≤ d) (hH : H ⊆ F ×ˢ (G ×ˢ U))
    (hdensity : d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ)) :
    ∃ S ⊆ H, (H.card : ℝ) / 2 ≤ (S.card : ℝ) ∧ TripleUniform (d / 12) F G U S := by
  classical
  let L : Fin 6 → Finset (Plane × Plane) :=
    ![F ×ˢ {0}, G ×ˢ {0}, U ×ˢ {0}, F ×ˢ G, F ×ˢ U, G ×ˢ U]
  have hproj : ∀ i, H.image (tripleProjection i) ⊆ L i := by
    intro i p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hq' := Finset.mem_product.mp (hH hq)
    have hq'' := Finset.mem_product.mp hq'.2
    fin_cases i <;> simp [L, tripleProjection, hq'.1, hq''.1, hq''.2]
  let threshold (i : Fin 6) := (d / 12) * tripleFiberCapacity F G U i
  have hthreshold : ∀ i, 0 ≤ threshold i := by
    intro i
    fin_cases i <;> dsimp [threshold, tripleFiberCapacity] <;> positivity
  obtain ⟨S, hSH, hcard, hfiber⟩ := exists_dense_fiber_refinement H tripleProjection threshold hthreshold
  have hbudget : ∑ i, threshold i * ((H.image (tripleProjection i)).card : ℝ) ≤
      d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) / 2 := by
    calc ∑ i, threshold i * ((H.image (tripleProjection i)).card : ℝ) ≤
          ∑ i, threshold i * ((L i).card : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            apply mul_le_mul_of_nonneg_left _ (hthreshold i)
            exact_mod_cast Finset.card_le_card (hproj i)
      _ = _ := by
        simp [Fin.sum_univ_succ, threshold, tripleFiberCapacity, L, Finset.card_product]
        ring
  refine ⟨S, hSH, by linarith, ?_⟩
  exact hfiber

theorem TripleUniform.fiber_second {d : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) (p : Triple) (hp : p ∈ H) :
    d * (G.card : ℝ) ≤ ((H.filter (fun q => q.1 = p.1 ∧ q.2.2 = p.2.2)).card : ℝ) := by
  classical
  simpa [tripleFiberCapacity, tripleProjection] using h 4 p hp

theorem TripleUniform.fiber_third {d : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) (p : Triple) (hp : p ∈ H) :
    d * (U.card : ℝ) ≤ ((H.filter (fun q => q.1 = p.1 ∧ q.2.1 = p.2.1)).card : ℝ) := by
  classical
  simpa [tripleFiberCapacity, tripleProjection] using h 3 p hp

theorem TripleUniform.row_third {d : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) (p : Triple) (hp : p ∈ H) :
    d * ((F.card : ℝ) * G.card) ≤ ((H.filter (fun q => q.2.2 = p.2.2)).card : ℝ) := by
  classical
  simpa [tripleFiberCapacity, tripleProjection] using h 2 p hp

theorem TripleUniform.row_second {d : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) (p : Triple) (hp : p ∈ H) :
    d * ((F.card : ℝ) * U.card) ≤ ((H.filter (fun q => q.2.1 = p.2.1)).card : ℝ) := by
  classical
  simpa [tripleFiberCapacity, tripleProjection] using h 1 p hp

end WangZahlLot.Obl.wz_separated_projection_dichotomy
