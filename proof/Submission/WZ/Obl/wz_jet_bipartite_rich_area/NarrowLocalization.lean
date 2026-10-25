-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.NarrowLocalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.CoefficientRefinement
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.TimeWindowCover
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.NearPairs
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.FirstMoment

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open MeasureTheory Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- The union of narrow intersections has the elementary one-strip bound. -/
theorem volume_narrow_union_le_firstMoment {n : ℕ}
    (A B : Finset (Fin n)) (q : Fin n → EuclideanSpace ℝ (Fin 3))
    (g : Fin n → ℝ → ℝ) {δ κ : ℝ} (hδ : 0 ≤ δ)
    (hg : ∀ i ∈ A, Continuous (g i)) :
    volume (⋃ i ∈ A, ⋃ j ∈ B, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ≤
      ENNReal.ofReal (4*δ*((A.card:ℝ)+(B.card:ℝ))) := by
  classical
  have hsub : (⋃ i ∈ A, ⋃ j ∈ B, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ⊆
      ⋃ i ∈ A, strip δ (g i) := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hp
    obtain ⟨j, hj, hp⟩ := mem_iUnion₂.mp hp
    exact mem_iUnion₂.mpr ⟨i, hi, hp.1.1⟩
  calc
    _ ≤ volume (⋃ i ∈ A, strip δ (g i)) := measure_mono hsub
    _ ≤ ∑ i ∈ A, volume (strip δ (g i)) := measure_biUnion_finset_le _ _
    _ = ∑ _i ∈ A, ENNReal.ofReal (4*δ) :=
      Finset.sum_congr rfl (fun i hi => volume_strip δ (hg i hi))
    _ = ENNReal.ofReal ((A.card:ℝ)*(4*δ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg A.card)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [Nat.cast_nonneg (α := ℝ) B.card])

/-- Large slope thresholds are covered by the linear term of the desired
union estimate. -/
theorem volume_narrow_union_le_of_large_threshold {n : ℕ}
    (A B : Finset (Fin n)) (q : Fin n → EuclideanSpace ℝ (Fin 3))
    (g : Fin n → ℝ → ℝ) {δ κ D ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε) (hκ : 1/100000 ≤ κ)
    (hg : ∀ i ∈ A, Continuous (g i)) :
    volume (⋃ i ∈ A, ⋃ j ∈ B, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ≤
      ENNReal.ofReal (400000*δ^(-ε)*δ*
        (Real.sqrt (δ/D)*((A.card:ℝ)+(B.card:ℝ))*Real.sqrt ((A.card:ℝ)+(B.card:ℝ))+
          κ*((A.card:ℝ)+(B.card:ℝ)))) := by
  apply (volume_narrow_union_le_firstMoment A B q g hδ.le hg).trans
  apply ENNReal.ofReal_le_ofReal
  have hp : 1 ≤ δ^(-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hκ0 : 0 ≤ κ := by linarith
  have hN : 0 ≤ (A.card:ℝ)+(B.card:ℝ) := by positivity
  have hr : 0 ≤ Real.sqrt (δ/D)*((A.card:ℝ)+(B.card:ℝ))*Real.sqrt ((A.card:ℝ)+(B.card:ℝ)) := by positivity
  have hsmall : 4*((A.card:ℝ)+(B.card:ℝ)) ≤
      400000*(κ*((A.card:ℝ)+(B.card:ℝ))) := by nlinarith [mul_le_mul_of_nonneg_right hκ hN]
  calc
    _ ≤ δ*(400000*(κ*((A.card:ℝ)+(B.card:ℝ)))) := by nlinarith only [mul_le_mul_of_nonneg_left hsmall hδ.le]
    _ ≤ δ*(400000*δ^(-ε)*(κ*((A.card:ℝ)+(B.card:ℝ)))) := by gcongr; linarith
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ 400000*δ^(-ε)*δ by positivity) hr]

/-- A uniform estimate for refined coefficient clusters and fixed short
time windows sums to a global narrow-union estimate. -/
theorem volume_narrow_union_le_of_refined_windows {n : ℕ}
    (A B : Finset (Fin n)) (q : Fin n → EuclideanSpace ℝ (Fin 3))
    (g : Fin n → ℝ → ℝ) {D θ δ κ T : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hT : 0 ≤ T)
    (hA : ∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D)
    (hB : ∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ D)
    (hlocal : ∀ F ⊆ A, ∀ G ⊆ B,
      (∀ i ∈ F, ∀ j ∈ F, dist (q i) (q j) ≤ θ*D) →
      (∀ i ∈ G, ∀ j ∈ G, dist (q i) (q j) ≤ θ*D) →
      ∀ w : Fin 20000,
      volume ((⋃ i ∈ F, ⋃ j ∈ G, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ∩
        {p : ℝ × ℝ | p.2 ∈ Icc (timeWindowLeft w) (timeWindowRight w)}) ≤
        ENNReal.ofReal (T*((F.card:ℝ)+(G.card:ℝ))*Real.sqrt ((F.card:ℝ)+(G.card:ℝ)))) :
    volume (⋃ i ∈ A, ⋃ j ∈ B, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ≤
      ENNReal.ofReal ((20000*(27648/θ^3)^2*T)*
        ((A.card:ℝ)+(B.card:ℝ))*Real.sqrt ((A.card:ℝ)+(B.card:ℝ))) := by
  classical
  obtain ⟨k, hk, F, hFA, -, hFc, hFd⟩ := exists_coefficient_refinement A q hD hθ hθ1 hA
  obtain ⟨m, hm, G, hGB, -, hGc, hGd⟩ := exists_coefficient_refinement B q hD hθ hθ1 hB
  let N : ℝ := (A.card:ℝ)+(B.card:ℝ)
  let U (z : Fin k × Fin m × Fin 20000) : Set (ℝ × ℝ) :=
    (⋃ i ∈ F z.1, ⋃ j ∈ G z.2.1, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ∩
      {p | p.2 ∈ Icc (timeWindowLeft z.2.2) (timeWindowRight z.2.2)}
  have hsub : (⋃ i ∈ A, ⋃ j ∈ B, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ⊆
      ⋃ z, U z := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hp
    obtain ⟨j, hj, hp⟩ := mem_iUnion₂.mp hp
    obtain ⟨a, ha⟩ := hFc i hi
    obtain ⟨b, hb⟩ := hGc j hj
    obtain ⟨w, hw⟩ := exists_mem_timeWindow hp.1.1.1
    exact mem_iUnion.mpr ⟨(a,b,w), mem_iUnion₂.mpr ⟨i, ha,
      mem_iUnion₂.mpr ⟨j,hb,hp⟩⟩, hw⟩
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hpiece (z : Fin k × Fin m × Fin 20000) :
      volume (U z) ≤ ENNReal.ofReal (T*N*Real.sqrt N) := by
    apply (hlocal (F z.1) (hFA z.1) (G z.2.1) (hGB z.2.1)
      (hFd z.1) (hGd z.2.1) z.2.2).trans
    apply ENNReal.ofReal_le_ofReal
    have hmass : ((F z.1).card:ℝ)+((G z.2.1).card:ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast Nat.add_le_add (Finset.card_le_card (hFA z.1)) (Finset.card_le_card (hGB z.2.1))
    gcongr
  calc
    _ ≤ volume (⋃ z, U z) := measure_mono hsub
    _ ≤ ∑ z, volume (U z) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _z : Fin k × Fin m × Fin 20000, ENNReal.ofReal (T*N*Real.sqrt N) :=
      Finset.sum_le_sum (fun z _ => hpiece z)
    _ = ENNReal.ofReal (((k:ℝ)*(m:ℝ)*20000)*(T*N*Real.sqrt N)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), Nat.cast_mul]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hkm : (k:ℝ)*(m:ℝ) ≤ (27648/θ^3)^2 := by
        calc
          _ ≤ (27648/θ^3)*(27648/θ^3) := mul_le_mul hk hm (Nat.cast_nonneg _) (by positivity)
          _ = _ := by ring
      dsimp [N] at *
      nlinarith [mul_le_mul_of_nonneg_right hkm
        (show 0 ≤ 20000*(T*((A.card:ℝ)+(B.card:ℝ))*Real.sqrt ((A.card:ℝ)+(B.card:ℝ))) by positivity)]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
