-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.Quantization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Frostman

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- Keep the occupied cells of a finite closed-ball cover, and choose a point
of the original set in each occupied cell. -/
theorem exists_occupied_model {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    {δ N : ℝ} {Q : Set X} (c : I → X)
    (hcov : Q ⊆ ⋃ i, Metric.closedBall (c i) δ) (hN : CoverLower δ Q N) :
    ∃ H : Finset I, N ≤ (H.card : ℝ) ∧
      Q ⊆ ⋃ i ∈ H, Metric.closedBall (c i) δ ∧
      ∃ p : H → X, ∀ i, p i ∈ Q ∧ dist (p i) (c i.val) ≤ δ := by
  classical
  let H : Finset I := Finset.univ.filter (fun i => ∃ x ∈ Q, dist x (c i) ≤ δ)
  have hHcov : Q ⊆ ⋃ i ∈ H, Metric.closedBall (c i) δ := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    have hiH : i ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ i, x, hx, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hiH, hi⟩⟩
  have hNH : N ≤ (H.card : ℝ) := by
    let e := Fintype.equivFin H
    let d : Fin (Fintype.card H) → X := fun i => c (e.symm i).val
    have hd : Covers δ Q d := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hHcov hx)
      obtain ⟨hiH, hxi⟩ := Set.mem_iUnion.mp hi
      exact Set.mem_iUnion.mpr ⟨e ⟨i, hiH⟩, by simpa [d] using hxi⟩
    simpa using hN (Fintype.card H) d hd
  have hp : ∀ i : H, ∃ x ∈ Q, dist x (c i.val) ≤ δ :=
    fun i => (Finset.mem_filter.mp i.property).2
  choose p hpQ hpdist using hp
  exact ⟨H, hNH, hHcov, p, fun i => ⟨hpQ i, hpdist i⟩⟩

def tripleCenter {S T : Finset Plane} (i : S × T × T) : Triple :=
  (i.1.val, i.2.1.val, i.2.2.val)

/-- Finite hypergraph encoding of the original triple set, with actual triples
chosen as witnesses and a sharp bound on the number of occupied cells. -/
theorem exists_tripartite_model {δ N : ℝ} {F G : Set Plane} {Q : Set Triple}
    (hQ : Q ⊆ F ×ˢ (G ×ˢ G)) (hN : CoverLower δ Q N)
    (S T : Finset Plane)
    (hS : ∀ x ∈ F, ∃ a ∈ S, dist x a ≤ δ)
    (hT : ∀ x ∈ G, ∃ a ∈ T, dist x a ≤ δ) :
    ∃ H : Finset (S × T × T), N ≤ (H.card : ℝ) ∧
      Q ⊆ ⋃ i ∈ H, Metric.closedBall (tripleCenter i) δ ∧
      ∃ p : H → Triple, ∀ i, p i ∈ Q ∧ dist (p i) (tripleCenter i.val) ≤ δ := by
  have hcov : Q ⊆ ⋃ i : S × T × T, Metric.closedBall (tripleCenter i) δ := by
    intro p hp
    have hp' := hQ hp
    obtain ⟨a, ha, hpa⟩ := hS p.1 hp'.1
    obtain ⟨b, hb, hpb⟩ := hT p.2.1 hp'.2.1
    obtain ⟨c, hc, hpc⟩ := hT p.2.2 hp'.2.2
    refine Set.mem_iUnion.mpr ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩), ?_⟩
    simpa [Metric.mem_closedBall, tripleCenter, Prod.dist_eq, max_le_iff] using
      And.intro hpa (And.intro hpb hpc)
  exact exists_occupied_model tripleCenter hcov hN

noncomputable def dotValue (p : Triple) : ℝ := inner ℝ p.1 (p.2.1 - p.2.2)

/-- An explicit Lipschitz estimate on the bounded region used by the theorem. -/
theorem dotValue_sub_le {p q : Triple}
    (hp₁ : ‖p.2.1‖ ≤ 2) (hp₂ : ‖p.2.2‖ ≤ 2) (hq : ‖q.1‖ ≤ 2) :
    |dotValue p - dotValue q| ≤ 8 * dist p q := by
  have ha : ‖p.1 - q.1‖ ≤ dist p q := by
    rw [← dist_eq_norm]
    exact le_max_left _ _
  have hb : ‖p.2.1 - q.2.1‖ ≤ dist p q := by
    rw [← dist_eq_norm]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hc : ‖p.2.2 - q.2.2‖ ≤ dist p q := by
    rw [← dist_eq_norm]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hd : ‖p.2.1 - p.2.2‖ ≤ 4 := by
    have hn := norm_sub_le p.2.1 p.2.2
    linarith
  have he : ‖(p.2.1 - q.2.1) - (p.2.2 - q.2.2)‖ ≤ 2 * dist p q := by
    have hn := norm_sub_le (p.2.1 - q.2.1) (p.2.2 - q.2.2)
    linarith
  have hid : dotValue p - dotValue q =
      inner ℝ (p.1 - q.1) (p.2.1 - p.2.2) +
        inner ℝ q.1 ((p.2.1 - q.2.1) - (p.2.2 - q.2.2)) := by
    simp only [dotValue, inner_sub_left, inner_sub_right]
    ring
  rw [hid]
  calc
    |inner ℝ (p.1 - q.1) (p.2.1 - p.2.2) +
        inner ℝ q.1 ((p.2.1 - q.2.1) - (p.2.2 - q.2.2))|
        ≤ |inner ℝ (p.1 - q.1) (p.2.1 - p.2.2)| +
          |inner ℝ q.1 ((p.2.1 - q.2.1) - (p.2.2 - q.2.2))| := abs_add_le _ _
    _ ≤ ‖p.1 - q.1‖ * ‖p.2.1 - p.2.2‖ +
        ‖q.1‖ * ‖(p.2.1 - q.2.1) - (p.2.2 - q.2.2)‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ dist p q * 4 + 2 * (2 * dist p q) := by gcongr
    _ = 8 * dist p q := by ring

theorem dotValue_sub_le_of_square {δ : ℝ} {F G : Set Plane}
    (hF : InUnitSquare F) (hG : InUnitSquare G) {p q : Triple}
    (hp : p ∈ F ×ˢ (G ×ˢ G)) (hq : q ∈ F ×ˢ (G ×ˢ G)) (hpq : dist p q ≤ δ) :
    |dotValue p - dotValue q| ≤ 8 * δ :=
  (dotValue_sub_le (hG.norm_le_two hp.2.1) (hG.norm_le_two hp.2.2)
    (hF.norm_le_two hq.1)).trans (mul_le_mul_of_nonneg_left hpq (by norm_num))

end WangZahlLot.Obl.wz_separated_projection_dichotomy
