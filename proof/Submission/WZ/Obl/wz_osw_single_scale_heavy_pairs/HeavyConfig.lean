-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.HeavyConfig.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.SingleScale
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.Bushes
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.Counting

/-!
# The configuration of heavy strips at one scale

For a thin relation `E ⊆ G ×ˢ G'` and a scale `r`, the heavy normals at `b` are
the unit `e` whose strip `strip E b e r` holds at least `lam = r ^ (σ + τ) * #G'`
points.  A finite maximal `16 r`-separated set `D` of heavy normals at `b`

* covers the heavy pairs at `b` by the strips of half-width `129 r` of its
  normals, so `#{b' | (b, b') heavy} ≤ #D * K * (129 r) ^ σ * #G'`;
* is Katz-Tao: at most `K * (9 ρ) ^ σ * #G' / lam` of its normals lie within `ρ`
  of a unit `u` (their strips are disjoint on `G'`, far from `b`).
-/

namespace WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

open scoped Classical

/-- Heavy normals at `b`. -/
def heavyNormals (E : Set (E2 × E2)) (b : E2) (r lam : ℝ) : Set E2 :=
  {e | ‖e‖ = 1 ∧ lam ≤ ((strip E b e r).ncard : ℝ)}

lemma norm_sub_le_eight_of_frost {δ C : ℝ} {G G' : Set E2} (hG : Frost δ C G)
    (hG' : Frost δ C G') {b b' : E2} (hb : b ∈ G) (hb' : b' ∈ G') : ‖b' - b‖ ≤ 8 :=
  norm_le_eight_of_norm_le_four (hG'.2.1 b' hb').1 (hG.2.1 b hb).1

/-- The heavy pairs at `b` lie in the fat strips of a covering set of heavy normals. -/
lemma heavy_fiber_subset {δ C r σ τ : ℝ} {G G' : Set E2} (hG : Frost δ C G) (hG' : Frost δ C G')
    {E : Set (E2 × E2)} (hE : E ⊆ G ×ˢ G') {b : E2} (hb : b ∈ G) (D : Finset E2)
    (hcov : ∀ e ∈ heavyNormals E b r (r ^ (σ + τ) * G'.ncard), ∃ e' ∈ D,
      dist e e' < 16 * r ∨ dist e (-e') < 16 * r) :
    {b' | (b, b') ∈ p2Heavy E r σ τ G'} ⊆ ⋃ e' ∈ D, strip E b e' (129 * r) := by
  intro b' hb'
  obtain ⟨hbE, e, he, hin, hlam⟩ := hb'
  simp only at hin hlam
  have hb'G' : b' ∈ G' := (hE hbE).2
  have h8 := norm_sub_le_eight_of_frost hG hG' hb hb'G'
  obtain ⟨e', he'D, hclose⟩ := hcov e ⟨he, hlam⟩
  simp only [Set.mem_iUnion]
  refine ⟨e', he'D, hbE, ?_⟩
  rcases hclose with h | h
  · have hee : ‖e - e'‖ ≤ 16 * r := by rw [← dist_eq_norm]; exact h.le
    have := inner_lt_of_close (e' := e') h8 hin hee
    linarith
  · have hee : ‖e - -e'‖ ≤ 16 * r := by rw [← dist_eq_norm]; exact h.le
    have := inner_lt_of_close (e' := -e') h8 hin hee
    rw [inner_neg_right, abs_neg] at this
    linarith

/-- Bush size: the heavy pairs at `b` are at most `#D * K * (129 r) ^ σ * #G'`. -/
lemma heavy_fiber_card_le {δ C r σ τ K : ℝ} (hδr : δ ≤ r) (hr : 0 < r)
    {G G' : Set E2} (hG : Frost δ C G) (hG' : Frost δ C G')
    {E : Set (E2 × E2)} (hE : E ⊆ G ×ˢ G')
    (hthin : ∀ b ∈ G, ∀ e : E2, ‖e‖ = 1 → ∀ ρ : ℝ, δ ≤ ρ →
      ({b' | (b, b') ∈ E ∧ |inner ℝ (b' - b) e| < ρ}.ncard : ℝ) ≤ K * ρ ^ σ * G'.ncard)
    {b : E2} (hb : b ∈ G) (D : Finset E2) (hDunit : ∀ e ∈ D, ‖e‖ = 1)
    (hcov : ∀ e ∈ heavyNormals E b r (r ^ (σ + τ) * G'.ncard), ∃ e' ∈ D,
      dist e e' < 16 * r ∨ dist e (-e') < 16 * r) :
    ({b' | (b, b') ∈ p2Heavy E r σ τ G'}.ncard : ℝ) ≤ D.card * (K * (129 * r) ^ σ * G'.ncard) := by
  have hsub := heavy_fiber_subset hG hG' hE hb D hcov
  have hfin : (⋃ e' ∈ D, strip E b e' (129 * r)).Finite := by
    apply Set.Finite.biUnion (Finset.finite_toSet D)
    intro e' _
    exact hG'.1.subset (fun b' hb' => (hE hb'.1).2)
  calc ({b' | (b, b') ∈ p2Heavy E r σ τ G'}.ncard : ℝ)
      ≤ ((⋃ e' ∈ D, strip E b e' (129 * r)).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfin
    _ ≤ ∑ e' ∈ D, ((strip E b e' (129 * r)).ncard : ℝ) := ncard_biUnion_finset_le D _
    _ ≤ ∑ e' ∈ D, K * (129 * r) ^ σ * G'.ncard := by
        apply Finset.sum_le_sum
        intro e' he'
        exact hthin b hb e' (hDunit e' he') (129 * r) (by linarith)
    _ = D.card * (K * (129 * r) ^ σ * G'.ncard) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Katz-Tao: separated heavy normals near a direction are few. -/
lemma heavy_normals_near_card_le {δ C r σ τ K ρ : ℝ} (hδr : δ ≤ r) (hr : 0 < r)
    (hr6 : r ≤ 1 / 6) (hρ : r ≤ ρ)
    {G G' : Set E2} (hG : Frost δ C G) (hG' : Frost δ C G')
    (hsep : ∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b')
    {E : Set (E2 × E2)} (hE : E ⊆ G ×ˢ G')
    (hthin : ∀ b ∈ G, ∀ e : E2, ‖e‖ = 1 → ∀ ρ : ℝ, δ ≤ ρ →
      ({b' | (b, b') ∈ E ∧ |inner ℝ (b' - b) e| < ρ}.ncard : ℝ) ≤ K * ρ ^ σ * G'.ncard)
    {b : E2} (hb : b ∈ G) (D : Finset E2)
    (hDheavy : ∀ e ∈ D, e ∈ heavyNormals E b r (r ^ (σ + τ) * G'.ncard))
    (hDsep : (D : Set E2).Pairwise (NormSep (16 * r)))
    {u : E2} (hu : ‖u‖ = 1) :
    ((D.filter (fun e => dist e u ≤ ρ)).card : ℝ) * (r ^ (σ + τ) * G'.ncard) ≤
      K * (9 * ρ) ^ σ * G'.ncard := by
  set F := D.filter (fun e => dist e u ≤ ρ) with hF
  have hFD : ∀ e ∈ F, e ∈ D := fun e he => (Finset.mem_filter.mp he).1
  have hlow : (F.card : ℝ) * (r ^ (σ + τ) * G'.ncard) ≤ ∑ e ∈ F, ((strip E b e r).ncard : ℝ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro e he
    exact (hDheavy e (hFD e he)).2
  have hdisj : ∀ e ∈ F, ∀ e' ∈ F, e ≠ e' → Disjoint (strip E b e r) (strip E b e' r) := by
    intro e he e' he' hne
    rw [Set.disjoint_left]
    intro b' h1 h2
    have hb'G' : b' ∈ G' := (hE h1.1).2
    have hfar : 1 / 4 ≤ ‖b' - b‖ := by
      rw [← dist_eq_norm, dist_comm]; exact hsep b hb b' hb'G'
    have hunit := (hDheavy e (hFD e he)).1
    have hunit' := (hDheavy e' (hFD e' he')).1
    have hcl := strips_close_of_common_far_point hr hr6 hunit hunit' hfar h1.2 h2.2
    have hs := hDsep (hFD e he) (hFD e' he') hne
    rcases hcl with h | h
    · linarith [hs.1]
    · linarith [hs.2]
  have hcont : ∀ e ∈ F, strip E b e r ⊆ strip E b u (9 * ρ) := by
    intro e he b' hb'
    refine ⟨hb'.1, ?_⟩
    have hb'G' : b' ∈ G' := (hE hb'.1).2
    have h8 := norm_sub_le_eight_of_frost hG hG' hb hb'G'
    have hdist : dist e u ≤ ρ := (Finset.mem_filter.mp he).2
    have hee : ‖e - u‖ ≤ ρ := by rw [← dist_eq_norm]; exact hdist
    have := inner_lt_of_close (e' := u) h8 hb'.2 hee
    linarith
  have hTfin : (strip E b u (9 * ρ)).Finite := hG'.1.subset (fun b' hb' => (hE hb'.1).2)
  have hsum := sum_ncard_le_of_pairwiseDisjoint F (fun e => strip E b e r) hdisj _ hTfin hcont
  have hthin' := hthin b hb u hu (9 * ρ) (by linarith)
  exact hlow.trans (hsum.trans hthin')

end WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs
