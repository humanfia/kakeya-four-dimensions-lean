-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_whitney_rich_reduction.WhitneyCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_whitney_rich_reduction.Whitney

/-!
# Whitney cover of the rich set (x0284)

For any family of sets `S i` (the strips) indexed by `Fin n` with `δ`-separated coefficients
`q i`, `‖q i‖ ≤ 10`, every point of multiplicity `≥ lam > 1` is `μ`-rich on both sides of a
Whitney pair at one of `L` scales, with `μ = (lam - 1) / (4 * 801 ^ 3 * L)`.  Hence the rich set
is covered by finitely many bi-rich sets and its outer volume is at most their sum.
-/

namespace WangZahlLot.Obl.wz_jet_whitney_rich_reduction

open Finset MeasureTheory

noncomputable section

variable {n : ℕ}

/-- Multiplicity of the index set `A` at `p`. -/
def multOn (S : Fin n → Set (ℝ × ℝ)) (A : Finset (Fin n)) (p : ℝ × ℝ) : ENNReal :=
  ∑ i ∈ A, (S i).indicator (fun _ => (1 : ENNReal)) p

open Classical in
lemma multOn_eq_card (S : Fin n → Set (ℝ × ℝ)) (A : Finset (Fin n)) (p : ℝ × ℝ) :
    multOn S A p = ((A.filter (fun i => p ∈ S i)).card : ENNReal) := by
  classical
  unfold multOn
  simp only [Set.indicator_apply]
  rw [Finset.sum_boole]

/-- The Whitney bi-rich set of the pair `kk` at scale `D` and level `μ`. -/
def biRichSet (q : Fin n → EuclideanSpace ℝ (Fin 3)) (S : Fin n → Set (ℝ × ℝ)) (D μ : ℝ)
    (kk : (Fin 3 → ℤ) × (Fin 3 → ℤ)) : Set (ℝ × ℝ) :=
  {p | ENNReal.ofReal μ ≤ multOn S (cubeSet q (D / 200) kk.1) p ∧
    ENNReal.ofReal μ ≤ multOn S (cubeSet q (D / 200) kk.2) p}

lemma dist_le_twenty {q : Fin n → EuclideanSpace ℝ (Fin 3)} (hq : ∀ i, ‖q i‖ ≤ 10) (i j : Fin n) :
    dist (q i) (q j) ≤ 20 := by
  rw [dist_eq_norm]
  calc ‖q i - q j‖ ≤ ‖q i‖ + ‖q j‖ := norm_sub_le _ _
    _ ≤ 20 := by linarith [hq i, hq j]

/-- Pointwise Whitney extraction for an incident fan. -/
theorem rich_point_whitney (q : Fin n → EuclideanSpace ℝ (Fin 3)) (S : Fin n → Set (ℝ × ℝ))
    {δ lam : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsep : ∀ i j, i ≠ j → δ ≤ dist (q i) (q j))
    (hq : ∀ i, ‖q i‖ ≤ 10) {L : ℕ} (hL : 20 < δ * (3 / 2) ^ (L - 1)) (hlam : 1 < lam)
    {p : ℝ × ℝ} (hp : ENNReal.ofReal lam ≤ multOn S univ p) :
    ∃ m < L, ∃ kk ∈ whitneyPairs q (whitneyScale δ m),
      p ∈ biRichSet q S (whitneyScale δ m) ((lam - 1) / (4 * 801 ^ 3 * L)) kk := by
  classical
  set F := univ.filter (fun i => p ∈ S i) with hF
  have hLpos : 0 < L := by
    by_contra h0
    push Not at h0
    have : L = 0 := by omega
    subst this
    norm_num at hL
    linarith
  have hcard : lam ≤ (F.card : ℝ) := by
    rw [multOn_eq_card] at hp
    rw [← ENNReal.ofReal_natCast] at hp
    exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).mp hp
  obtain ⟨m, hm, hshell⟩ := exists_dense_shell q hδ F
    (fun i _ j _ hij => hsep i j hij) hLpos
    (fun i _ j _ => (dist_le_twenty hq i j).trans_lt hL)
  set D := whitneyScale δ m with hD_def
  have hD : 0 < D := whitneyScale_pos hδ m
  set μ := (lam - 1) / (4 * 801 ^ 3 * L) with hμ_def
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hμ0 : 0 ≤ μ := by
    rw [hμ_def]; apply div_nonneg (by linarith); positivity
  have hFpos : (0 : ℝ) < F.card := by linarith
  have hkey : 2 * μ * 801 ^ 3 * F.card < ((F.card : ℝ) ^ 2 - F.card) / L := by
    rw [hμ_def, lt_div_iff₀ hLr]
    have h1 : 2 * ((lam - 1) / (4 * 801 ^ 3 * L)) * 801 ^ 3 * F.card * L =
        (lam - 1) / 2 * F.card := by
      field_simp
      ring
    rw [h1]
    have h2 : (F.card : ℝ) ^ 2 - F.card = (F.card - 1) * F.card := by ring
    rw [h2]
    apply mul_lt_mul_of_pos_right _ hFpos
    linarith
  obtain ⟨kk, hkk, h1, h2⟩ := exists_rich_whitney_pair q hD hμ0 F (hkey.trans_le hshell)
  refine ⟨m, hm, kk, hkk, ?_, ?_⟩
  · rw [multOn_eq_card]
    have : (cubeSet q (D / 200) kk.1).filter (fun i => p ∈ S i) = F ∩ cubeSet q (D / 200) kk.1 := by
      ext i; simp [hF, Finset.mem_filter, Finset.mem_inter, and_comm]
    rw [this, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal h1
  · rw [multOn_eq_card]
    have : (cubeSet q (D / 200) kk.2).filter (fun i => p ∈ S i) = F ∩ cubeSet q (D / 200) kk.2 := by
      ext i; simp [hF, Finset.mem_filter, Finset.mem_inter, and_comm]
    rw [this, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal h2

/-- The rich set is covered by the Whitney bi-rich sets. -/
theorem rich_set_subset_whitney (q : Fin n → EuclideanSpace ℝ (Fin 3)) (S : Fin n → Set (ℝ × ℝ))
    {δ lam : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsep : ∀ i j, i ≠ j → δ ≤ dist (q i) (q j))
    (hq : ∀ i, ‖q i‖ ≤ 10) {L : ℕ} (hL : 20 < δ * (3 / 2) ^ (L - 1)) (hlam : 1 < lam) :
    {p | ENNReal.ofReal lam ≤ multOn S univ p} ⊆
      ⋃ m ∈ range L, ⋃ kk ∈ whitneyPairs q (whitneyScale δ m),
        biRichSet q S (whitneyScale δ m) ((lam - 1) / (4 * 801 ^ 3 * L)) kk := by
  intro p hp
  obtain ⟨m, hm, kk, hkk, hpk⟩ := rich_point_whitney q S hδ hδ1 hsep hq hL hlam hp
  simp only [Set.mem_iUnion]
  exact ⟨m, Finset.mem_range.mpr hm, kk, hkk, hpk⟩

/-- Outer volume of the rich set is at most the sum over scales and Whitney pairs. -/
theorem volume_rich_le_sum_whitney (q : Fin n → EuclideanSpace ℝ (Fin 3))
    (S : Fin n → Set (ℝ × ℝ)) {δ lam : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) (hq : ∀ i, ‖q i‖ ≤ 10) {L : ℕ}
    (hL : 20 < δ * (3 / 2) ^ (L - 1)) (hlam : 1 < lam) (T : Set (ℝ × ℝ))
    (hT : T ⊆ {p | ENNReal.ofReal lam ≤ multOn S univ p}) :
    volume T ≤ ∑ m ∈ range L, ∑ kk ∈ whitneyPairs q (whitneyScale δ m),
      volume (biRichSet q S (whitneyScale δ m) ((lam - 1) / (4 * 801 ^ 3 * L)) kk) := by
  calc volume T ≤ volume (⋃ m ∈ range L, ⋃ kk ∈ whitneyPairs q (whitneyScale δ m),
        biRichSet q S (whitneyScale δ m) ((lam - 1) / (4 * 801 ^ 3 * L)) kk) :=
        measure_mono (hT.trans (rich_set_subset_whitney q S hδ hδ1 hsep hq hL hlam))
    _ ≤ ∑ m ∈ range L, volume (⋃ kk ∈ whitneyPairs q (whitneyScale δ m),
        biRichSet q S (whitneyScale δ m) ((lam - 1) / (4 * 801 ^ 3 * L)) kk) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ range L, ∑ kk ∈ whitneyPairs q (whitneyScale δ m),
        volume (biRichSet q S (whitneyScale δ m) ((lam - 1) / (4 * 801 ^ 3 * L)) kk) := by
        apply Finset.sum_le_sum
        intro m _
        exact measure_biUnion_finset_le _ _

/-- Members of one cube are within `D / 100` of each other. -/
lemma dist_lt_of_mem_cubeSet {q : Fin n → EuclideanSpace ℝ (Fin 3)} {D : ℝ} (hD : 0 < D)
    {k : Fin 3 → ℤ} {i j : Fin n} (hi : i ∈ cubeSet q (D / 200) k)
    (hj : j ∈ cubeSet q (D / 200) k) : dist (q i) (q j) < D / 100 := by
  rw [mem_cubeSet] at hi hj
  have := dist_lt_of_cubeIdx_eq (by positivity : (0 : ℝ) < D / 200) (hi.trans hj.symm)
  linarith

/-- Cross distances of a Whitney pair. -/
lemma cross_dist_of_mem_whitneyPairs {q : Fin n → EuclideanSpace ℝ (Fin 3)} {D : ℝ}
    {kk : (Fin 3 → ℤ) × (Fin 3 → ℤ)} (hkk : kk ∈ whitneyPairs q D) {i j : Fin n}
    (hi : i ∈ cubeSet q (D / 200) kk.1) (hj : j ∈ cubeSet q (D / 200) kk.2) :
    D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2 * D :=
  (mem_whitneyPairs.mp hkk).2 i hi j hj

end

end WangZahlLot.Obl.wz_jet_whitney_rich_reduction
