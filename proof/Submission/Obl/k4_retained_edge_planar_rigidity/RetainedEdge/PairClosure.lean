-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/PairClosure.lean;
-- only the namespace and module paths were renamed to o071's.
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.ScalarClosure
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.IndividualBSG

/-!
# From two individual BSG outputs to the cross sum of the common pair

Paper Lemma 7.3, proof: for a retained parameter `κ₁` whose endpoint sets `A₁, B₁` meet the common
pair `A₀, B₀` in many lattice points, the Ruzsa triangle inequality (through the intersections, and
through the small cross sums of both individual pairs) bounds `N(A₀ + κ₁ B₀)`. Every loss is a power
of the subpower `M`.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open scoped Pointwise

noncomputable section

theorem ruzsa_le (h : ℝ) (U V W : Finset (ℝ × ℝ)) {ℓ B₁ B₂ : ℝ} (hℓ : 0 < ℓ)
    (hV : ℓ ≤ ((cells h V).card : ℝ)) (h1 : ((cells h (U - V)).card : ℝ) ≤ B₁)
    (h2 : ((cells h (V - W)).card : ℝ) ≤ B₂) :
    ((cells h (U - W)).card : ℝ) ≤ 256 * B₁ * B₂ / ℓ := by
  have hr := cells_ruzsa h U V W
  have hB₁ : 0 ≤ B₁ := le_trans (by positivity) h1
  refine le_div_of_mul_le_lower hℓ hV (by positivity) (hr.trans ?_)
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by positivity)
    (by positivity)

theorem card_cells_neg_lower (h : ℝ) (X : Finset (ℝ × ℝ)) :
    ((cells h X).card : ℝ) / 4 ≤ (cells h (-X)).card := by
  have := card_cells_neg_le h (-X)
  rw [neg_neg] at this
  have h' : ((cells h X).card : ℝ) ≤ (cells h (-X)).card * 4 := by exact_mod_cast this
  linarith

theorem card_cells_neg_upper (h : ℝ) (X : Finset (ℝ × ℝ)) :
    ((cells h (-X)).card : ℝ) ≤ 4 * (cells h X).card := by
  have := card_cells_neg_le h X
  have h' : ((cells h (-X)).card : ℝ) ≤ (cells h X).card * 4 := by exact_mod_cast this
  linarith

theorem card_cells_sub_comm_le' (h : ℝ) (U V : Finset (ℝ × ℝ)) :
    ((cells h (V - U)).card : ℝ) ≤ 4 * (cells h (U - V)).card := by
  have := card_cells_sub_comm_le h U V
  have h' : ((cells h (V - U)).card : ℝ) ≤ (cells h (U - V)).card * 4 := by exact_mod_cast this
  linarith

theorem card_cells_mono' {h : ℝ} {U V : Finset (ℝ × ℝ)} (hUV : U ⊆ V) :
    ((cells h U).card : ℝ) ≤ (cells h V).card := by
  exact_mod_cast Finset.card_le_card (cells_mono hUV)

/-- Self-differences of one side of a pair with small cross sum. -/
theorem self_diff_le (h : ℝ) (a b : Finset (ℝ × ℝ)) {M L : ℝ} (hM : 0 < M) (hL : 0 < L)
    (ha : L / M ≤ (cells h a).card) (hb : L / M ≤ (cells h b).card)
    (hab : ((cells h (a + b)).card : ℝ) ≤ M * L) :
    ((cells h (a - a)).card : ℝ) ≤ 4096 * M ^ 3 * L ∧
      ((cells h (b - b)).card : ℝ) ≤ 4096 * M ^ 3 * L := by
  have hnb := card_cells_neg_lower h b
  have hna := card_cells_neg_lower h a
  have hℓ : 0 < L / (4 * M) := by positivity
  constructor
  · have h1 : ((cells h (a - -b)).card : ℝ) ≤ M * L := by rw [sub_neg_eq_add]; exact hab
    have h2 : ((cells h (-b - a)).card : ℝ) ≤ 4 * (M * L) := by
      have e : -b - a = -(a + b) := by rw [neg_add, sub_eq_add_neg, add_comm]
      rw [e]; exact (card_cells_neg_upper h _).trans (by linarith)
    have := ruzsa_le h a (-b) a hℓ (by rw [div_mul_eq_div_div_swap]; linarith) h1 h2
    calc ((cells h (a - a)).card : ℝ) ≤ 256 * (M * L) * (4 * (M * L)) / (L / (4 * M)) := this
      _ = 4096 * M ^ 3 * L := by field_simp; ring
  · have h1 : ((cells h (b - -a)).card : ℝ) ≤ M * L := by rw [sub_neg_eq_add, add_comm]; exact hab
    have h2 : ((cells h (-a - b)).card : ℝ) ≤ 4 * (M * L) := by
      have e : -a - b = -(a + b) := by rw [neg_add, sub_eq_add_neg]
      rw [e]; exact (card_cells_neg_upper h _).trans (by linarith)
    have := ruzsa_le h b (-a) b hℓ (by rw [div_mul_eq_div_div_swap]; linarith) h1 h2
    calc ((cells h (b - b)).card : ℝ) ≤ 256 * (M * L) * (4 * (M * L)) / (L / (4 * M)) := this
      _ = 4096 * M ^ 3 * L := by field_simp; ring


set_option maxHeartbeats 1000000 in
/-- **The cross sum of the common pair at a retained parameter** (paper Lemma 7.3, proof of
`re:fixed-cross`). -/
theorem cross_sum_bound {h K M L : ℝ} (hh : 0 < h) (hL : 0 < L) (hK1 : 1 ≤ K) (hM : 4096 ≤ M)
    (hKM : (2 * K ^ 2 + 2) ^ 2 ≤ M) {A B A₀ B₀ A₁ B₁ : Finset (ℝ × ℝ)}
    (hAlat : OnLattice h A) (hBlat : OnLattice h B) (hA₀ : A₀ ⊆ A) (hB₀ : B₀ ⊆ B)
    (hA₁ : A₁ ⊆ A) (hB₁ : B₁ ⊆ B) {κ₀ κ₁ : ℝ} (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (hκ₀inv : |κ₀⁻¹| ≤ K) (hκ₁le : |κ₁| ≤ K) (hκ₁inv : |κ₁⁻¹| ≤ K)
    (hA₀c : L / M ≤ (A₀.card : ℝ)) (hb₀ : L / M ≤ ((cells h (κ₀ • B₀)).card : ℝ))
    (hab₀ : ((cells h (A₀ + κ₀ • B₀)).card : ℝ) ≤ M * L)
    (hA₁c : L / M ≤ (A₁.card : ℝ)) (hb₁ : L / M ≤ ((cells h (κ₁ • B₁)).card : ℝ))
    (hab₁ : ((cells h (A₁ + κ₁ • B₁)).card : ℝ) ≤ M * L)
    (hAA : L / M ≤ ((A₁ ∩ A₀).card : ℝ)) (hBB : L / M ≤ ((B₁ ∩ B₀).card : ℝ)) :
    ((cells h (A₀ + κ₁ • B₀)).card : ℝ) ≤ M ^ 27 * L := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM1 : 1 ≤ M := le_trans (by norm_num) hM
  have hNA₀ : ((cells h A₀).card : ℝ) = A₀.card := by
    rw [card_cells_lattice hh (hAlat.mono hA₀)]
  have hNA₁ : ((cells h A₁).card : ℝ) = A₁.card := by
    rw [card_cells_lattice hh (hAlat.mono hA₁)]
  -- (a), (b): self-differences of both pairs
  obtain ⟨haa₀, hbb₀⟩ := self_diff_le h A₀ (κ₀ • B₀) hM0 hL (by rw [hNA₀]; exact hA₀c) hb₀ hab₀
  obtain ⟨haa₁, hbb₁⟩ := self_diff_le h A₁ (κ₁ • B₁) hM0 hL (by rw [hNA₁]; exact hA₁c) hb₁ hab₁
  -- (c): `A₁ - A₀` through the intersection
  have hH : L / M ≤ ((cells h (A₁ ∩ A₀)).card : ℝ) := by
    have hsub : A₁ ∩ A₀ ⊆ A := Finset.inter_subset_left.trans hA₁
    rw [card_cells_lattice hh (hAlat.mono hsub)]; exact hAA
  have hc : ((cells h (A₁ - A₀)).card : ℝ) ≤ M ^ 10 * L := by
    have h1 : ((cells h (A₁ - A₁ ∩ A₀)).card : ℝ) ≤ 4096 * M ^ 3 * L :=
      (card_cells_mono' (Finset.sub_subset_sub le_rfl Finset.inter_subset_left)).trans haa₁
    have h2 : ((cells h (A₁ ∩ A₀ - A₀)).card : ℝ) ≤ 4096 * M ^ 3 * L :=
      (card_cells_mono' (Finset.sub_subset_sub Finset.inter_subset_right le_rfl)).trans haa₀
    have := ruzsa_le h A₁ (A₁ ∩ A₀) A₀ (by positivity) hH h1 h2
    calc ((cells h (A₁ - A₀)).card : ℝ) ≤ 256 * (4096 * M ^ 3 * L) * (4096 * M ^ 3 * L) / (L / M) :=
          this
      _ = 2 ^ 32 * M ^ 7 * L := by field_simp; ring
      _ ≤ M ^ 10 * L := by
          have : (2 : ℝ) ^ 32 ≤ M ^ 3 := by
            calc (2 : ℝ) ^ 32 ≤ 4096 ^ 3 := by norm_num
              _ ≤ M ^ 3 := by gcongr
          have : (2 : ℝ) ^ 32 * M ^ 7 ≤ M ^ 10 := by
            calc (2 : ℝ) ^ 32 * M ^ 7 ≤ M ^ 3 * M ^ 7 := by gcongr
              _ = M ^ 10 := by ring
          gcongr
  -- (d): the self-difference of `κ₁ B₀`
  have hratio : |κ₁ / κ₀| ≤ K ^ 2 := by
    rw [div_eq_mul_inv, abs_mul, sq]
    exact mul_le_mul hκ₁le hκ₀inv (abs_nonneg _) (by linarith)
  have hκB₀ : κ₁ • B₀ = (κ₁ / κ₀) • (κ₀ • B₀) := by
    rw [smul_smul_finset, div_mul_cancel₀ _ hκ₀]
  have hd : ((cells h (κ₁ • B₀ - κ₁ • B₀)).card : ℝ) ≤ M * (4096 * M ^ 3 * L) := by
    rw [hκB₀]
    calc ((cells h ((κ₁ / κ₀) • (κ₀ • B₀) - (κ₁ / κ₀) • (κ₀ • B₀))).card : ℝ)
        ≤ (2 * |κ₁ / κ₀| + 2) ^ 2 * (cells h (κ₀ • B₀ - κ₀ • B₀)).card :=
          card_cells_smul_sub_le h _ _ _
      _ ≤ M * (4096 * M ^ 3 * L) := by
          have : (2 * |κ₁ / κ₀| + 2) ^ 2 ≤ M := le_trans (by gcongr) hKM
          gcongr
  -- (e): `κ₁ B₁ - κ₁ B₀` through the intersection
  have hH' : L / M ^ 2 ≤ ((cells h (κ₁ • (B₁ ∩ B₀))).card : ℝ) := by
    have hsub : B₁ ∩ B₀ ⊆ B := Finset.inter_subset_left.trans hB₁
    have h1 := card_lattice_le_smul hh (hBlat.mono hsub) hκ₁
    have h2 : (2 * |κ₁⁻¹| + 2) ^ 2 ≤ M := by
      refine le_trans ?_ hKM
      have : |κ₁⁻¹| ≤ K ^ 2 := le_trans hκ₁inv (le_self_pow₀ hK1 (by norm_num))
      gcongr
    rw [div_le_iff₀ (by positivity)]
    calc L = L / M * M := by field_simp
      _ ≤ ((B₁ ∩ B₀).card : ℝ) * M := by gcongr
      _ ≤ (2 * |κ₁⁻¹| + 2) ^ 2 * (cells h (κ₁ • (B₁ ∩ B₀))).card * M := by gcongr
      _ ≤ M * (cells h (κ₁ • (B₁ ∩ B₀))).card * M := by gcongr
      _ = ((cells h (κ₁ • (B₁ ∩ B₀))).card : ℝ) * M ^ 2 := by ring
  have he : ((cells h (κ₁ • B₁ - κ₁ • B₀)).card : ℝ) ≤ M ^ 12 * L := by
    have h1 : ((cells h (κ₁ • B₁ - κ₁ • (B₁ ∩ B₀))).card : ℝ) ≤ 4096 * M ^ 3 * L :=
      (card_cells_mono' (Finset.sub_subset_sub le_rfl
        (Finset.smul_finset_subset_smul_finset Finset.inter_subset_left))).trans hbb₁
    have h2 : ((cells h (κ₁ • (B₁ ∩ B₀) - κ₁ • B₀)).card : ℝ) ≤ M * (4096 * M ^ 3 * L) :=
      (card_cells_mono' (Finset.sub_subset_sub
        (Finset.smul_finset_subset_smul_finset Finset.inter_subset_right) le_rfl)).trans hd
    have := ruzsa_le h (κ₁ • B₁) (κ₁ • (B₁ ∩ B₀)) (κ₁ • B₀) (by positivity) hH' h1 h2
    calc ((cells h (κ₁ • B₁ - κ₁ • B₀)).card : ℝ)
        ≤ 256 * (4096 * M ^ 3 * L) * (M * (4096 * M ^ 3 * L)) / (L / M ^ 2) := this
      _ = 2 ^ 32 * M ^ 9 * L := by field_simp; ring
      _ ≤ M ^ 12 * L := by
          have : (2 : ℝ) ^ 32 ≤ M ^ 3 := by
            calc (2 : ℝ) ^ 32 ≤ 4096 ^ 3 := by norm_num
              _ ≤ M ^ 3 := by gcongr
          have : (2 : ℝ) ^ 32 * M ^ 9 ≤ M ^ 12 := by
            calc (2 : ℝ) ^ 32 * M ^ 9 ≤ M ^ 3 * M ^ 9 := by gcongr
              _ = M ^ 12 := by ring
          gcongr
  -- (f): `A₀ + κ₁ B₁`
  have hf : ((cells h (A₀ + κ₁ • B₁)).card : ℝ) ≤ M ^ 13 * L := by
    have h1 : ((cells h (A₀ - A₁)).card : ℝ) ≤ 4 * (M ^ 10 * L) :=
      (card_cells_sub_comm_le' h A₁ A₀).trans (by linarith)
    have h2 : ((cells h (A₁ - -(κ₁ • B₁))).card : ℝ) ≤ M * L := by
      rw [sub_neg_eq_add]; exact hab₁
    have := ruzsa_le h A₀ A₁ (-(κ₁ • B₁)) (ℓ := L / M) (by positivity) (by rw [hNA₁]; exact hA₁c)
      h1 h2
    rw [sub_neg_eq_add] at this
    calc ((cells h (A₀ + κ₁ • B₁)).card : ℝ) ≤ 256 * (4 * (M ^ 10 * L)) * (M * L) / (L / M) := this
      _ = 1024 * M ^ 12 * L := by field_simp; ring
      _ ≤ M ^ 13 * L := by
          have : (1024 : ℝ) * M ^ 12 ≤ M ^ 13 := by
            calc (1024 : ℝ) * M ^ 12 ≤ M * M ^ 12 := by gcongr; linarith
              _ = M ^ 13 := by ring
          gcongr
  -- (g): `A₀ + κ₁ B₀`
  have h1 : ((cells h (A₀ - -(κ₁ • B₁))).card : ℝ) ≤ M ^ 13 * L := by
    rw [sub_neg_eq_add]; exact hf
  have h2 : ((cells h (-(κ₁ • B₁) - -(κ₁ • B₀))).card : ℝ) ≤ 4 * (M ^ 12 * L) := by
    rw [neg_sub_neg]
    exact (card_cells_sub_comm_le' h _ _).trans (by linarith)
  have hlow : L / (4 * M) ≤ ((cells h (-(κ₁ • B₁))).card : ℝ) := by
    have := card_cells_neg_lower h (κ₁ • B₁)
    calc L / (4 * M) = (L / M) / 4 := by field_simp
      _ ≤ ((cells h (κ₁ • B₁)).card : ℝ) / 4 := by gcongr
      _ ≤ _ := this
  have := ruzsa_le h A₀ (-(κ₁ • B₁)) (-(κ₁ • B₀)) (by positivity) hlow h1 h2
  rw [sub_neg_eq_add] at this
  calc ((cells h (A₀ + κ₁ • B₀)).card : ℝ) ≤ 256 * (M ^ 13 * L) * (4 * (M ^ 12 * L)) / (L / (4 * M)) :=
        this
    _ = 4096 * M ^ 26 * L := by field_simp; ring
    _ ≤ M ^ 27 * L := by
        have : (4096 : ℝ) * M ^ 26 ≤ M ^ 27 := by
          calc (4096 : ℝ) * M ^ 26 ≤ M * M ^ 26 := by gcongr
            _ = M ^ 27 := by ring
        gcongr


/-- **The scalar-closure hypotheses for the common pair** (paper Lemma 7.3): with `E = A₀`,
`F = -(κ₀ B₀)` and the ratios `κ_j/κ₀` of the retained parameters. -/
theorem closureData_of_pairs {h K M L : ℝ} (hh : 0 < h) (hL : 0 < L) (hK1 : 1 ≤ K)
    (hM : 4096 ≤ M) (hKM : (2 * K ^ 2 + 2) ^ 2 ≤ M) {A B : Finset (ℝ × ℝ)}
    (hAlat : OnLattice h A) (hBlat : OnLattice h B) (hAM : (A.card : ℝ) ≤ M * L)
    {ι : Type*} [DecidableEq ι] (I' : Finset ι) (κ : ι → ℝ) (Ai Bi : ι → Finset (ℝ × ℝ))
    (hAi : ∀ i, Ai i ⊆ A) (hBi : ∀ i, Bi i ⊆ B) (hκ : ∀ i, κ i ≠ 0) (hκle : ∀ i, |κ i| ≤ K)
    (hκinv : ∀ i, |(κ i)⁻¹| ≤ K) (hAc : ∀ i, L / M ≤ ((Ai i).card : ℝ))
    (hbc : ∀ i, L / M ≤ ((cells h (κ i • Bi i)).card : ℝ))
    (habc : ∀ i, ((cells h (Ai i + κ i • Bi i)).card : ℝ) ≤ M * L) (i₀ : ι)
    (hAA : ∀ j ∈ I', L / M ≤ ((Ai j ∩ Ai i₀).card : ℝ))
    (hBB : ∀ j ∈ I', L / M ≤ ((Bi j ∩ Bi i₀).card : ℝ)) :
    ClosureData h M L 27 (Ai i₀) (-(κ i₀ • Bi i₀)) (I'.image (fun j => κ j / κ i₀)) := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM1 : 1 ≤ M := le_trans (by norm_num) hM
  have hM27 : M ≤ M ^ 27 := le_self_pow₀ hM1 (by norm_num)
  have hK2M : K ^ 2 ≤ M := by
    refine le_trans ?_ hKM
    nlinarith [sq_nonneg K]
  have hNA₀ : ((cells h (Ai i₀)).card : ℝ) = (Ai i₀).card := by
    rw [card_cells_lattice hh (hAlat.mono (hAi i₀))]
  have hLM : L / M ^ 27 ≤ L / M := div_le_div_of_nonneg_left hL.le hM0 hM27
  refine ⟨hM1, hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hNA₀]; exact hLM.trans (hAc i₀)
  · calc ((cells h (Ai i₀)).card : ℝ) = (Ai i₀).card := hNA₀
      _ ≤ A.card := by exact_mod_cast Finset.card_le_card (hAi i₀)
      _ ≤ M * L := hAM
      _ ≤ M ^ 27 * L := by gcongr
  · have h1 := card_cells_neg_lower h (κ i₀ • Bi i₀)
    calc L / M ^ 27 ≤ (L / M) / 4 := by
          rw [div_div]
          apply div_le_div_of_nonneg_left hL.le (by positivity)
          calc M * 4 ≤ M * M := by gcongr; linarith
            _ = M ^ 2 := by ring
            _ ≤ M ^ 27 := pow_le_pow_right₀ hM1 (by norm_num)
      _ ≤ ((cells h (κ i₀ • Bi i₀)).card : ℝ) / 4 := by gcongr; exact hbc i₀
      _ ≤ _ := h1
  · rw [sub_neg_eq_add]
    exact (habc i₀).trans (by gcongr)
  · intro t ht
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
    exact div_ne_zero (hκ j) (hκ i₀)
  · intro t ht
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
    rw [div_eq_mul_inv, abs_mul]
    calc |κ j| * |(κ i₀)⁻¹| ≤ K * K := mul_le_mul (hκle j) (hκinv i₀) (abs_nonneg _) (by linarith)
      _ = K ^ 2 := by ring
      _ ≤ M := hK2M
  · intro t ht
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
    rw [inv_div, div_eq_mul_inv, abs_mul]
    calc |κ i₀| * |(κ j)⁻¹| ≤ K * K := mul_le_mul (hκle i₀) (hκinv j) (abs_nonneg _) (by linarith)
      _ = K ^ 2 := by ring
      _ ≤ M := hK2M
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    have e : Ai i₀ - (κ j / κ i₀) • -(κ i₀ • Bi i₀) = Ai i₀ + κ j • Bi i₀ := by
      rw [Finset.smul_finset_neg, smul_smul_finset, div_mul_cancel₀ _ (hκ i₀), sub_neg_eq_add]
    rw [e]
    exact cross_sum_bound hh hL hK1 hM hKM hAlat hBlat (hAi i₀) (hBi i₀) (hAi j) (hBi j)
      (hκ i₀) (hκ j) (hκinv i₀) (hκle j) (hκinv j) (hAc i₀) (hbc i₀) (habc i₀) (hAc j) (hbc j)
      (habc j) (hAA j hj) (hBB j hj)

end

end Submission.Obl.k4_retained_edge_planar_rigidity
