import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.IndividualBSG
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.CommonPair
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.PairClosure
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.RatioLaw

/-!
# Common endpoint sets and the restricted ratio law (paper Lemma 7.3)

From the planar graph data of the frozen statement (written with `L = 1/h`): graph BSG for every
represented index (`individual_bsg`), a reference index `i₀` whose BSG rectangle meets those of a
large part of the parameter law (`common_pair_avg`), the scalar-closure data of the common pair
(`closureData_of_pairs`), and the restricted, renormalized ratio law `t j = κ j / κ i₀` with its
interval cap (`restricted_ratio_frostman`), normalized by `R = K²` as `flat_generated` wants.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open scoped Pointwise

noncomputable section

/-- The rounded restricted sum set of the frozen statement is a cell set. -/
theorem cells_image_add_smul (h κ : ℝ) (G : Finset ((ℝ × ℝ) × (ℝ × ℝ))) :
    cells h (G.image (fun p => p.1 + κ • p.2)) =
      G.image (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) =>
        (⌊(p.1.1 + κ * p.2.1) / h⌋, ⌊(p.1.2 + κ * p.2.2) / h⌋)) := by
  rw [cells, Finset.image_image]
  rfl

/-- If `x * y ≥ T > 0` with `0 ≤ x` and `y ≤ Y`, then `x ≥ T / Y`. -/
theorem le_of_mul_le_of_le {x y Y T : ℝ} (hx : 0 ≤ x) (hT : 0 < T) (hy : y ≤ Y)
    (hxy : T ≤ x * y) : T / Y ≤ x := by
  have hY : 0 < Y := by
    by_contra hY
    push Not at hY
    have : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx (hy.trans hY)
    linarith
  rw [div_le_iff₀ hY]
  calc T ≤ x * y := hxy
    _ ≤ x * Y := mul_le_mul_of_nonneg_left hy hx

/-- **Common sets** (paper Lemma 7.3 with the restricted ratio law). -/
theorem common_sets {c C₀ : ℝ} (hc : 0 < c) (hC₀ : 0 < C₀) (hT5 : GraphBSG c C₀)
    {h K L s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hL : 0 < L) (hK : 2 ^ 20 ≤ K) (hKc : 1 / c ≤ K)
    (hKC : C₀ ≤ K) (hs : 0 < s) (hs1 : s ≤ 1)
    {m : ℕ} {w κ : Fin m → ℝ} {A B : Finset (ℝ × ℝ)} {G : Fin m → Finset ((ℝ × ℝ) × (ℝ × ℝ))}
    (hAlat : OnLattice h A) (hBlat : OnLattice h B)
    (hA1 : L / K ≤ A.card) (hA2 : (A.card : ℝ) ≤ K * L)
    (hB1 : L / K ≤ B.card) (hB2 : (B.card : ℝ) ≤ K * L)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hκ : ∀ i, 1 / K ≤ |κ i| ∧ |κ i| ≤ K)
    (hcap : ∀ x r : ℝ, h ≤ r → r ≤ 1 →
      (∑ i, if κ i ∈ Set.Icc x (x + r) then w i else 0) ≤ K * r ^ s)
    (hG : ∀ i, G i ⊆ A ×ˢ B) (hGc : ∀ i, L ^ 2 / K ≤ (G i).card)
    (hsum : ∀ i, ((cells h ((G i).image (fun p => p.1 + κ i • p.2))).card : ℝ) ≤ K * L) :
    ∃ i₀ : Fin m, ∃ A₀ B₀ : Finset (ℝ × ℝ), ∃ I' : Finset (Fin m), ∃ ν t : Fin m → ℝ,
      A₀ ⊆ A ∧ B₀ ⊆ B ∧
      L ^ 2 / K ^ 40 ≤ (((G i₀).filter (fun p => p.1 ∈ A₀ ∧ p.2 ∈ B₀)).card : ℝ) ∧
      ClosureData h (K ^ 200) L 27 A₀ (-(κ i₀ • B₀)) (I'.image (fun j => κ j / κ i₀)) ∧
      (∀ j, 0 ≤ ν j) ∧ ∑ j, ν j = 1 ∧
      (∀ j, t j ∈ I'.image (fun j => κ j / κ i₀)) ∧ (∀ j, |t j| ≤ K ^ 2) ∧
      ∀ x u : ℝ, h ≤ u → u ≤ 1 →
        (∑ j, if t j / K ^ 2 ∈ Set.Icc (x - u) (x + u) then ν j else 0) ≤ K ^ 172 * u ^ s := by
  classical
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have hκne : ∀ i, κ i ≠ 0 := fun i h0 => by
    have h1 := (hκ i).1
    rw [h0, abs_zero] at h1
    have : (0 : ℝ) < 1 / K := by positivity
    linarith
  have hκinv : ∀ i, |(κ i)⁻¹| ≤ K := fun i => by
    rw [abs_inv, inv_le_comm₀ (abs_pos.mpr (hκne i)) hK0, ← one_div]
    exact (hκ i).1
  -- Step 1: graph BSG for every represented index
  have hbsg : ∀ i, ∃ A₁ B₁ : Finset (ℝ × ℝ), A₁ ⊆ A ∧ B₁ ⊆ B ∧ L / K ^ 40 ≤ (A₁.card : ℝ) ∧
      L / K ^ 40 ≤ ((cells h (κ i • B₁)).card : ℝ) ∧
      ((cells h (A₁ + κ i • B₁)).card : ℝ) ≤ K ^ 40 * L ∧
      L ^ 2 / K ^ 40 ≤ (((G i).filter (fun p => p.1 ∈ A₁ ∧ p.2 ∈ B₁)).card : ℝ) := fun i =>
    individual_bsg hc hC₀ hT5 hh hL hK hKc hKC hAlat hBlat hA1 hA2 hB1 hB2 (hκne i) (hκinv i)
      (hG i) (hGc i) (hsum i)
  choose Ai Bi hAi hBi hAic hBic hABc hGic using hbsg
  -- Step 2: a common pair by averaging over the parameter law
  set ℓ : ℝ := (L / K ^ 40) ^ 2 with hℓ
  have hLK : 0 < L / K ^ 40 := by positivity
  have hℓpos : 0 < ℓ := by positivity
  have hBcard : ∀ i, L / K ^ 40 ≤ ((Bi i).card : ℝ) := fun i =>
    (hBic i).trans (by exact_mod_cast card_cells_le_card' h (Bi i) (κ i))
  have hRl : ∀ i, ℓ ≤ ((Ai i ×ˢ Bi i).card : ℝ) := fun i => by
    rw [Finset.card_product, Nat.cast_mul, hℓ, sq]
    exact mul_le_mul (hAic i) (hBcard i) hLK.le (by positivity)
  have hRU : ∀ i, Ai i ×ˢ Bi i ⊆ A ×ˢ B := fun i => Finset.product_subset_product (hAi i) (hBi i)
  obtain ⟨i₀, hi₀⟩ := common_pair_avg w hw0 hw1 (A ×ˢ B) (fun i => Ai i ×ˢ Bi i) hRU hℓpos hRl
  set U := A ×ˢ B with hU
  have hUc : (U.card : ℝ) ≤ K ^ 2 * L ^ 2 := by
    rw [hU, Finset.card_product, Nat.cast_mul]
    calc (A.card : ℝ) * B.card ≤ (K * L) * (K * L) :=
          mul_le_mul hA2 hB2 (by positivity) (by positivity)
      _ = K ^ 2 * L ^ 2 := by ring
  have hUpos : (0 : ℝ) < U.card := lt_of_lt_of_le hℓpos
    ((hRl i₀).trans (by exact_mod_cast Finset.card_le_card (hRU i₀)))
  set T : ℝ := ℓ ^ 2 / (2 * (U.card : ℝ)) with hT
  have hTpos : 0 < T := by positivity
  set I' : Finset (Fin m) := Finset.univ.filter
    (fun j => T ≤ (((Ai i₀ ×ˢ Bi i₀) ∩ (Ai j ×ˢ Bi j)).card : ℝ)) with hI'
  set W : ℝ := ∑ j ∈ I', w j with hW
  have hℓ' : ℓ = L ^ 2 / K ^ 80 := by rw [hℓ, div_pow, ← pow_mul]
  have hWlow : 1 / (2 * K ^ 164) ≤ W := by
    have e : (∑ j, (if T ≤ (((Ai i₀ ×ˢ Bi i₀) ∩ (Ai j ×ˢ Bi j)).card : ℝ) then w j else 0)) = W := by
      rw [hW, hI', Finset.sum_filter]
    have hi₀' : ℓ ^ 2 / (2 * (U.card : ℝ) ^ 2) ≤ W := by rw [← e]; exact hi₀
    refine le_trans ?_ hi₀'
    have hU2 : (U.card : ℝ) ^ 2 ≤ (K ^ 2 * L ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hUc 2
    calc 1 / (2 * K ^ 164) = ℓ ^ 2 / (2 * (K ^ 2 * L ^ 2) ^ 2) := by
          rw [hℓ']; field_simp
      _ ≤ ℓ ^ 2 / (2 * (U.card : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hWpos : 0 < W := lt_of_lt_of_le (by positivity) hWlow
  -- intersections for retained indices
  have hTlow : L ^ 2 / (2 * K ^ 162) ≤ T := by
    calc L ^ 2 / (2 * K ^ 162) = ℓ ^ 2 / (2 * (K ^ 2 * L ^ 2)) := by
          rw [hℓ']; field_simp
      _ ≤ T := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hinter : ∀ j ∈ I', L / K ^ 200 ≤ ((Ai j ∩ Ai i₀).card : ℝ) ∧
      L / K ^ 200 ≤ ((Bi j ∩ Bi i₀).card : ℝ) := by
    intro j hj
    have hj' : T ≤ (((Ai i₀ ×ˢ Bi i₀) ∩ (Ai j ×ˢ Bi j)).card : ℝ) := (Finset.mem_filter.mp hj).2
    rw [Finset.product_inter_product, Finset.card_product, Nat.cast_mul] at hj'
    have hT' : L ^ 2 / (2 * K ^ 162) ≤ ((Ai i₀ ∩ Ai j).card : ℝ) * ((Bi i₀ ∩ Bi j).card : ℝ) :=
      hTlow.trans hj'
    have hAle : ((Ai i₀ ∩ Ai j).card : ℝ) ≤ K * L :=
      le_trans (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_left.trans (hAi i₀)))
        hA2
    have hBle : ((Bi i₀ ∩ Bi j).card : ℝ) ≤ K * L :=
      le_trans (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_left.trans (hBi i₀)))
        hB2
    have hpos : 0 < L ^ 2 / (2 * K ^ 162) := by positivity
    have hA' := le_of_mul_le_of_le (Nat.cast_nonneg _) hpos hBle hT'
    have hB' := le_of_mul_le_of_le (Nat.cast_nonneg _) hpos hAle (hT'.trans_eq (mul_comm _ _))
    have hkey : L / K ^ 200 ≤ L ^ 2 / (2 * K ^ 162) / (K * L) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h38 : (2 : ℝ) ≤ K ^ 37 := le_trans (by norm_num) (le_trans hK
        (le_self_pow₀ hK1 (by norm_num)))
      calc L * (2 * K ^ 162 * (K * L)) = L ^ 2 * (2 * K ^ 163) := by ring
        _ ≤ L ^ 2 * (K ^ 37 * K ^ 163) := by gcongr
        _ = L ^ 2 * K ^ 200 := by ring
    rw [Finset.inter_comm] at hA' hB'
    exact ⟨hkey.trans hA', hkey.trans hB'⟩
  -- Step 3: scalar-closure data of the common pair
  have hK200 : (4096 : ℝ) ≤ K ^ 200 :=
    le_trans (by norm_num) (le_trans hK (le_self_pow₀ hK1 (by norm_num)))
  have hK40 : K ^ 40 ≤ K ^ 200 := pow_le_pow_right₀ hK1 (by norm_num)
  have hKM : (2 * K ^ 2 + 2) ^ 2 ≤ K ^ 200 := by
    have h4 : (2 * K ^ 2 + 2) ^ 2 ≤ (4 * K ^ 2) ^ 2 := by
      have : 2 * K ^ 2 + 2 ≤ 4 * K ^ 2 := by nlinarith
      exact pow_le_pow_left₀ (by positivity) this 2
    have h16 : (16 : ℝ) ≤ K ^ 196 :=
      le_trans (by norm_num) (le_trans hK (le_self_pow₀ hK1 (by norm_num)))
    calc (2 * K ^ 2 + 2) ^ 2 ≤ (4 * K ^ 2) ^ 2 := h4
      _ = 16 * K ^ 4 := by ring
      _ ≤ K ^ 196 * K ^ 4 := by gcongr
      _ = K ^ 200 := by ring
  have hAM : (A.card : ℝ) ≤ K ^ 200 * L :=
    hA2.trans (mul_le_mul_of_nonneg_right (le_self_pow₀ hK1 (by norm_num)) hL.le)
  have hLdiv : L / K ^ 200 ≤ L / K ^ 40 := div_le_div_of_nonneg_left hL.le (by positivity) hK40
  have hD := closureData_of_pairs hh hL hK1 hK200 hKM hAlat hBlat hAM I' κ Ai Bi hAi hBi hκne
    (fun i => (hκ i).2) hκinv (fun i => hLdiv.trans (hAic i)) (fun i => hLdiv.trans (hBic i))
    (fun i => (hABc i).trans (mul_le_mul_of_nonneg_right hK40 hL.le)) i₀
    (fun j hj => (hinter j hj).1) (fun j hj => (hinter j hj).2)
  -- Step 4: the restricted ratio law
  have hi₀I : i₀ ∈ I' := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.inter_self]
    have hRi : ((Ai i₀ ×ˢ Bi i₀).card : ℝ) ≤ U.card := by
      exact_mod_cast Finset.card_le_card (hRU i₀)
    have h1 : ℓ ≤ ((Ai i₀ ×ˢ Bi i₀).card : ℝ) := hRl i₀
    rw [hT, div_le_iff₀ (by positivity)]
    calc ℓ ^ 2 = ℓ * ℓ := sq ℓ
      _ ≤ ((Ai i₀ ×ˢ Bi i₀).card : ℝ) * U.card := mul_le_mul h1 (h1.trans hRi) hℓpos.le
          (Nat.cast_nonneg _)
      _ ≤ ((Ai i₀ ×ˢ Bi i₀).card : ℝ) * (2 * U.card) := by
          gcongr
          linarith
  set ν : Fin m → ℝ := fun j => if j ∈ I' then w j / W else 0 with hν
  set t : Fin m → ℝ := fun j => if j ∈ I' then κ j / κ i₀ else 1 with ht
  refine ⟨i₀, Ai i₀, Bi i₀, I', ν, t, hAi i₀, hBi i₀, hGic i₀, hD, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [hν]
    split_ifs
    · exact div_nonneg (hw0 j) hWpos.le
    · exact le_rfl
  · simp only [hν]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, ← hW, div_self hWpos.ne']
  · intro j
    simp only [ht]
    split_ifs with hj
    · exact Finset.mem_image_of_mem _ hj
    · exact Finset.mem_image.mpr ⟨i₀, hi₀I, div_self (hκne i₀)⟩
  · intro j
    simp only [ht]
    split_ifs
    · rw [abs_div, div_le_iff₀ (abs_pos.mpr (hκne i₀)), sq]
      calc |κ j| ≤ K := (hκ j).2
        _ = K * K * (1 / K) := by field_simp
        _ ≤ K * K * |κ i₀| := by gcongr; exact (hκ i₀).1
    · rw [abs_one]; nlinarith
  · intro x u hu hu1
    have hint : ∀ y ℓ' : ℝ, h ≤ ℓ' → ℓ' ≤ 1 → wmass w κ (Set.Icc y (y + ℓ')) ≤ K * ℓ' ^ s :=
      fun y ℓ' h1 h2 => hcap y ℓ' h1 h2
    have hR := restricted_ratio_frostman hw0 hh hh1 hs hs1 hK0.le hint I' hWpos (hκne i₀)
      (by positivity : (0 : ℝ) < K ^ 2) x u hu hu1
    have heq : (∑ j, if t j / K ^ 2 ∈ Set.Icc (x - u) (x + u) then ν j else 0) =
        ∑ j, if κ j / κ i₀ / K ^ 2 ∈ Set.Icc (x - u) (x + u) then
          (if j ∈ I' then w j / W else 0) else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ht, hν]
      by_cases hj : j ∈ I' <;> simp [hj]
    rw [heq]
    refine hR.trans ?_
    have hus : 0 ≤ u ^ s := Real.rpow_nonneg (le_trans hh.le hu) s
    have h1 : K / W ≤ 2 * K ^ 165 := by
      rw [div_le_iff₀ hWpos]
      calc K = 2 * K ^ 165 * (1 / (2 * K ^ 164)) := by field_simp
        _ ≤ 2 * K ^ 165 * W := by gcongr
    have h2 : (2 * |κ i₀| * K ^ 2 + 2) ^ 2 ≤ 16 * K ^ 6 := by
      have hk : |κ i₀| ≤ K := (hκ i₀).2
      have : 2 * |κ i₀| * K ^ 2 + 2 ≤ 4 * K ^ 3 := by
        have h1 : 2 * |κ i₀| * K ^ 2 ≤ 2 * K * K ^ 2 := by gcongr
        have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK1
        have h2 : 2 * K * K ^ 2 = 2 * K ^ 3 := by ring
        linarith
      calc (2 * |κ i₀| * K ^ 2 + 2) ^ 2 ≤ (4 * K ^ 3) ^ 2 :=
            pow_le_pow_left₀ (by positivity) this 2
        _ = 16 * K ^ 6 := by ring
    have h32 : (32 : ℝ) ≤ K := le_trans (by norm_num) hK
    calc K / W * (2 * |κ i₀| * K ^ 2 + 2) ^ 2 * u ^ s ≤ 2 * K ^ 165 * (16 * K ^ 6) * u ^ s :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by positivity)) hus
      _ = 32 * K ^ 171 * u ^ s := by ring
      _ ≤ K * K ^ 171 * u ^ s :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h32 (by positivity)) hus
      _ = K ^ 172 * u ^ s := by ring

end

end Submission.Obl.k4_retained_edge_planar_rigidity
