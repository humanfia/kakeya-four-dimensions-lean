-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CordobaSlab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.ConvexSlab
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorDyadic
import Submission.WZ.Obl.wz_finite_shading_second_moment

/-!
# WZ Lemma 5.7: a Córdoba-type `L²` bound for unions of `δ × 1 × 1` slabs

Let `S_j = box δ 1 1 (z j) (e j)` (`j ∈ F`) be slabs (not necessarily essentially distinct) obeying
the Katz–Tao convex count with constant `m` (`#{j : S_j ⊆ W} δ ≤ m vol W`), with measurable
`λ`-dense shadings `Y_j ⊆ S_j`. Then
`λ² δ #F ≤ 3456 (⌊log₂(1/δ)⌋₊ + 2) m vol(⋃ Y_j)`.
For fixed `i`, the slabs `S_j` with `vol(S_i ∩ S_j) ∈ (2^{-k-1}, 2^{-k}] δ` lie (by Lemma 4.9) in the
`48 δ 2^k`-neighbourhood of the plane of `S_i` intersected with `ball (z i) 3`, so there are at most
`3456 m 2^k` of them; summing over `k` bounds the overlap row by `3456 (K+2) m δ`, and the
second-moment lemma o031 concludes.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open ConvexSlab
open scoped Classical

noncomputable section

/-- An orthonormal basis whose first vector is a given unit vector. -/
theorem exists_frame_first {ν : Space} (hν : ‖ν‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ Space, b 0 = ν := by
  let v : Fin 3 → Space := ![ν, 0, 0]
  let s : Set (Fin 3) := {0}
  have hon : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [s, Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp [Set.domRestrict, v, hν]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb 0 (by simp [s])⟩

/-- A slab of half-width `h` meets a ball of radius `R` in volume at most `8 h R²`. -/
theorem slab_inter_ball_volume {ν : Space} (hν : ‖ν‖ = 1) (t h : ℝ) (c : Space) {R : ℝ}
    (hh : 0 ≤ h) (hR : 0 ≤ R) :
    volume (slab ν t h ∩ ball c R) ≤ ENNReal.ofReal (2 * h * (2 * R) * (2 * R)) := by
  obtain ⟨b, hb⟩ := exists_frame_first hν
  set z : Space := c + (t - inner ℝ ν c) • ν with hz
  have hsub : slab ν t h ∩ ball c R ⊆ box (2 * h) (2 * R) (2 * R) z b.repr := by
    rintro p ⟨hp1, hp2⟩
    have hpc : ‖p - c‖ < R := by rwa [mem_ball, dist_eq_norm] at hp2
    have hcoord : ∀ i : Fin 3, i ≠ 0 → |b.repr (p - z) i| < R := by
      intro i hi
      rw [OrthonormalBasis.repr_apply_apply, hz]
      have horth : inner ℝ (b i) ν = 0 := by rw [← hb]; exact b.orthonormal.2 hi
      have : inner ℝ (b i) (p - (c + (t - inner ℝ ν c) • ν)) = inner ℝ (b i) (p - c) := by
        rw [show p - (c + (t - inner ℝ ν c) • ν) = (p - c) - (t - inner ℝ ν c) • ν by abel,
          inner_sub_right, inner_smul_right, horth, mul_zero, sub_zero]
      rw [this]
      calc |inner ℝ (b i) (p - c)| ≤ ‖b i‖ * ‖p - c‖ := abs_real_inner_le_norm _ _
        _ = ‖p - c‖ := by rw [b.orthonormal.1 i, one_mul]
        _ < R := hpc
    refine ⟨?_, ?_, ?_⟩
    · rw [OrthonormalBasis.repr_apply_apply, hb, hz]
      have : inner ℝ ν (p - (c + (t - inner ℝ ν c) • ν)) = inner ℝ ν p - t := by
        rw [inner_sub_right, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hν]
        ring
      rw [this]
      have := hp1; simp only [slab, mem_ofPred_eq] at this
      linarith
    · have := hcoord 1 (by decide); linarith
    · have := hcoord 2 (by decide); linarith
  calc volume (slab ν t h ∩ ball c R) ≤ volume (box (2 * h) (2 * R) (2 * R) z b.repr) :=
        measure_mono hsub
    _ = ENNReal.ofReal (2 * h * (2 * R) * (2 * R)) :=
        box_volume (by positivity) (by positivity) (by positivity) _ _

/-- The unit normal of the slab `box δ 1 1 z e`. -/
def nrm (e : Space ≃ₗᵢ[ℝ] Space) : Space := e.symm (EuclideanSpace.single 0 1)

theorem nrm_norm (e : Space ≃ₗᵢ[ℝ] Space) : ‖nrm e‖ = 1 := by
  simp [nrm, EuclideanSpace.norm_single]

theorem coord_zero (e : Space ≃ₗᵢ[ℝ] Space) (v : Space) : e v 0 = inner ℝ (nrm e) v := by
  have h1 : inner ℝ (EuclideanSpace.single 0 1 : Space) (e v) = e v 0 := by
    rw [EuclideanSpace.inner_single_left]; simp
  calc e v 0 = inner ℝ (EuclideanSpace.single 0 1 : Space) (e v) := h1.symm
    _ = inner ℝ (e (e.symm (EuclideanSpace.single 0 1))) (e v) := by rw [e.apply_symm_apply]
    _ = inner ℝ (nrm e) v := e.inner_map_map _ _

theorem box_subset_slab {δ : ℝ} (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    box δ 1 1 z e ⊆ slab (nrm e) (inner ℝ (nrm e) z) (δ / 2) := by
  rintro p ⟨h0, -, -⟩
  simp only [slab, mem_ofPred_eq]
  rw [coord_zero, inner_sub_right] at h0
  exact h0

theorem box_subset_ball {δ : ℝ} (hδ1 : δ ≤ 1) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    box δ 1 1 z e ⊆ ball z 1 := by
  rintro p ⟨h0, h1, h2⟩
  rw [mem_ball, dist_eq_norm, ← e.norm_map, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have hδ0 : |e (p - z) 0| ≤ 1 / 2 := h0.trans (by linarith)
  have hsq : ∀ x : ℝ, |x| ≤ 1 / 2 → ‖x‖ ^ 2 ≤ 1 / 4 := by
    intro x hx
    rw [Real.norm_eq_abs, sq_abs]
    nlinarith [abs_nonneg x, sq_abs x]
  have := hsq _ hδ0
  have := hsq _ (h1.trans (by norm_num))
  have := hsq _ (h2.trans (by norm_num))
  rw [Real.sqrt_lt' (by norm_num)]
  linarith

theorem ball_volume_le (c : Space) {R : ℝ} (hR : 0 ≤ R) :
    volume (ball c R) ≤ ENNReal.ofReal (2 * R * (2 * R) * (2 * R)) := by
  have h := slab_inter_ball_volume (nrm_norm (LinearIsometryEquiv.refl ℝ Space))
    (inner ℝ (nrm (LinearIsometryEquiv.refl ℝ Space)) c) R c hR hR
  refine le_trans (measure_mono ?_) h
  intro p hp
  refine ⟨?_, hp⟩
  simp only [slab, mem_ofPred_eq]
  rw [← inner_sub_right]
  calc |inner ℝ (nrm (LinearIsometryEquiv.refl ℝ Space)) (p - c)|
      ≤ ‖nrm (LinearIsometryEquiv.refl ℝ Space)‖ * ‖p - c‖ := abs_real_inner_le_norm _ _
    _ = ‖p - c‖ := by rw [nrm_norm, one_mul]
    _ ≤ R := by rw [mem_ball, dist_eq_norm] at hp; linarith

/-- The Katz–Tao count of the slabs, in real form. -/
theorem kt_count_real {n : ℕ} {F : Finset (Fin n)} {δ m : ℝ} (hm : 0 ≤ m)
    {Sl : Fin n → Set Space}
    (hKT : ∀ W, Convex ℝ W →
      ENNReal.ofReal ((F.filter fun j => Sl j ⊆ W).card * δ) ≤ ENNReal.ofReal m * volume W)
    {W : Set Space} (hW : Convex ℝ W) {V : ℝ} (hV : 0 ≤ V) (hWV : volume W ≤ ENNReal.ofReal V) :
    ((F.filter fun j => Sl j ⊆ W).card : ℝ) * δ ≤ m * V := by
  have h : ENNReal.ofReal ((F.filter fun j => Sl j ⊆ W).card * δ) ≤
      ENNReal.ofReal m * ENNReal.ofReal V := (hKT W hW).trans (by gcongr)
  rw [← ENNReal.ofReal_mul hm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hm hV)).mp h

/-- The overlap row of a slab. -/
theorem overlap_row {n : ℕ} (F : Finset (Fin n)) {δ m : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 0 < m) (z : Fin n → Space) (e : Fin n → Space ≃ₗᵢ[ℝ] Space)
    (hKT : ∀ W, Convex ℝ W → ENNReal.ofReal
      ((F.filter fun j => box δ 1 1 (z j) (e j) ⊆ W).card * δ) ≤ ENNReal.ofReal m * volume W)
    (i : Fin n) :
    ∑ j ∈ F, (volume (box δ 1 1 (z i) (e i) ∩ box δ 1 1 (z j) (e j))).toReal ≤
      3456 * ((dyExp 1 δ : ℝ) + 2) * m * δ := by
  classical
  set Sl : Fin n → Set Space := fun j => box δ 1 1 (z j) (e j) with hSl
  have hvolSl : ∀ j, volume (Sl j) = ENNReal.ofReal δ := fun j => by
    rw [hSl]; simp only
    rw [box_volume hδ.le zero_le_one zero_le_one]; ring_nf
  set term : Fin n → ℝ := fun j => (volume (Sl i ∩ Sl j)).toReal with hterm
  have hterm_le : ∀ j, term j ≤ δ := fun j => by
    have : volume (Sl i ∩ Sl j) ≤ ENNReal.ofReal δ := (measure_mono inter_subset_right).trans
      (hvolSl j).le
    exact ENNReal.toReal_le_of_le_ofReal hδ.le this
  have hterm_nn : ∀ j, 0 ≤ term j := fun j => ENNReal.toReal_nonneg
  set K := dyExp 1 δ with hK
  set ν := nrm (e i) with hν
  set c := inner ℝ ν (z i) with hc
  let W : ℕ → Set Space := fun k => slab ν c (48 * δ * 2 ^ k) ∩ ball (z i) 3
  have hWconv : ∀ k, Convex ℝ (W k) := fun k => (slab_convex _ _ _).inter (convex_ball _ _)
  have hWvol : ∀ k, volume (W k) ≤ ENNReal.ofReal (3456 * δ * 2 ^ k) := fun k => by
    refine (slab_inter_ball_volume (nrm_norm _) _ _ _ (by positivity) (by norm_num)).trans ?_
    apply ENNReal.ofReal_le_ofReal; ring_nf; rfl
  have hballvol : volume (ball (z i) 3) ≤ ENNReal.ofReal 216 :=
    (ball_volume_le _ (by norm_num)).trans (ENNReal.ofReal_le_ofReal (by norm_num))
  -- meeting slabs lie in `ball (z i) 3`
  have hmeet : ∀ j, (Sl i ∩ Sl j).Nonempty → Sl j ⊆ ball (z i) 3 := by
    rintro j ⟨p, hpi, hpj⟩ q hq
    have h1 := box_subset_ball hδ1 _ _ hpi
    have h2 := box_subset_ball hδ1 _ _ hpj
    have h3 := box_subset_ball hδ1 _ _ hq
    rw [mem_ball] at h1 h2 h3 ⊢
    calc dist q (z i) ≤ dist q (z j) + dist (z j) p + dist p (z i) := dist_triangle4 _ _ _ _
      _ < 1 + 1 + 1 := by rw [dist_comm (z j) p]; linarith
      _ = 3 := by norm_num
  -- slabs with a large overlap lie in the thin neighbourhood of the plane of `S_i`
  have hSi_slab : Sl i ⊆ slab ν c (δ / 2) := box_subset_slab (z i) (e i)
  have hfin_ij : ∀ j, volume (Sl i ∩ Sl j) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (by rw [hvolSl j]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  have hthin : ∀ j, δ * δ ≤ term j → Sl j ⊆ W (dyExp 1 (term j / δ)) := by
    intro j hj q hq
    set t := term j / δ with ht
    have htpos : 0 < t := by rw [ht]; exact div_pos (lt_of_lt_of_le (by positivity) hj) hδ
    have hnonempty : (Sl i ∩ Sl j).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have : term j = 0 := by
        rw [hterm]; simp only; rw [hne, measure_empty, ENNReal.toReal_zero]
      nlinarith
    refine ⟨?_, hmeet j hnonempty hq⟩
    have hconc : ENNReal.ofReal t * volume (Sl j) ≤ volume (Sl j ∩ slab ν c (δ / 2)) := by
      rw [hvolSl j, ← ENNReal.ofReal_mul htpos.le]
      have heq : t * δ = term j := by rw [ht]; field_simp
      rw [heq, hterm]
      simp only
      rw [ENNReal.ofReal_toReal (hfin_ij j)]
      exact measure_mono (fun x hx => ⟨hx.2, hSi_slab hx.1⟩)
    have hsub := subset_slab (box_convex δ 1 1 (z j) (e j))
      (by rw [hvolSl j]; exact ENNReal.ofReal_pos.mpr hδ)
      (by rw [hvolSl j]; exact ENNReal.ofReal_ne_top) (by positivity : (0 : ℝ) < δ / 2) htpos
      hconc hq
    simp only [slab, mem_ofPred_eq] at hsub ⊢
    refine hsub.trans ?_
    have hlt := dyUp_lt (M := 1) htpos one_pos
    have h2k : (0 : ℝ) < 2 ^ dyExp 1 t := by positivity
    unfold dyUp at hlt
    rw [div_lt_iff₀ h2k] at hlt
    rw [div_le_iff₀ htpos]
    nlinarith
  -- the per-term bound
  have hpointwise : ∀ j, term j ≤ (if Sl j ⊆ ball (z i) 3 then δ * δ else 0) +
      ∑ k ∈ Finset.range (K + 1), (if Sl j ⊆ W k then δ / 2 ^ k else 0) := by
    intro j
    by_cases hsmall : term j < δ * δ
    · have hsum_nn : 0 ≤ ∑ k ∈ Finset.range (K + 1), (if Sl j ⊆ W k then δ / 2 ^ k else 0) :=
        Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
      by_cases hz : term j = 0
      · rw [hz]; split_ifs <;> linarith [mul_pos hδ hδ]
      · have hpos : 0 < term j := lt_of_le_of_ne (hterm_nn j) (Ne.symm hz)
        have hnonempty : (Sl i ∩ Sl j).Nonempty := by
          by_contra hne
          rw [Set.not_nonempty_iff_eq_empty] at hne
          have : term j = 0 := by
            rw [hterm]; simp only; rw [hne, measure_empty, ENNReal.toReal_zero]
          exact hz this
        rw [if_pos (hmeet j hnonempty)]
        linarith
    · push Not at hsmall
      set k := dyExp 1 (term j / δ) with hk
      have htpos : 0 < term j / δ := div_pos (lt_of_lt_of_le (by positivity) hsmall) hδ
      have hkK : k ≤ K := by
        rw [hk, hK]
        exact dyExp_le one_pos hδ (by rw [le_div_iff₀ hδ]; nlinarith)
      have hfirst_nn : 0 ≤ (if Sl j ⊆ ball (z i) 3 then δ * δ else 0) := by
        split_ifs <;> positivity
      have hk_mem : k ∈ Finset.range (K + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hkK)
      have hterm_k : term j ≤ δ / 2 ^ k := by
        have := le_dyUp (M := 1) htpos (by rw [div_le_one hδ]; exact hterm_le j)
        unfold dyUp at this
        rw [← hk] at this
        rw [div_le_iff₀ hδ] at this
        calc term j ≤ 1 / 2 ^ k * δ := this
          _ = δ / 2 ^ k := by ring
      have hsingle : (if Sl j ⊆ W k then δ / 2 ^ k else 0) ≤
          ∑ k' ∈ Finset.range (K + 1), (if Sl j ⊆ W k' then δ / 2 ^ k' else 0) :=
        Finset.single_le_sum (f := fun k' => if Sl j ⊆ W k' then δ / 2 ^ k' else 0)
          (fun k' _ => by split_ifs <;> positivity) hk_mem
      rw [if_pos (hthin j hsmall)] at hsingle
      linarith
  -- summing the per-term bound
  have hcount_ball : ((F.filter fun j => Sl j ⊆ ball (z i) 3).card : ℝ) * δ ≤ m * 216 :=
    kt_count_real hm.le hKT (convex_ball _ _) (by norm_num) hballvol
  have hcount_W : ∀ k, ((F.filter fun j => Sl j ⊆ W k).card : ℝ) * δ ≤ m * (3456 * δ * 2 ^ k) :=
    fun k => kt_count_real hm.le hKT (hWconv k) (by positivity) (hWvol k)
  have h_ball : ((F.filter fun j => Sl j ⊆ ball (z i) 3).card : ℝ) * (δ * δ) ≤ 216 * m * δ := by
    nlinarith [hcount_ball]
  have h_k : ∀ k ∈ Finset.range (K + 1),
      ((F.filter fun j => Sl j ⊆ W k).card : ℝ) * (δ / 2 ^ k) ≤ 3456 * m * δ := by
    intro k _
    have h1 := hcount_W k
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    rw [mul_div_assoc', div_le_iff₀ h2k]
    nlinarith
  calc ∑ j ∈ F, term j
      ≤ ∑ j ∈ F, ((if Sl j ⊆ ball (z i) 3 then δ * δ else 0) +
          ∑ k ∈ Finset.range (K + 1), (if Sl j ⊆ W k then δ / 2 ^ k else 0)) :=
        Finset.sum_le_sum fun j _ => hpointwise j
    _ = ((F.filter fun j => Sl j ⊆ ball (z i) 3).card : ℝ) * (δ * δ) +
          ∑ k ∈ Finset.range (K + 1), ((F.filter fun j => Sl j ⊆ W k).card : ℝ) * (δ / 2 ^ k) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        · apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 216 * m * δ + ∑ _k ∈ Finset.range (K + 1), 3456 * m * δ :=
        add_le_add h_ball (Finset.sum_le_sum h_k)
    _ ≤ 3456 * ((K : ℝ) + 2) * m * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        nlinarith [mul_pos hm hδ]

/-- **WZ Lemma 5.7.** -/
theorem cordoba_slabs {n : ℕ} (F : Finset (Fin n)) {δ m l : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 0 < m) (hl : 0 ≤ l) (z : Fin n → Space) (e : Fin n → Space ≃ₗᵢ[ℝ] Space)
    (Y : Fin n → Set Space)
    (hY : ∀ j ∈ F, MeasurableSet (Y j) ∧ Y j ⊆ box δ 1 1 (z j) (e j) ∧
      ENNReal.ofReal (l * δ) ≤ volume (Y j))
    (hKT : ∀ W, Convex ℝ W → ENNReal.ofReal
      ((F.filter fun j => box δ 1 1 (z j) (e j) ⊆ W).card * δ) ≤ ENNReal.ofReal m * volume W) :
    l ^ 2 * δ * F.card ≤ 3456 * ((dyExp 1 δ : ℝ) + 2) * m * (volume (⋃ j ∈ F, Y j)).toReal := by
  classical
  have hEmeas : MeasurableSet (⋃ j ∈ F, Y j) :=
    Finset.measurableSet_biUnion F fun j hj => (hY j hj).1
  have hEfin : volume (⋃ j ∈ F, Y j) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_biUnion_finset_le F Y)
    refine ENNReal.sum_ne_top.mpr fun j hj => ne_top_of_le_ne_top ?_ (measure_mono (hY j hj).2.1)
    rw [box_volume hδ.le zero_le_one zero_le_one]; exact ENNReal.ofReal_ne_top
  have hA : 0 < 3456 * ((dyExp 1 δ : ℝ) + 2) * m * δ := by positivity
  have hrow : ∀ j ∈ F, ∑ j' ∈ F, (volume (Y j ∩ Y j')).toReal ≤
      3456 * ((dyExp 1 δ : ℝ) + 2) * m * δ := by
    intro j hj
    refine le_trans (Finset.sum_le_sum fun j' hj' => ?_) (overlap_row F hδ hδ1 hm z e hKT j)
    apply ENNReal.toReal_mono
    · refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_right)
      rw [box_volume hδ.le zero_le_one zero_le_one]; exact ENNReal.ofReal_ne_top
    · exact measure_mono (inter_subset_inter (hY j hj).2.1 (hY j' hj').2.1)
  have hlow : ∀ j ∈ F, l * δ ≤ (volume (Y j)).toReal := by
    intro j hj
    have hfin : volume (Y j) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (hY j hj).2.1)
      rw [box_volume hδ.le zero_le_one zero_le_one]; exact ENNReal.ofReal_ne_top
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp (hY j hj).2.2
  have := WangZahlLot.wz_finite_shading_second_moment n F Y (⋃ j ∈ F, Y j) (l * δ)
    (3456 * ((dyExp 1 δ : ℝ) + 2) * m * δ) hEmeas hEfin (fun j hj => (hY j hj).1)
    (fun j hj => Set.subset_biUnion_of_mem (u := Y) hj) (by positivity) hA hlow hrow
  have h2 : (l * δ) ^ 2 * F.card = (l ^ 2 * δ * F.card) * δ := by ring
  have h3 : 3456 * ((dyExp 1 δ : ℝ) + 2) * m * δ * (volume (⋃ j ∈ F, Y j)).toReal =
      (3456 * ((dyExp 1 δ : ℝ) + 2) * m * (volume (⋃ j ∈ F, Y j)).toReal) * δ := by ring
  rw [h2, h3] at this
  exact le_of_mul_le_mul_right this hδ

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
