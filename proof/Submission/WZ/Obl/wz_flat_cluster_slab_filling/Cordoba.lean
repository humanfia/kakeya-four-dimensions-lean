-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_cluster_slab_filling.Cordoba.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Geometry
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Volume

/-!
Córdoba's `L²` argument in the box of one tube, for the proof of
`WangZahlLot.wz_flat_cluster_slab_filling`.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_flat_cluster_slab_filling

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

/-- Summing a nonnegative function of the index distance: every distance occurs at most
twice. -/
lemma sum_dist_le {M : ℕ} (ψ : ℕ → ℝ) (hψ : ∀ k, 0 ≤ ψ k) (m : Fin M)
    (F : Finset (Fin M)) :
    ∑ m' ∈ F, ψ (Nat.dist m m') ≤ 2 * ∑ k ∈ Finset.range M, ψ k := by
  have key : ∀ G : Finset (Fin M), Set.InjOn (fun m' : Fin M => Nat.dist m m') G →
      ∑ m' ∈ G, ψ (Nat.dist m m') ≤ ∑ k ∈ Finset.range M, ψ k := by
    intro G hG
    rw [← Finset.sum_image hG]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨m', -, rfl⟩ := hk
      rw [Finset.mem_range]
      have h1 := m.isLt
      have h2 := m'.isLt
      unfold Nat.dist
      omega
    · intro k _ _
      exact hψ k
  rw [← Finset.sum_filter_add_sum_filter_not F (fun m' : Fin M => (m' : ℕ) < m), two_mul]
  apply add_le_add
  · apply key
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    obtain ⟨-, ha⟩ := ha
    obtain ⟨-, hb⟩ := hb
    simp only at hab
    unfold Nat.dist at hab
    apply Fin.ext
    omega
  · apply key
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    obtain ⟨-, ha⟩ := ha
    obtain ⟨-, hb⟩ := hb
    simp only at hab
    unfold Nat.dist at hab
    apply Fin.ext
    omega

lemma harmonic_sum_le (M : ℕ) :
    ∑ k ∈ Finset.range M, (1 / ((k : ℝ) + 1)) ≤ 1 + Real.log M := by
  have h := harmonic_le_one_add_log M
  have heq : ((harmonic M : ℚ) : ℝ) = ∑ k ∈ Finset.range M, (1 / ((k : ℝ) + 1)) := by
    simp [harmonic, one_div]
  linarith

/-- Two points in the cells `i` and `j` are at axial distance at least `(|i-j| - 1) D`. -/
lemma cell_dist_bound {i j : ℕ} {D a b : ℝ}
    (ha1 : (i : ℝ) * D ≤ a) (ha2 : a ≤ ((i : ℝ) + 1) * D)
    (hb1 : (j : ℝ) * D ≤ b) (hb2 : b ≤ ((j : ℝ) + 1) * D) :
    ((Nat.dist i j : ℝ) - 1) * D ≤ |b - a| := by
  rcases le_total i j with h | h
  · have hd : Nat.dist i j = j - i := by unfold Nat.dist; omega
    rw [hd, Nat.cast_sub h]
    apply le_trans _ (le_abs_self _)
    linarith
  · have hd : Nat.dist i j = i - j := by unfold Nat.dist; omega
    rw [hd, Nat.cast_sub h, abs_sub_comm]
    apply le_trans _ (le_abs_self _)
    linarith

/-- Córdoba's `L²` argument: pieces of crossing tubes through points of the tube `[x,x+v]`
lying in distinct axial cells of length `D = 32 δ / θ`, all crossing at angle `≳ θ`, have
almost disjoint union. -/
theorem cordoba_box {δ θ L D u : ℝ} {M : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hL : 2 * δ ≤ L) (hD : D = 32 * δ / θ) (hu : 0 ≤ u)
    {x v : Space} (hv : ‖v‖ = 1) {g : Space ≃ₗᵢ[ℝ] Space} (hg : ∀ p, g p 2 = inner ℝ v p)
    (F : Finset (Fin M)) (p : Fin M → Space) (y w : Fin M → Space) (A : Fin M → Set Space)
    (hw : ∀ m, ‖w m‖ = 1)
    (hp : ∀ m ∈ F, p m ∈ Tube δ x v)
    (hcell : ∀ m ∈ F, p m ∈ cell δ D x v m)
    (hpw : ∀ m ∈ F, p m ∈ Tube δ (y m) (w m))
    (hcross : ∀ m ∈ F, θ / 2 ≤ |g (w m) 1|)
    (hAm : ∀ m ∈ F, MeasurableSet (A m))
    (hA : ∀ m ∈ F, A m ⊆ Tube δ (y m) (w m) ∩ ball (p m) L)
    (hmass : ∀ m ∈ F, ENNReal.ofReal u ≤ volume (A m))
    (E : Set Space) (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤)
    (hAE : ∀ m ∈ F, A m ⊆ E) :
    u ^ 2 * F.card ≤ 20000 * L * δ ^ 2 * (1 + Real.log M) * (volume E).toReal := by
  have hδL : δ ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hD0 : 0 < D := by rw [hD]; positivity
  have hθD : θ * D = 32 * δ := by rw [hD]; field_simp
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_natCast_nonneg M
  set ψ : ℕ → ℝ := fun k =>
    if k ≤ 1 then 1664 * L * δ ^ 2 else 4096 * L * δ ^ 2 / ((k : ℝ) - 1) with hψdef
  have hψ0 : ∀ k, 0 ≤ ψ k := by
    intro k
    simp only [hψdef]
    split_ifs with hk
    · positivity
    · have : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
      exact div_nonneg (by positivity) (by linarith)
  have hAfin : ∀ m ∈ F, volume (A m) ≠ ⊤ := fun m hm =>
    ne_top_of_le_ne_top hEfin (measure_mono (hAE m hm))
  -- the overlap of two pieces, in terms of the distance of their cells
  have hpair : ∀ i ∈ F, ∀ j ∈ F, (volume (A i ∩ A j)).toReal ≤ ψ (Nat.dist i j) := by
    intro i hi j hj
    by_cases hk : Nat.dist i j ≤ 1
    · simp only [hψdef, ite_eq_left hk]
      apply ENNReal.toReal_le_of_le_ofReal (by positivity)
      calc volume (A i ∩ A j) ≤ volume (A i) := measure_mono inter_subset_left
        _ ≤ volume (Tube δ (y i) (w i) ∩ ball (p i) L) := measure_mono (hA i hi)
        _ ≤ ENNReal.ofReal (1664 * L * δ ^ 2) :=
          tube_ball_volume_upper hδ (hw i) hδL (hpw i hi)
    · simp only [hψdef, ite_eq_right hk]
      replace hk := not_le.mp hk
      have hk2 : (2 : ℝ) ≤ (Nat.dist i j : ℝ) := by exact_mod_cast hk
      rcases (A i ∩ A j).eq_empty_or_nonempty with he | ⟨q, hqi, hqj⟩
      · rw [he, measure_empty, ENNReal.toReal_zero]
        exact div_nonneg (by positivity) (by linarith)
      · have hqi' := hA i hi hqi
        have hqj' := hA j hj hqj
        have hmeet := meeting_angle hδ hv (hw i) (hw j) hg hθ hθ1 hL (hp i hi) (hp j hj)
          (hpw i hi) (hpw j hj) hqi'.1 hqj'.1 (mem_ball_iff_norm.mp hqi'.2)
          (mem_ball_iff_norm.mp hqj'.2) (hcross j hj)
        have hci := hcell i hi
        have hcj := hcell j hj
        simp only [cell] at hci hcj
        have hinner : inner ℝ v (p j - p i) =
            (inner ℝ v (p j - x) + δ) - (inner ℝ v (p i - x) + δ) := by
          rw [add_sub_add_right_eq_sub, ← inner_sub_right, sub_sub_sub_cancel_right]
        have hax : ((Nat.dist i j : ℝ) - 1) * D ≤ |inner ℝ v (p j - p i)| := by
          rw [hinner]
          exact cell_dist_bound hci.1 hci.2 hcj.1 hcj.2
        have hang : 2 * ((Nat.dist i j : ℝ) - 1) * δ ≤ L * angle (w i) (w j) := by
          have h1 : θ * (((Nat.dist i j : ℝ) - 1) * D) ≤ θ * |inner ℝ v (p j - p i)| :=
            mul_le_mul_of_nonneg_left hax hθ.le
          have h2 : θ * (((Nat.dist i j : ℝ) - 1) * D) =
              ((Nat.dist i j : ℝ) - 1) * (32 * δ) := by
            rw [← hθD]; ring
          have h3 : 2 * δ ≤ (Nat.dist i j : ℝ) * δ := mul_le_mul_of_nonneg_right hk2 hδ.le
          linarith
        have hvol := WangZahlLot.Obl.wz_off_stem_brush_overlap.regularized_intersection
          (x := y i) (y := y j) hδ hδ1 (hw i) (hw j)
        apply ENNReal.toReal_le_of_le_ofReal (div_nonneg (by positivity) (by linarith))
        calc volume (A i ∩ A j) ≤ volume (Tube δ (y i) (w i) ∩ Tube δ (y j) (w j)) :=
              measure_mono (inter_subset_inter (fun q hq => (hA i hi hq).1)
                (fun q hq => (hA j hj hq).1))
          _ ≤ ENNReal.ofReal (8192 * δ ^ 3 / max δ (angle (w i) (w j))) := hvol
          _ ≤ ENNReal.ofReal (4096 * L * δ ^ 2 / ((Nat.dist i j : ℝ) - 1)) := by
              apply ENNReal.ofReal_le_ofReal
              rw [div_le_div_iff₀ (lt_max_of_lt_left hδ) (by linarith)]
              have hm : L * angle (w i) (w j) ≤ L * max δ (angle (w i) (w j)) :=
                mul_le_mul_of_nonneg_left (le_max_right _ _) hLpos.le
              have h5 := mul_le_mul_of_nonneg_left (hang.trans hm)
                (by positivity : (0 : ℝ) ≤ 4096 * δ ^ 2)
              linarith
  -- the sum of the profile
  have hsumψ : ∑ k ∈ Finset.range M, ψ k ≤
      3328 * L * δ ^ 2 + 4096 * L * δ ^ 2 * (1 + Real.log M) := by
    have h0 : ψ 0 = 1664 * L * δ ^ 2 := by simp [hψdef]
    have h1 : ψ (0 + 1) = 1664 * L * δ ^ 2 := by simp [hψdef]
    have h2 : ∀ k : ℕ, ψ (k + 1 + 1) = 4096 * L * δ ^ 2 * (1 / ((k : ℝ) + 1)) := by
      intro k
      simp only [hψdef]
      rw [ite_eq_right (by omega)]
      push_cast
      ring
    calc ∑ k ∈ Finset.range M, ψ k ≤ ∑ k ∈ Finset.range (M + 1 + 1), ψ k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun k _ _ => hψ0 k)
      _ = 4096 * L * δ ^ 2 * ∑ k ∈ Finset.range M, (1 / ((k : ℝ) + 1)) +
            3328 * L * δ ^ 2 := by
          rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum, h0, h1,
            Finset.sum_congr rfl (fun k _ => h2 k)]
          ring
      _ ≤ 4096 * L * δ ^ 2 * (1 + Real.log M) + 3328 * L * δ ^ 2 := by
          gcongr
          exact harmonic_sum_le M
      _ = _ := by ring
  have hrow : ∀ i ∈ F, ∑ j ∈ F, (volume (A i ∩ A j)).toReal ≤
      20000 * L * δ ^ 2 * (1 + Real.log M) := by
    intro i hi
    have hLd : 0 ≤ L * δ ^ 2 := by positivity
    have hl1 := mul_le_mul_of_nonneg_left (show 1 ≤ 1 + Real.log M by linarith) hLd
    calc ∑ j ∈ F, (volume (A i ∩ A j)).toReal ≤ ∑ j ∈ F, ψ (Nat.dist i j) :=
          Finset.sum_le_sum (fun j hj => hpair i hi j hj)
      _ ≤ 2 * ∑ k ∈ Finset.range M, ψ k := sum_dist_le ψ hψ0 i F
      _ ≤ 20000 * L * δ ^ 2 * (1 + Real.log M) := by nlinarith
  have hApos : 0 < 20000 * L * δ ^ 2 * (1 + Real.log M) :=
    mul_pos (by positivity) (by linarith)
  have hlu : ∀ i ∈ F, u ≤ (volume (A i)).toReal := fun i hi =>
    (ENNReal.ofReal_le_iff_le_toReal (hAfin i hi)).mp (hmass i hi)
  exact WangZahlLot.wz_finite_shading_second_moment M F A E u _ hE hEfin hAm hAE hu hApos hlu hrow

end WangZahlLot.Obl.wz_flat_cluster_slab_filling

end
