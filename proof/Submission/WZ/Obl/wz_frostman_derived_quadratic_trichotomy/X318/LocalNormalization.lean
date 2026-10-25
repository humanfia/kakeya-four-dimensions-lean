-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalPruning
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.ParentContributors

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file LocalNormalization.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective exists_enumerate)
open WangZahlLot.Obl.wz_concentrated_convex_factorization (enumerate_ncard)

attribute [local instance] Classical.propDecidable

/-- Normalize locally saturated containers inside distinct coarse tubes.  The
retained fibres keep saturation in their original parents even though the new
prisms can gain incidences from other parents. -/
theorem normalize_local_saturated_cover {n p q : ℕ} {δ τ a b κ H D : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) (hbτ : b ≤ τ)
    (hκ : 0 < κ) (hH : 0 < H) (hD : 1 ≤ D)
    (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (z w : Fin q → Space) (hw : ∀ l, ‖w l‖ = 1)
    (hsep : Distinct (fun l => Tube τ (z l) (w l)))
    (W : Fin p → Set Space) (label : Fin p → Fin q)
    (c e₁ e₂ e₃ : Fin p → Space) (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j])
    (hshape : ∀ j, W j ⊆ Tube τ (z (label j)) (w (label j)) ∩
      {y | |inner ℝ (e₁ j) (y - c j)| ≤ a ∧ |inner ℝ (e₂ j) (y - c j)| ≤ b})
    (hcover : ∀ i, ∃ j, Tube δ (x i) (v i) ⊆ W j)
    (hdegree : ∀ i, (ncard {j | Tube δ (x i) (v i) ⊆ W j} : ℝ) ≤ D)
    (hparent : ∀ l U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | Tube δ (x i) (v i) ⊆ Tube τ (z l) (w l) ∧
        Tube δ (x i) (v i) ⊆ U} : ℝ) * δ ^ 2) ≤ ENNReal.ofReal κ * volume U)
    (hsat : ∀ j, κ * (8 * a * b) ≤
      H * (contained (fun i => Tube δ (x i) (v i)) (W j) : ℝ) * δ ^ 2) :
    ∃ (k : ℕ) (g : Fin k → Fin n) (r : ℕ) (s : Fin r → Fin p) (c' : Fin r → Space),
      Function.Injective g ∧ Function.Injective s ∧ (n : ℝ) ≤ 2 * k ∧
      (∀ j, ‖c' j - center (z (label (s j))) (w (label (s j)))‖ ≤ 6 * τ) ∧
      (∀ j, UnorientedNear (8 * τ) (e₃ (s j)) (w (label (s j)))) ∧
      (let A := fun i => Tube δ (x (g i)) (v (g i))
       let P := fun j => Prism a b (c' j) (e₁ (s j)) (e₂ (s j)) (e₃ (s j))
       (∀ i, ∃ j, A i ⊆ P j) ∧
       (∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤
         8 * ((576000000 * 7 ^ 4) * H) * D ^ 2) ∧
       (∀ j, κ * (8 * a * b) ≤ (2 * H) *
         (ncard {i | A i ⊆ Tube τ (z (label (s j))) (w (label (s j))) ∧ A i ⊆ P j} : ℝ) *
           δ ^ 2)) := by
  classical
  let A := fun i => Tube δ (x i) (v i)
  let E : ℝ := 576000000 * 7 ^ 4
  have hE : 0 < E := by norm_num [E]
  have hb : 0 < b := ha.trans_le hab
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hcoarse (i) : ∃ l, A i ⊆ Tube τ (z l) (w l) := by
    obtain ⟨j, hij⟩ := hcover i
    exact ⟨label j, fun y hy => (hshape j (hij hy)).1⟩
  have hwitness (j) : ∃ i, A i ⊆ W j := by
    have hpos : 0 < (contained A (W j) : ℝ) := by
      by_contra hn
      have hn' : (contained A (W j) : ℝ) = 0 :=
        le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
      have hh := hsat j
      change κ * (8 * a * b) ≤ H * (contained A (W j) : ℝ) * δ ^ 2 at hh
      rw [hn'] at hh
      nlinarith [mul_pos hκ (by positivity : 0 < 8 * a * b)]
    have hn : 0 < contained A (W j) := by exact_mod_cast hpos
    exact (Set.ncard_pos (Set.toFinite _)).mp hn
  have hgeo (j) : ∃ c' : Space,
      W j ⊆ Prism a b c' (e₁ j) (e₂ j) (e₃ j) ∧
      ‖c' - center (z (label j)) (w (label j))‖ ≤ 6 * τ ∧
      UnorientedNear (8 * τ) (e₃ j) (w (label j)) := by
    obtain ⟨i, hi⟩ := hwitness j
    have hsub := hi.trans (hshape j)
    obtain ⟨c', hkeep, hc', he'⟩ := recentered_local_prism hδ hτ hτhalf hab hbτ
      (hv i) (hw (label j)) (he j)
      (fun y hy => (hsub hy).1) (fun y hy => (hsub hy).2)
    exact ⟨c', (hshape j).trans hkeep, hc', he'⟩
  choose c' hkeep hcenter haxis using hgeo
  let Q := fun j => Prism a b (c' j) (e₁ j) (e₂ j) (e₃ j)
  have hvol (j) : volume (Q j) = ENNReal.ofReal (8 * a * b) :=
    prism_volume ha.le hb.le _ _ _ _ (he j)
  have hupper (j U) (hU : Convex ℝ U) :
      ENNReal.ofReal ((ncard {i | A i ⊆ Q j ∧ A i ⊆ U} : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal (E * κ) * volume U := by
    convert parentwise_katzTao_in_prism hδ hτ hτhalf
      ha.le hab (by simpa using hbτ : b ≤ 1 * τ) zero_le_one hκ.le
      x v hv z w hw hsep hcoarse hparent (c' j) (e₁ j) (e₂ j) (e₃ j) (he j) U hU using 1 <;>
      norm_num [E, A, Q]
  have hload (j) : (contained A (Q j) : ℝ) ≤ (E * H) * contained A (W j) := by
    have hh := hupper j (Q j) (prism_convex _ _ _ _ _ _)
    simp only [and_self] at hh
    rw [hvol j, ← ENNReal.ofReal_mul (by positivity : 0 ≤ E * κ)] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (E * κ) * (8 * a * b))).mp hh
    have hs := mul_le_mul_of_nonneg_left (hsat j) hE.le
    apply (mul_le_mul_iff_right₀ hδsq).mp
    change (contained A (Q j) : ℝ) * δ ^ 2 ≤ _ at hh'
    nlinarith only [hh', hs]
  obtain ⟨J, R, hmass, hcoverR, hdegreeR, hfibre⟩ :=
    prune_preserving_old_incidence A W Q hD (mul_pos hE hH) hcover hdegree hload
  have hsatR (j) (hj : j ∈ J) : κ * (8 * a * b) ≤ (2 * H) *
      ((R.filter fun i => A i ⊆ Tube τ (z (label j)) (w (label j)) ∧ A i ⊆ Q j).card : ℝ) *
        δ ^ 2 := by
    have hsub : R.filter (fun i => A i ⊆ W j) ⊆
        R.filter (fun i => A i ⊆ Tube τ (z (label j)) (w (label j)) ∧ A i ⊆ Q j) := by
      intro i hi
      obtain ⟨hiR, hiW⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hiR, (fun y hy => (hshape j (hiW hy)).1),
        hiW.trans (hkeep j)⟩
    have hcount := (hfibre j hj).trans (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (Finset.card_le_card hsub)) (by norm_num : (0 : ℝ) ≤ 2))
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount hH.le) hδsq.le
    have hs := hsat j
    change κ * (8 * a * b) ≤ H * (contained A (W j) : ℝ) * δ ^ 2 at hs
    nlinarith only [hh, hs]
  refine ⟨R.card, enumerate R, J.card, enumerate J, c' ∘ enumerate J,
    enumerate_injective R, enumerate_injective J, hmass,
    (fun j => hcenter (enumerate J j)), (fun j => haxis (enumerate J j)), ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, hj, hij⟩ := hcoverR (enumerate R i) (enumerate_mem R i)
    obtain ⟨j', rfl⟩ := exists_enumerate J hj
    exact ⟨j', hij.trans (hkeep _)⟩
  · intro i
    change (ncard {j | A (enumerate R i) ⊆ Q (enumerate J j)} : ℝ) ≤ _
    rw [enumerate_ncard J (fun j => A (enumerate R i) ⊆ Q j)]
    exact hdegreeR (enumerate R i) (enumerate_mem R i)
  · intro j
    change κ * (8 * a * b) ≤ (2 * H) *
      (ncard {i | A (enumerate R i) ⊆ Tube τ (z (label (enumerate J j))) (w (label (enumerate J j))) ∧
        A (enumerate R i) ⊆ Q (enumerate J j)} : ℝ) * δ ^ 2
    rw [enumerate_ncard R (fun i => A i ⊆ Tube τ (z (label (enumerate J j))) (w (label (enumerate J j))) ∧
      A i ⊆ Q (enumerate J j))]
    convert hsatR (enumerate J j) (enumerate_mem J j) using 1
    congr 4
    ext i
    simp

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
