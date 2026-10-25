-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.TubeEnlargement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TubeStretch

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox volume_orthogonalBox)

def eighthEquiv : Space ≃ᵃ[ℝ] Space :=
  (diagonalEquiv (fun _ => (1 / 8 : ℝ)) (by intro i; norm_num)).toAffineEquiv

lemma eighthEquiv_apply (p : Space) : eighthEquiv p = (1 / 8 : ℝ) • p := by
  ext i
  rfl

lemma eighthEquiv_volume (A : Set Space) :
    volume (eighthEquiv '' A) = ENNReal.ofReal (1 / 512 : ℝ) * volume A := by
  rw [WangZahlLot.Obl.wz_regular_transverse_affine_cells.affineEquiv_volume]
  change ENNReal.ofReal |LinearMap.det (diagonalMap (fun _ => (1 / 8 : ℝ)))| * volume A = _
  rw [diagonalMap_det]
  norm_num [Fin.prod_univ_three]

lemma body_slab_eighth {n : ℕ} {V : Fin n → Set Space} {l : ℝ}
    (hV : BodySlabCount V l) : BodySlabCount (fun i => eighthEquiv '' V i) (8 * l) := by
  intro ν s r hν hr
  have hcard : ({i | eighthEquiv '' V i ⊆ {p | |inner ℝ ν p - s| ≤ r}}.ncard : ℝ) ≤
      {i | V i ⊆ {p | |inner ℝ ν p - 8 * s| ≤ 8 * r}}.ncard := by
    exact_mod_cast Set.ncard_le_ncard (by
      intro i hi p hp
      have hh := hi (mem_image_of_mem eighthEquiv hp)
      change |inner ℝ ν (eighthEquiv p) - s| ≤ r at hh
      rw [eighthEquiv_apply, inner_smul_right] at hh
      change |inner ℝ ν p - 8 * s| ≤ 8 * r
      have he : inner ℝ ν p - 8 * s = 8 * ((1 / 8 : ℝ) * inner ℝ ν p - s) := by ring
      rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
      linarith)
  apply (ENNReal.ofReal_le_ofReal hcard).trans
  convert hV ν (8 * s) (8 * r) hν (by positivity) using 1
  congr 1
  ring

lemma eighth_box_mem (u : OrthonormalBasis (Fin 3) ℝ Space) (c : Space) {r : ℝ}
    {p : Space} (hp : p ∈ orthogonalBox ![2, 2 * r, 2 * r] c u) :
    eighthEquiv p ∈ orthogonalBox ![1 / 4, r / 4, r / 4] (eighthEquiv c) u := by
  intro j
  rw [eighthEquiv_apply, eighthEquiv_apply, ← smul_sub, inner_smul_right,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
  have hh := hp j
  fin_cases j <;> norm_num at hh ⊢ <;> linarith

/-- The original tube slab condition has a convenient scale-free body form. -/
lemma tube_body_slab {d l : ℝ} {n : ℕ} (x v : Fin n → Space) (hl : 0 ≤ l)
    (hball : ∀ i, Tube d (x i) (v i) ⊆ ball 0 1)
    (hF : SlabCount d l n x v) :
    BodySlabCount (fun i => Tube d (x i) (v i)) (8 * l) := by
  intro ν s r hν hr
  have he : {i | Tube d (x i) (v i) ⊆ {p | |inner ℝ ν p - s| ≤ r}} =
      {i | Tube d (x i) (v i) ⊆ ball 0 1 ∩ {p | |inner ℝ ν p - s| ≤ r}} := by
    ext i
    exact ⟨fun hi p hp => ⟨hball i hp, hi hp⟩, fun hi => hi.trans inter_subset_right⟩
  rw [he]
  have hh := (hF ν s r hν hr).trans (mul_le_mul' le_rfl
    (WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.slab_volume_le hν s r hr.le))
  convert hh using 1
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ l * n)]
  congr 1
  ring

/-- Geometric data for applying the enlarged-body estimate to neighbourhoods
of the fine shadings. -/
lemma tube_enlargement_data {n : ℕ} {d r D lam : ℝ} (hd : 0 < d) (hdr : d ≤ r)
    (hr1 : r ≤ 1) (hD : D ≤ r / 4) (hlam : 0 ≤ lam)
    (x : Fin n → Space) (u : Fin n → OrthonormalBasis (Fin 3) ℝ Space)
    (Y : Fin n → Set Space)
    (hball : ∀ i, Tube d (x i) (u i 0) ⊆ ball 0 1)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ Tube d (x i) (u i 0))
    (hden : ∀ i, ENNReal.ofReal (64 * lam * d ^ 2) ≤ volume (Y i)) :
    ∃ (U Z : Fin n → Set Space) (c : Fin n → Space),
      BodyGeometry U c D (r / 8) (r ^ 2 / 8) ∧
      (∀ i, eighthEquiv '' Tube d (x i) (u i 0) ⊆ U i) ∧
      (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ U i) ∧
      (∀ i, ENNReal.ofReal lam * volume (U i) ≤ volume (Z i)) ∧
      (⋃ i, Z i) ⊆ eighthEquiv '' thickening (3 * r) (⋃ i, Y i) := by
  have hr : 0 < r := hd.trans_le hdr
  let c := fun i => x i + (1 / 2 : ℝ) • u i 0
  let U := fun i => orthogonalBox ![1 / 4, r / 4, r / 4] (eighthEquiv (c i)) (u i)
  let f := fun i => tubeStretch (u i) (c i) (r / d) (div_pos (hd.trans_le hdr) hd)
  let Z := fun i => eighthEquiv '' (f i '' Y i)
  have hc (i : Fin n) : ‖eighthEquiv (c i)‖ ≤ 3 / 8 := by
    rw [eighthEquiv_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
    have hh := tube_midpoint_norm hd (x i) (u i) (hball i)
    change ‖c i‖ ≤ 3 / 2 at hh
    linarith
  have hG : BodyGeometry U (fun i => eighthEquiv (c i)) D (r / 8) (r ^ 2 / 8) :=
    tube_box_geometry (hd.trans_le hdr) hr1 hD _ u hc
  refine ⟨U, Z, _, hG, ?_, ?_, ?_, ?_, ?_⟩
  · intro i p hp
    obtain ⟨q, hq, rfl⟩ := hp
    apply eighth_box_mem
    have hh := tube_subset_midpoint_box (u i) (x i) (hdr.trans hr1) hq
    intro j
    have hj := hh j
    fin_cases j <;> norm_num at hj ⊢ <;> linarith
  · intro i
    exact eighthEquiv.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      ((f i).toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm i))
  · intro i p hp
    obtain ⟨q, ⟨p, hp, rfl⟩, rfl⟩ := hp
    exact eighth_box_mem (u i) (c i) (tubeStretch_mem_box (u i) (x i) hd
      (hdr.trans hr1) (hd.trans_le hdr) (hYT i hp))
  · intro i
    have hvU : volume (U i) = ENNReal.ofReal (r ^ 2 / 8) := by
      dsimp [U]
      rw [volume_orthogonalBox]
      · congr 1
        simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val, Fin.isValue]
        ring
      · intro j
        fin_cases j <;> norm_num <;> positivity
    have hvZ : volume (Z i) = ENNReal.ofReal ((1 / 512 : ℝ) * (r / d) ^ 2) * volume (Y i) := by
      dsimp [Z, f]
      rw [eighthEquiv_volume, tubeStretch_volume, ← mul_assoc,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 512)]
    rw [hvU, hvZ]
    apply le_trans _ (mul_le_mul' le_rfl (hden i))
    rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / 512 : ℝ) * (r / d) ^ 2)]
    apply le_of_eq
    congr 1
    field_simp
    <;> ring
  · intro q hq
    obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hq
    obtain ⟨y, hy, rfl⟩ := hp
    refine mem_image_of_mem eighthEquiv (mem_thickening_iff.mpr ⟨y, mem_iUnion.mpr ⟨i, hy⟩, ?_⟩)
    have hh := tubeStretch_dist_le (u i) (x i) hd hdr (hYT i hy)
    exact hh.trans_lt (by linarith : 2 * r < 3 * r)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
