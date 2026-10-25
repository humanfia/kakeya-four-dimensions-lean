-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.PreparedHierarchy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.RestrictionErrors
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyAnalysis

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridCell gridUnion)

lemma HierarchyRestriction.sum_bottom {J : ℕ} {T : TubeHierarchy J}
    {S : Finset (Fin (T.layer J).card)} (R : HierarchyRestriction T S)
    (w : Fin (T.layer J).card → ENNReal) :
    (∑ i, w (R.map J i)) = ∑ i ∈ S, w i := by
  classical
  apply Finset.sum_bij (fun i _ => R.map J i)
  · intro i hi
    exact R.bottom_mem i
  · intro i hi k hk he
    exact R.injective J he
  · intro i hi
    have hi' : i ∈ Set.range (R.map J) := by rw [R.bottom_image]; exact hi
    obtain ⟨k, rfl⟩ := hi'
    exact ⟨k, Finset.mem_univ _, rfl⟩
  · intro i hi
    rfl

lemma shadow_density_size {density lam r a : ℝ} (hden : 0 ≤ density) (hr : 0 ≤ r)
    (ha : r / 512 ≤ a) (hcoef : 4194304 * density ≤ lam) :
    density * r ^ 2 ≤ lam * a ^ 2 / 16 := by
  have har : r ≤ 512 * a := by linarith
  have hs := pow_le_pow_left₀ hr har 2
  have hm := mul_le_mul_of_nonneg_left hs hden
  have hc := mul_le_mul_of_nonneg_right hcoef (sq_nonneg a)
  nlinarith only [hm, hc]

/-- Assemble balanced leaf selection and the fixed-reference density classes into
a hierarchy with uniform analytic frames. No radius is changed. -/
theorem prepare_hierarchy_from_classes {d θ τ g gap : ℝ} {J : ℕ}
    (C : HierarchyCertificate d θ g gap J) (hd : 0 < d) (hd1 : d < 1)
    (hτ : 0 < τ) (hθ : θ ≤ τ) (hgap : d ^ gap ≤ 1 / 64)
    (q : ℕ) (hq : 0 < q) (hcard : ((C.tree.layer J).card : ℝ) < (d ^ (-τ)) ^ q)
    (hsmall : 2 * (q : ℝ) ^ (J + 1) * d ^ τ ≤ 1) (hsmallG : 8388608 * d ^ τ ≤ 1)
    (Z : Fin (C.tree.layer J).card → Set Space)
    (hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ C.shading i)
    (hret : ENNReal.ofReal (d ^ τ) * (∑ i, volume (C.shading i)) ≤ ∑ i, volume (Z i))
    (a t : ℕ → ℝ) (G : ℕ → Finset (Fin 3 → ℤ))
    (ha : ∀ j, j < J → 0 < a j ∧ (C.tree.layer j).radius / 512 ≤ a j ∧
      a j ≤ (C.tree.layer j).radius / 256)
    (hnest : ∀ j, j + 1 < J → ∃ k : ℕ, 0 < k ∧ a j = (k : ℝ) * a (j + 1))
    (hgrid : ∀ j, j < J → ∀ i, Z i ⊆ gridUnion (a j) (G j))
    (ht : ∀ j, j < J → 0 < t j)
    (hclass : ∀ j, j < J → ∀ z ∈ G j,
      t j * (a j) ^ 3 ≤ volume.real ((⋃ i, C.shading i) ∩ gridCell (a j) z) ∧
      d ^ τ * volume.real ((⋃ i, C.shading i) ∩ gridCell (a j) z) ≤ t j * (a j) ^ 3) :
    ∃ C' : HierarchyCertificate d (8 * τ) g gap J,
      (∀ j, (C'.tree.layer j).radius = (C.tree.layer j).radius) ∧
      (C'.tree.layer J).card ≤ (C.tree.layer J).card ∧
      (⋃ i, C'.shading i) ⊆ (⋃ i, C.shading i) ∧
      ENNReal.ofReal (d ^ (2 * τ)) * (∑ i, volume (C.shading i)) ≤ ∑ i, volume (C'.shading i) ∧
      Nonempty (HierarchyAnalysis C'.tree (⋃ i, C.shading i) d (8 * τ) (d ^ τ)) := by
  classical
  have hsmall56 : 56 * d ^ τ ≤ 1 :=
    power_coefficient_bound hd hd1.le (by norm_num) (by norm_num) le_rfl hsmallG
  obtain ⟨S, hS, hretain, hden, hbal, hScard⟩ := regularize_dense_leaves C.tree C.family
    hd hd1 hτ hθ (fun i => (hZ i).2) hret q hq hcard hsmall hsmall56
  let R : HierarchyRestriction C.tree S := Classical.choice (exists_hierarchy_restriction C.tree S hS)
  let lam := d ^ (θ + τ) / 2
  have hcoef : 4194304 * d ^ (8 * τ) ≤ lam := by
    have hh : d ^ (8 * τ) ≤ d ^ (θ + τ) / 8388608 := density_power_bound hd (by norm_num)
      (power_coefficient_bound hd hd1.le (by norm_num) le_rfl (by linarith) hsmallG)
    dsimp [lam]
    linarith
  have hlam : d ^ (8 * τ) ≤ lam := by
    have hh := Real.rpow_nonneg hd.le (8 * τ)
    linarith
  have hZden (i) (hi : i ∈ S) : ENNReal.ofReal (d ^ (8 * τ) * d ^ 2) ≤ volume (Z i) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hlam (sq_nonneg d))).trans (hden i hi)
  have H : HierarchyControl d (8 * τ) g gap R.tree := R.control_of_power_retention C.control
    hd hd1.le (by linarith) (by linarith) (by linarith) hbal hScard
  have F := R.aligned_family C hd hd1.le (by linarith) (by linarith) hScard Z
    (fun i _ => (hZ i).1) (fun i _ => (hZ i).2) hZden
  let C' : HierarchyCertificate d (8 * τ) g gap J :=
    ⟨R.tree, Z ∘ R.map J, C.root_axis, C.scalar, H, R.alignment C.alignment, F⟩
  refine ⟨C', R.radius, ?_, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (R.map J) (R.injective J)
  · exact iUnion_subset fun i => ((hZ (R.map J i)).2).trans (subset_iUnion C.shading (R.map J i))
  · change ENNReal.ofReal (d ^ (2 * τ)) * (∑ i, volume (C.shading i)) ≤
      ∑ i, volume (Z (R.map J i))
    rw [R.sum_bottom (fun i => volume (Z i))]
    exact hretain
  · apply hierarchy_analysis_of_grids H hd (Real.rpow_nonneg hd.le τ) hgap
      (MeasurableSet.iUnion C.family.measurable)
      (fun i => (hZ (R.map J i)).1)
      (fun i => ((hZ (R.map J i)).2).trans (subset_iUnion C.shading (R.map J i)))
      F.shading (lam := lam) (fun i => hden _ (R.bottom_mem i)) hlam a t G
    · intro j hj
      rw [R.radius]
      exact ⟨(ha j hj).1, by linarith [(ha j hj).2.2, C.control.positive j hj.le]⟩
    · intro j hj
      rw [R.radius]
      exact shadow_density_size (Real.rpow_nonneg hd.le _) (C.control.positive j hj.le).le
        (ha j hj).2.1 hcoef
    · exact hnest
    · intro j hj i
      exact hgrid j hj (R.map J i)
    · exact ht
    · exact hclass

end WangZahlLot.Obl.wz_multiscale_finite_tower
