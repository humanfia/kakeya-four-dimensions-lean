-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NormalizedCapCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NormalizedCapCount.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit be976b9, NormalizedCapCount.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CoarseCapCount
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.DirectionTransport
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainWitnesses
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate
  (unit pd pd_triangle pd_symm pd_nonneg areaSq pd_sq_le_areaSq)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm)

/-- The frozen transverse alignment implies projective closeness to the
long grain axis. -/
theorem aligned_grain_axis_close {ρ : ℝ} (hρ : 0 ≤ ρ)
    (e : V ≃ₗᵢ[ℝ] V) {w : V} (hw : ‖w‖ = 1)
    (halign : (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2) :
    pd w (boxAxis e 2) ≤ 20 * ρ := by
  have heq : pd w (boxAxis e 2) = pd (e w) (EuclideanSpace.basisFun (Fin 3) ℝ 2) := by
    unfold pd
    rw [← e.norm_map (w - boxAxis e 2), ← e.norm_map (w + boxAxis e 2)]
    simp only [map_sub, map_add, boxAxis, e.apply_symm_apply]
  rw [heq]
  have hnorm : ‖(EuclideanSpace.basisFun (Fin 3) ℝ 2 : V)‖ = 1 := by
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have H := pd_sq_le_areaSq (by simpa using hw : ‖e w‖ = 1) hnorm
  simp only [areaSq, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply,
    Fin.reduceEq, ite_true, ite_false, mul_zero, sub_zero, mul_one, zero_sub,
    neg_sq, zero_pow, zero_add, add_zero] at H
  simp only [EuclideanSpace.basisFun_apply]
  norm_num only [zero_pow, zero_add] at H
  nlinarith [pd_nonneg (e w) (EuclideanSpace.single 2 1)]

/-- A cap of normalized directions can be counted through any pointwise
injective representation by essentially distinct coarse tubes. -/
theorem represented_projective_cap_count :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ρ θ : ℝ, 0 < ρ → ρ ≤ θ →
      ∀ (N L : ℕ) (y w : Fin N → V) (ν : Fin L → V) (γ : Fin L → Fin N)
        (J : Finset (Fin L)), (∀ k, ‖w k‖ = 1) → X ρ N y w →
      ∀ p u : V,
        Set.InjOn γ (↑J : Set (Fin L)) →
        (∀ j ∈ J, p ∈ T ρ (y (γ j)) (w (γ j))) →
        (∀ j ∈ J, ∀ k ∈ J,
          pd (w (γ j)) (w (γ k)) ≤ 40 * (ρ + pd (ν j) (ν k))) →
        ((J.filter (fun j => pd (ν j) u ≤ θ)).card : ℝ) ≤ C₀ * (θ / ρ) ^ 3 := by
  classical
  obtain ⟨C₀, hC₀, Hcount⟩ := coarse_projective_cap_count
  refine ⟨C₀ * 120 ^ 3, by positivity, ?_⟩
  intro ρ θ hρ hρθ N L y w ν γ J hw hX p u hinj hmem hpair
  have hθ : 0 < θ := hρ.trans_le hρθ
  let K := J.filter (fun j => pd (ν j) u ≤ θ)
  by_cases hK : K.Nonempty
  · obtain ⟨j₀, hj₀⟩ := hK
    obtain ⟨hj₀J, hj₀cap⟩ := Finset.mem_filter.mp hj₀
    have himage : (K.image γ : Set (Fin N)) ⊆
        {k | p ∈ T ρ (y k) (w k) ∧ pd (w k) (w (γ j₀)) ≤ 120 * θ} := by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hjJ, hjcap⟩ := Finset.mem_filter.mp hj
      refine ⟨hmem j hjJ, ?_⟩
      have ht := pd_triangle (ν j) u (ν j₀)
      rw [pd_symm u] at ht
      have hh := hpair j hjJ j₀ hj₀J
      linarith
    have hinjK : Set.InjOn γ (↑K : Set (Fin L)) :=
      hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    calc
      (K.card : ℝ) = (K.image γ).card := by rw [Finset.card_image_of_injOn hinjK]
      _ ≤ q N {k | p ∈ T ρ (y k) (w k) ∧ pd (w k) (w (γ j₀)) ≤ 120 * θ} := by
        dsimp only [q]
        exact_mod_cast Set.ncard_le_ncard himage (Set.toFinite _)
      _ ≤ C₀ * ((120 * θ) / ρ) ^ 3 :=
        Hcount ρ _ hρ (by linarith) N y w hw hX p (w (γ j₀))
      _ = _ := by ring
  · change (K.card : ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hK, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The natural map has a fixed inverse projective distortion on the long
grain axes, even though it is very anisotropic on arbitrary directions. -/
theorem natural_axes_coarse_pair {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 < c)
    (A : V ≃ₗ[ℝ] V) (e e' : V ≃ₗᵢ[ℝ] V) (w w' : V)
    (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1)
    (halign : (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2)
    (halign' : (e' w' 0) ^ 2 + (e' w' 1) ^ 2 ≤ (10 * ρ) ^ 2)
    (hInv : ∀ u, ‖A.symm u‖ ≤ (4 * c) * ‖u‖)
    (hupper : ‖A (boxAxis e 2)‖ ≤ c⁻¹) :
    pd w w' ≤ 40 * (ρ + pd (unit (A (boxAxis e 2))) (unit (A (boxAxis e' 2)))) := by
  have H := unit_linear_inverse_pd A (by positivity : 0 ≤ 4 * c) (inv_pos.mpr hc)
    hInv (boxAxis_norm e 2) (boxAxis_norm e' 2) hupper
  have he : 2 * (4 * c) * c⁻¹ = (8 : ℝ) := by field_simp; ring
  rw [he] at H
  have h0 := aligned_grain_axis_close hρ e hw halign
  have h1 := aligned_grain_axis_close hρ e' hw' halign'
  have htri := pd_triangle w (boxAxis e 2) w'
  have htri' := pd_triangle (boxAxis e 2) (boxAxis e' 2) w'
  rw [pd_symm (boxAxis e' 2)] at htri'
  nlinarith [pd_nonneg (unit (A (boxAxis e 2))) (unit (A (boxAxis e' 2)))]

/-- Exact stage data give a uniform cubic cap count on every selected
normalized grain block. Common measurable cuts can be incorporated into
`Hs` before applying this result. -/
theorem HB_normalized_cap_count :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {δ h ρ a c b g m : ℝ} {n N L : ℕ}
      {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
      {y w : Fin N → V} {f : Fin n → Fin N}
      {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
      {Hs : Fin L → Set V} {γ : Fin L → Fin N},
      0 < ρ → 0 < c → (∀ k, ‖w k‖ = 1) → X ρ N y w →
      GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m →
      ∀ (Q : Finset (Fin L)) (A : V ≃ₗ[ℝ] V),
        (∀ u, ‖A.symm u‖ ≤ (4 * c) * ‖u‖) →
        (∀ j ∈ Q, ‖A (boxAxis (e j) 2)‖ ≤ c⁻¹) →
        ∀ p u θ, ρ ≤ θ →
          q L {j | j ∈ Q ∧ p ∈ Hs j ∧ pd (unit (A (boxAxis (e j) 2))) u ≤ θ} ≤
            C₀ * (θ / ρ) ^ 3 := by
  classical
  obtain ⟨C₀, hC₀, Hcount⟩ := represented_projective_cap_count
  refine ⟨C₀, hC₀, ?_⟩
  intro δ h ρ a c b g m n N L x v S Z y w f z e Hs γ hρ hc hw hX hHB Q A hInv hupper p u θ hρθ
  let J := Q.filter (fun j => p ∈ Hs j)
  have hJ (j) : j ∈ J ↔ j ∈ Q ∧ p ∈ Hs j := by simp [J]
  have hinj : Set.InjOn γ (↑J : Set (Fin L)) := by
    intro j hj k hk he
    by_contra hne
    exact Set.disjoint_left.mp (hHB.2.2.2.2.2.1 j k hne he)
      ((hJ j).mp hj).2 ((hJ k).mp hk).2
  have hmem (j) (hj : j ∈ J) : p ∈ T ρ (y (γ j)) (w (γ j)) :=
    (hHB.2.2.2.2.1 j).2.2.1 ((hHB.2.2.2.2.1 j).2.1 ((hJ j).mp hj).2)
  have hpair (j) (hj : j ∈ J) (k) (_hk : k ∈ J) :
      pd (w (γ j)) (w (γ k)) ≤ 40 *
        (ρ + pd (unit (A (boxAxis (e j) 2))) (unit (A (boxAxis (e k) 2)))) :=
    natural_axes_coarse_pair hρ.le hc A (e j) (e k) _ _ (hw _) (hw _)
      (hHB.2.2.2.2.1 j).2.2.2 (hHB.2.2.2.2.1 k).2.2.2
      hInv (hupper j ((hJ j).mp hj).1)
  have HH := Hcount ρ θ hρ hρθ N L y w (fun j => unit (A (boxAxis (e j) 2)))
    γ J hw hX p u hinj hmem hpair
  have he : {j | j ∈ Q ∧ p ∈ Hs j ∧ pd (unit (A (boxAxis (e j) 2))) u ≤ θ} =
      (↑(J.filter (fun j => pd (unit (A (boxAxis (e j) 2))) u ≤ θ)) : Set (Fin L)) := by
    ext j
    simp [J, and_assoc]
  simpa only [q, he, Set.ncard_coe_finset] using HH

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
