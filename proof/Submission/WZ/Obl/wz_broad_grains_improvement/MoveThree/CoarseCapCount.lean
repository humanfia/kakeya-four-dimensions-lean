-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.CoarseCapCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/CoarseCapCount.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit be976b9, CoarseCapCount.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.RescaleDegree
import Submission.WZ.Obl.wz_move_two_fibre_multiplicity_gain.CoarseCount

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped BigOperators
open WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain
  (coarse_decomp coarse_norm_sub_le)

/-- Essential distinctness bounds the number of coarse tubes through one
point whose directions lie in an oriented angular cap. A cubic bound is
enough for the scale increase; no sphere chart is needed. -/
theorem coarse_oriented_cap_count :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ρ θ : ℝ, 0 < ρ → ρ ≤ θ →
      ∀ (N : ℕ) (y w : Fin N → V), (∀ k, ‖w k‖ = 1) → X ρ N y w →
      ∀ p u : V,
        q N {k | p ∈ T ρ (y k) (w k) ∧ ‖w k - u‖ ≤ θ} ≤ C₀ * (θ / ρ) ^ 3 := by
  classical
  obtain ⟨M, hM⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.near_axis_finset_card_bound
      2 2 1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨((M : ℝ) + 1) * 125, by positivity, ?_⟩
  intro ρ θ hρ hρθ N y w hw hX p u
  have hθ : 0 < θ := hρ.trans_le hρθ
  let S : Finset (Fin N) := Finset.univ.filter
    (fun k => p ∈ T ρ (y k) (w k) ∧ ‖w k - u‖ ≤ θ)
  let label : Fin N → Fin 3 → ℕ := fun k j => ⌊(w k j - u j + 2 * θ) / ρ⌋₊
  let D : ℕ := ⌈4 * θ / ρ⌉₊
  have hcoordinate (k : Fin N) (hk : k ∈ S) (j : Fin 3) : |w k j - u j| ≤ θ := by
    have hh := WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm (w k - u) j
    exact hh.trans (Finset.mem_filter.mp hk).2.2
  have hlabel (k : Fin N) (hk : k ∈ S) (j : Fin 3) : label k j < D := by
    have hc := abs_le.mp (hcoordinate k hk j)
    exact WangZahlLot.Obl.wz_tube_packing_bound.floor_lt_ceil hρ
      (by linarith : 0 ≤ w k j - u j + 2 * θ)
      (by linarith : w k j - u j + 2 * θ < 4 * θ)
  have hlabel_close (i j : Fin N) (hi : i ∈ S) (hj : j ∈ S)
      (he : label i = label j) : ‖w i - w j‖ ≤ 2 * ρ := by
    have hcoord (a : Fin 3) : |w i a - w j a| < ρ := by
      have hi' := abs_le.mp (hcoordinate i hi a)
      have hj' := abs_le.mp (hcoordinate j hj a)
      have hh := WangZahlLot.Obl.wz_tube_packing_bound.abs_sub_lt_of_floor_eq hρ
        (by linarith : 0 ≤ w i a - u a + 2 * θ)
        (by linarith : 0 ≤ w j a - u a + 2 * θ) (congrFun he a)
      convert hh using 1
      congr 1
      ring
    exact coarse_norm_sub_le (hcoord 0) (hcoord 1) (hcoord 2)
  have hfiber (a : Fin 3 → ℕ) : (S.filter (fun k => label k = a)).card ≤ M := by
    let F := S.filter (fun k => label k = a)
    by_cases hF : F.Nonempty
    · obtain ⟨j, hj⟩ := hF
      have hjS := (Finset.mem_filter.mp hj).1
      apply hM hρ y w p (w j) F hw _ hX
      intro k hk
      have hkS := (Finset.mem_filter.mp hk).1
      have hkw : ‖w k - w j‖ ≤ 2 * ρ := hlabel_close k j hkS hjS
        ((Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hj).2.symm)
      refine ⟨(min_le_left _ _).trans hkw, ?_⟩
      obtain ⟨t, q₀, ht0, ht1, hq, hp⟩ :=
        coarse_decomp ((Finset.mem_filter.mp hkS).2.1)
      refine ⟨1 / 2 - t, abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
      have he : (y k + (1 / 2 : ℝ) • w k) - p - (1 / 2 - t) • w j =
          (1 / 2 - t) • (w k - w j) - q₀ := by rw [hp]; module
      rw [he]
      calc
        _ ≤ ‖(1 / 2 - t) • (w k - w j)‖ + ‖q₀‖ := norm_sub_le _ _
        _ = |1 / 2 - t| * ‖w k - w j‖ + ‖q₀‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ (1 / 2) * (2 * ρ) + ρ := by
          apply add_le_add _ hq.le
          exact mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩)
            hkw (norm_nonneg _) (by norm_num)
        _ = 2 * ρ := by ring
    · change F.card ≤ M
      rw [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.card_empty]
      exact Nat.zero_le M
  have hsize : (S.image label).card ≤ D ^ 3 := by
    calc
      _ ≤ (Fintype.piFinset (fun _ : Fin 3 => Finset.range D)).card := by
        apply Finset.card_le_card
        rintro a ha
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
        exact Fintype.mem_piFinset.mpr (fun j => Finset.mem_range.mpr (hlabel k hk j))
      _ = _ := by simp
  have hcount : S.card ≤ M * D ^ 3 := by
    calc
      S.card = ∑ a ∈ S.image label, (S.filter (fun k => label k = a)).card :=
        Finset.card_eq_sum_card_image label S
      _ ≤ ∑ _ ∈ S.image label, M := Finset.sum_le_sum (fun a _ => hfiber a)
      _ = M * (S.image label).card := by simp [mul_comm]
      _ ≤ M * D ^ 3 := Nat.mul_le_mul_left M hsize
  have hratio : 1 ≤ θ / ρ := (le_div_iff₀ hρ).mpr (by linarith)
  have hD : (D : ℝ) ≤ 5 * (θ / ρ) := by
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * θ / ρ)
    rw [mul_div_assoc] at hceil
    dsimp [D]
    rw [mul_div_assoc]
    linarith
  have hcard : q N {k | p ∈ T ρ (y k) (w k) ∧ ‖w k - u‖ ≤ θ} = S.card := by
    simp [q, S, Set.ncard_eq_toFinset_card']
  rw [hcard]
  calc
    (S.card : ℝ) ≤ M * (D : ℝ) ^ 3 := by exact_mod_cast hcount
    _ ≤ ((M : ℝ) + 1) * (5 * (θ / ρ)) ^ 3 := by gcongr; linarith
    _ = (((M : ℝ) + 1) * 125) * (θ / ρ) ^ 3 := by ring

/-- The unoriented cap version of the local coarse point count. -/
theorem coarse_projective_cap_count :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ρ θ : ℝ, 0 < ρ → ρ ≤ θ →
      ∀ (N : ℕ) (y w : Fin N → V), (∀ k, ‖w k‖ = 1) → X ρ N y w →
      ∀ p u : V,
        q N {k | p ∈ T ρ (y k) (w k) ∧ min ‖w k - u‖ ‖w k + u‖ ≤ θ} ≤
          C₀ * (θ / ρ) ^ 3 := by
  obtain ⟨C₀, hC₀, H⟩ := coarse_oriented_cap_count
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro ρ θ hρ hρθ N y w hw hX p u
  have he : {k | p ∈ T ρ (y k) (w k) ∧ min ‖w k - u‖ ‖w k + u‖ ≤ θ} =
      {k | p ∈ T ρ (y k) (w k) ∧ ‖w k - u‖ ≤ θ} ∪
        {k | p ∈ T ρ (y k) (w k) ∧ ‖w k - -u‖ ≤ θ} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_union, min_le_iff, sub_neg_eq_add]
    tauto
  change (({k | p ∈ T ρ (y k) (w k) ∧ min ‖w k - u‖ ‖w k + u‖ ≤ θ} : Set (Fin N)).ncard : ℝ) ≤ _
  rw [he]
  calc
    _ ≤ q N {k | p ∈ T ρ (y k) (w k) ∧ ‖w k - u‖ ≤ θ} +
        q N {k | p ∈ T ρ (y k) (w k) ∧ ‖w k - -u‖ ≤ θ} := by
      exact_mod_cast Set.ncard_union_le _ _
    _ ≤ C₀ * (θ / ρ) ^ 3 + C₀ * (θ / ρ) ^ 3 :=
      add_le_add (H ρ θ hρ hρθ N y w hw hX p u) (H ρ θ hρ hρθ N y w hw hX p (-u))
    _ = _ := by ring

/-- A direction packet containing a prescribed power fraction of a highly
overlapping coarse family must occur at a larger angular scale. -/
theorem packet_scale_growth {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcount : ∀ ρ θ : ℝ, 0 < ρ → ρ ≤ θ →
      ∀ (N : ℕ) (y w : Fin N → V), (∀ k, ‖w k‖ = 1) → X ρ N y w →
      ∀ p u : V,
        q N {k | p ∈ T ρ (y k) (w k) ∧ min ‖w k - u‖ ‖w k + u‖ ≤ θ} ≤
          C₀ * (θ / ρ) ^ 3)
    {δ ρ θ β q₀ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ)
    (hδθ : δ ≤ θ) (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (hbudget : 16 * C₀ * δ ^ (q₀ - β - 3 * t) ≤ 1)
    {N : ℕ} (y w : Fin N → V) (hw : ∀ k, ‖w k‖ = 1) (hX : X ρ N y w)
    (p u : V) (K W : Finset (Fin N))
    (hK : ∀ k ∈ K, p ∈ T ρ (y k) (w k)) (hWK : W ⊆ K)
    (hhigh : δ ^ (-q₀) < K.card)
    (hlarge : ((K.card : ℝ) / 2) * θ ^ β ≤ W.card)
    (hcap : ∀ k ∈ W, min ‖w k - u‖ ‖w k + u‖ ≤ 2 * θ) :
    δ ^ (-t) * ρ ≤ θ := by
  by_contra hsmall
  have hθsmall : θ < δ ^ (-t) * ρ := lt_of_not_ge hsmall
  have hθ : 0 < θ := hδ.trans_le hδθ
  have hp : 1 ≤ δ ^ (-t) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hR : ρ ≤ 2 * δ ^ (-t) * ρ := by nlinarith
  have hWcount : (W.card : ℝ) ≤ 8 * C₀ * δ ^ (-3 * t) := by
    have hsub : (W : Set (Fin N)) ⊆
        {k | p ∈ T ρ (y k) (w k) ∧ min ‖w k - u‖ ‖w k + u‖ ≤
          2 * δ ^ (-t) * ρ} := by
      intro k hk
      exact ⟨hK k (hWK hk), (hcap k hk).trans (by linarith)⟩
    calc
      (W.card : ℝ) ≤ q N {k | p ∈ T ρ (y k) (w k) ∧
          min ‖w k - u‖ ‖w k + u‖ ≤ 2 * δ ^ (-t) * ρ} := by
        dsimp only [q]
        exact_mod_cast (Set.ncard_le_ncard hsub (Set.toFinite _))
      _ ≤ C₀ * ((2 * δ ^ (-t) * ρ) / ρ) ^ 3 :=
        hcount ρ _ hρ hR N y w hw hX p u
      _ = 8 * C₀ * δ ^ (-3 * t) := by
        rw [mul_div_cancel_right₀ _ hρ.ne', mul_pow,
          ← Real.rpow_natCast (δ ^ (-t)) 3, ← Real.rpow_mul hδ.le]
        norm_num
        rw [show t * 3 = 3 * t by ring]
        ring
  have hlower : δ ^ (β - q₀) / 2 < (W.card : ℝ) := by
    calc
      _ = (δ ^ (-q₀) / 2) * δ ^ β := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hδ]
        congr 2
        ring
      _ < ((K.card : ℝ) / 2) * δ ^ β :=
        mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hδ β)
      _ ≤ ((K.card : ℝ) / 2) * θ ^ β :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hδθ hβ) (by positivity)
      _ ≤ W.card := hlarge
  have hupper : 8 * C₀ * δ ^ (-3 * t) ≤ δ ^ (β - q₀) / 2 := by
    calc
      _ = (16 * C₀ * δ ^ (q₀ - β - 3 * t)) * (δ ^ (β - q₀) / 2) := by
        have heq : δ ^ (q₀ - β - 3 * t) * δ ^ (β - q₀) = δ ^ (-3 * t) := by
          rw [← Real.rpow_add hδ]
          congr 1
          ring
        calc
          _ = 8 * C₀ * (δ ^ (q₀ - β - 3 * t) * δ ^ (β - q₀)) := by rw [heq]
          _ = _ := by ring
      _ ≤ 1 * (δ ^ (β - q₀) / 2) :=
        mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = _ := one_mul _
  exact (hlower.trans_le (hWcount.trans hupper)).false

/-- The prescribed `δ^(-ζ/2000)` increase follows uniformly from the
`δ^(-ζ/2)` overlap reduction and dense angular packets. -/
theorem coarse_packet_scale_cutoff {ζ β : ℝ} (hζ : 0 < ζ)
    (hβ : 0 ≤ β) (hβζ : β ≤ ζ / 100) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ ρ θ : ℝ,
      0 < δ → δ ≤ d₀ → 0 < ρ → δ ≤ θ →
      ∀ (N : ℕ) (y w : Fin N → V), (∀ k, ‖w k‖ = 1) → X ρ N y w →
      ∀ (p u : V) (K W : Finset (Fin N)),
        (∀ k ∈ K, p ∈ T ρ (y k) (w k)) → W ⊆ K →
        δ ^ (-(ζ / 2)) < K.card → ((K.card : ℝ) / 2) * θ ^ β ≤ W.card →
        (∀ k ∈ W, min ‖w k - u‖ ‖w k + u‖ ≤ 2 * θ) →
        δ ^ (-(ζ / 2000)) * ρ ≤ θ := by
  obtain ⟨C₀, hC₀, hcount⟩ := coarse_projective_cap_count
  let d₀ := min 1 ((1 / (16 * C₀)) ^ (1 / (ζ / 4)))
  have hd₀ : 0 < d₀ := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨d₀, hd₀, min_le_left _ _, ?_⟩
  intro δ ρ θ hδ hδd hρ hδθ N y w hw hX p u K W hK hWK hhigh hlarge hcap
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  have hsmall : δ ^ (ζ / 4) ≤ 1 / (16 * C₀) := by
    calc
      _ ≤ ((1 / (16 * C₀)) ^ (1 / (ζ / 4))) ^ (ζ / 4) :=
        Real.rpow_le_rpow hδ.le (hδd.trans (min_le_right _ _)) (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul (by positivity : 0 ≤ 1 / (16 * C₀)),
          one_div_mul_cancel (by positivity : (ζ / 4) ≠ 0), Real.rpow_one]
  apply packet_scale_growth hC₀ hcount hδ hδ1 hρ hδθ hβ
    (by positivity : 0 ≤ ζ / 2000) _ y w hw hX p u K W hK hWK hhigh hlarge hcap
  have he : δ ^ (ζ / 2 - β - 3 * (ζ / 2000)) ≤ δ ^ (ζ / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hh := he.trans hsmall
  have hmul := (le_div_iff₀ (by positivity : 0 < 16 * C₀)).mp hh
  nlinarith

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
