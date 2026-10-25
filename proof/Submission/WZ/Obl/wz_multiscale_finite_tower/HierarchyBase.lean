-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.HierarchyBase.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Hierarchy

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced leafFiber)
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (ConvexCount SlabBound)

noncomputable def alignedBaseTree (d : ℝ) (u : Space) (hu : ‖u‖ = 1)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1) : TubeHierarchy 1 where
  layer j := match j with
    | 0 => ⟨1, 1, by omega, (fun _ => - (1 / 2 : ℝ) • u), (fun _ => u), (fun _ => hu)⟩
    | _ + 1 => ⟨d, n, hn, x, v, hv⟩
  parent j := match j with
    | 0 => fun _ => 0
    | _ + 1 => id
  ancestor j := match j with
    | 0 => fun _ => 0
    | _ + 1 => id
  terminal := rfl
  coherent j hj i := by
    have hj0 : j = 0 := by omega
    subst j
    rfl
  active j hj := by
    cases j with
    | zero =>
      intro k
      exact ⟨⟨0, hn⟩, Subsingleton.elim _ _⟩
    | succ j => exact Function.surjective_id

lemma alignedBaseTree_alignment {d lam K L h : ℝ} {u : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : AlignedFamily d lam K L u h n x v Y) :
    HierarchyAlignment u h (alignedBaseTree d u hF.root_unit hF.nonempty x v hF.unit) := by
  refine ⟨fun k => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro j hj hj1 i
    have hj' : j = 1 := by omega
    subst j
    exact hF.direction_cap i
  · intro j hj hj1 i
    have hj' : j = 1 := by omega
    subst j
    exact hF.aligned i
  · intro j hj hj1 i
    have hj' : j = 1 := by omega
    subst j
    exact hF.midpoint i

lemma alignedBaseTree_control {d θ g gap h : ℝ} {u : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hd : 0 < d) (hd32 : d ≤ 1 / 32) (hd1 : d < 1) (hθ : 0 ≤ θ) (hg : 1 ≤ g) (hgap : gap ≤ 1)
    (hF : AlignedFamily d (d ^ θ) (d ^ (-θ)) (d ^ (-θ)) u h n x v Y) :
    HierarchyControl d θ g gap (alignedBaseTree d u hF.root_unit hF.nonempty x v hF.unit) := by
  classical
  have hR : 1 ≤ d ^ (-θ) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hd hd1.le (neg_nonpos.mpr hθ)
  refine ⟨by omega, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · exact zero_lt_one
    · exact hd
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact hd1
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    change d ^ g * 1 ≤ d
    simpa only [mul_one, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hd hd1.le hg
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    change d ≤ d ^ gap * 1
    simpa only [mul_one, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hd hd1.le hgap
  · intro j hj i
    have hj0 : j = 0 := by omega
    subst j
    exact (hF.ball i).trans (centered_root_contains_ball u)
  · intro j hj i
    have hj0 : j = 0 := by omega
    subst j
    simpa only [alignedBaseTree, mul_one] using
      representative_root_buffer hd32 (hF.midpoint i) (hF.direction_cap i)
  · intro j hj k
    have hj0 : j = 0 := by omega
    subst j
    change Fin 1 at k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    simpa only [alignedBaseTree, ConvexCount, KatzTao, true_and] using hF.count
  · intro j hj k
    have hj0 : j = 0 := by omega
    subst j
    change Fin 1 at k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    simpa only [alignedBaseTree, SlabBound, true_and] using hF.slab
  · intro j hj i hi k hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · change ((leafFiber (Finset.univ : Finset (Fin n)) (fun _ => (0 : Fin 1)) i).card : ℝ) ≤
        d ^ (-θ) * (leafFiber (Finset.univ : Finset (Fin n)) (fun _ => (0 : Fin 1)) k).card
      have he (i : Fin n) : leafFiber Finset.univ (fun _ : Fin n => (0 : Fin 1)) i = Finset.univ := by
        ext a
        simp [leafFiber]
      rw [he i, he k]
      simpa only [Finset.card_univ, Fintype.card_fin, one_mul] using
        mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg n)
    · change ((leafFiber (Finset.univ : Finset (Fin n)) id i).card : ℝ) ≤
        d ^ (-θ) * (leafFiber (Finset.univ : Finset (Fin n)) id k).card
      have he (i : Fin n) : leafFiber Finset.univ id i = {i} := by
        ext a
        simp [leafFiber]
      have hc (i : Fin n) : (leafFiber Finset.univ id i).card = 1 :=
        (congrArg Finset.card (he i)).trans (Finset.card_singleton i)
      rw [hc i, hc k]
      simpa only [Nat.cast_one, mul_one] using hR

noncomputable def initialHierarchy {d θ g gap h : ℝ} {u : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hd : 0 < d) (hd32 : d ≤ 1 / 32) (hd1 : d < 1) (hθ : 0 ≤ θ) (hg : 1 ≤ g) (hgap : gap ≤ 1)
    (hF : AlignedFamily d (d ^ θ) (d ^ (-θ)) (d ^ (-θ)) u h n x v Y) :
    HierarchyCertificate d θ g gap 1 where
  tree := alignedBaseTree d u hF.root_unit hF.nonempty x v hF.unit
  shading := Y
  root_axis := u
  scalar := h
  control := alignedBaseTree_control hd hd32 hd1 hθ hg hgap hF
  alignment := alignedBaseTree_alignment hF
  family := hF

end WangZahlLot.Obl.wz_multiscale_finite_tower
