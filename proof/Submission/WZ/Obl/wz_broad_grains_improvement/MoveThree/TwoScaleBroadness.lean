-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.TwoScaleBroadness.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/TwoScaleBroadness.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/TwoScaleBroadness.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainWitnesses
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Defs
import Submission.WZ.Obl.wz_measurable_angular_selection
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.RescaleGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open scoped BigOperators
open WangZahlLot.Obl.wz_measurable_angular_selection (pd pd_comm pd_triangle)

private theorem card_le_fibre_upper {n N : ℕ} (F : Finset (Fin n))
    (K : Finset (Fin N)) (f : Fin n → Fin N) {M : ℝ}
    (hmap : ∀ i ∈ F, f i ∈ K)
    (hupper : ∀ k ∈ K, ((F.filter (fun i => f i = k)).card : ℝ) ≤ M) :
    (F.card : ℝ) ≤ M * K.card := by
  classical
  have hsum : (F.card : ℝ) =
      ∑ k ∈ K, ((F.filter (fun i => f i = k)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
  rw [hsum]
  calc
    _ ≤ ∑ _ ∈ K, M := Finset.sum_le_sum hupper
    _ = _ := by simp [mul_comm]

private theorem fibre_lower_le_card {n N : ℕ} (F : Finset (Fin n))
    (K : Finset (Fin N)) (f : Fin n → Fin N) {m : ℝ}
    (hmap : ∀ i ∈ F, f i ∈ K)
    (hlower : ∀ k ∈ K, m ≤ ((F.filter (fun i => f i = k)).card : ℝ)) :
    m * K.card ≤ F.card := by
  classical
  have hsum : (F.card : ℝ) =
      ∑ k ∈ K, ((F.filter (fun i => f i = k)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
  rw [hsum]
  calc
    _ = ∑ _ ∈ K, m := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum hlower

/-- Broadness at two adjacent angular scales combines with the fibre
multiplicity ratio. The coarse bound is stated also above its own scale,
where it follows from the trivial cardinal bound. -/
theorem two_scale_broadness {n N : ℕ} (v : Fin n → V) (w : Fin N → V)
    (F : Finset (Fin n)) (K : Finset (Fin N)) (f : Fin n → Fin N)
    {δ ρ θ β A B C m M : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hθ : 0 < θ) (_hβ : 0 ≤ β)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hmap : ∀ i ∈ F, f i ∈ K)
    (hlower : ∀ k ∈ K, m ≤ ((F.filter (fun i => f i = k)).card : ℝ))
    (hupper : ∀ k ∈ K, ((F.filter (fun i => f i = k)).card : ℝ) ≤ M * m)
    (hclose : ∀ i ∈ F, pd (v i) (w (f i)) ≤ A * ρ)
    (hfine : ∀ k ∈ K, ∀ u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      ((F.filter (fun i => f i = k ∧ pd (v i) u ≤ r)).card : ℝ) ≤
        B * (r / ρ) ^ β * (F.filter (fun i => f i = k)).card)
    (hcoarse : ∀ u R, ‖u‖ = 1 → ρ ≤ R →
      ((K.filter (fun k => pd (w k) u ≤ R)).card : ℝ) ≤
        C * (R / θ) ^ β * K.card) :
    ∀ u r, ‖u‖ = 1 → δ ≤ r →
      ((F.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤
        (M * B * C * (A + 1) ^ β) * (r / θ) ^ β * F.card := by
  classical
  intro u r hu hr
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hr0 : 0 < r := hδ.trans_le hr
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hAB : 0 < A + 1 := by linarith
  have hmass : m * K.card ≤ F.card := fibre_lower_le_card F K f hmap hlower
  let Q := F.filter (fun i => pd (v i) u ≤ r)
  have hQk (k : Fin N) :
      Q.filter (fun i => f i = k) =
        F.filter (fun i => f i = k ∧ pd (v i) u ≤ r) := by
    ext i
    simp only [Q, Finset.mem_filter]
    tauto
  have hnear (R : ℝ) (hR : A * ρ + r ≤ R) :
      ∀ i ∈ Q, f i ∈ K.filter (fun k => pd (w k) u ≤ R) := by
    intro i hi
    obtain ⟨hiF, hcap⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hmap i hiF, ?_⟩
    calc
      pd (w (f i)) u ≤ pd (w (f i)) (v i) + pd (v i) u := pd_triangle _ _ _
      _ = pd (v i) (w (f i)) + pd (v i) u := by rw [pd_comm (w (f i))]
      _ ≤ A * ρ + r := add_le_add (hclose i hiF) hcap
      _ ≤ R := hR
  by_cases hrρ : r ≤ ρ
  · let R := (A + 1) * ρ
    have hR : ρ ≤ R := by dsimp [R]; nlinarith
    have hmapQ := hnear R (by dsimp [R]; linarith)
    have hcap : (Q.card : ℝ) ≤
        (B * (r / ρ) ^ β * (M * m)) *
          (K.filter (fun k => pd (w k) u ≤ R)).card := by
      apply card_le_fibre_upper Q _ f hmapQ
      intro k hk
      rw [hQk]
      exact (hfine k (Finset.mem_filter.mp hk).1 u r hu hr hrρ).trans
        (mul_le_mul_of_nonneg_left (hupper k (Finset.mem_filter.mp hk).1)
          (by positivity))
    have hpower : (r / ρ) ^ β * (R / θ) ^ β =
        (A + 1) ^ β * (r / θ) ^ β := by
      rw [← Real.mul_rpow (by positivity : 0 ≤ r / ρ) (by dsimp [R]; positivity),
        ← Real.mul_rpow hAB.le (by positivity : 0 ≤ r / θ)]
      congr 1
      dsimp [R]
      field_simp
    calc
      (Q.card : ℝ) ≤ _ := hcap
      _ ≤ (B * (r / ρ) ^ β * (M * m)) * (C * (R / θ) ^ β * K.card) :=
        mul_le_mul_of_nonneg_left (hcoarse u R hu hR) (by positivity)
      _ = (M * B * C * (A + 1) ^ β) * (r / θ) ^ β * (m * K.card) := by
        calc
          _ = M * B * C * ((r / ρ) ^ β * (R / θ) ^ β) * (m * K.card) := by ring
          _ = _ := by rw [hpower]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  · have hρr : ρ ≤ r := (lt_of_not_ge hrρ).le
    let R := (A + 1) * r
    have hR : ρ ≤ R := by dsimp [R]; nlinarith
    have hmapQ := hnear R (by dsimp [R]; nlinarith)
    have hcap : (Q.card : ℝ) ≤ (M * m) *
        (K.filter (fun k => pd (w k) u ≤ R)).card := by
      apply card_le_fibre_upper Q _ f hmapQ
      intro k hk
      calc
        _ ≤ ((F.filter (fun i => f i = k)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
        _ ≤ M * m := hupper k (Finset.mem_filter.mp hk).1
    have hpower : (R / θ) ^ β = (A + 1) ^ β * (r / θ) ^ β := by
      rw [← Real.mul_rpow hAB.le (by positivity : 0 ≤ r / θ)]
      congr 1
      dsimp [R]
      ring
    calc
      (Q.card : ℝ) ≤ _ := hcap
      _ ≤ (M * m) * (C * (R / θ) ^ β * K.card) :=
        mul_le_mul_of_nonneg_left (hcoarse u R hu hR) (mul_nonneg hM hm)
      _ = (M * C * (A + 1) ^ β * (r / θ) ^ β) * (m * K.card) := by rw [hpower]; ring
      _ ≤ (M * C * (A + 1) ^ β * (r / θ) ^ β) * F.card :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hB
          (by positivity : 0 ≤ M * C * (A + 1) ^ β * (r / θ) ^ β * (F.card : ℝ))
        nlinarith only [hh]

/-- A broadness bound on its natural interval extends above that interval
by the elementary bound by the full cardinality. -/
theorem cap_bound_above_scale {N : ℕ} (w : Fin N → V) (K : Finset (Fin N))
    {ρ θ β C : ℝ} (_hρ : 0 < ρ) (hθ : 0 < θ) (hβ : 0 ≤ β) (hC : 1 ≤ C)
    (hcap : ∀ u R, ‖u‖ = 1 → ρ ≤ R → R ≤ θ →
      ((K.filter (fun k => pd (w k) u ≤ R)).card : ℝ) ≤
        C * (R / θ) ^ β * K.card) :
    ∀ u R, ‖u‖ = 1 → ρ ≤ R →
      ((K.filter (fun k => pd (w k) u ≤ R)).card : ℝ) ≤
        C * (R / θ) ^ β * K.card := by
  classical
  intro u R hu hR
  by_cases hRθ : R ≤ θ
  · exact hcap u R hu hR hRθ
  · have hratio : 1 ≤ R / θ := (le_div_iff₀ hθ).mpr (by linarith)
    have hp : 1 ≤ (R / θ) ^ β := Real.one_le_rpow hratio hβ
    have hprod : 1 ≤ C * (R / θ) ^ β := by nlinarith
    calc
      _ ≤ (K.card : ℝ) := by exact_mod_cast Finset.card_filter_le K _
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg K.card)

/-- The exact fine/coarse predicates turn coarse directional broadness into
global fine directional broadness. No geometric prism reconstruction is used. -/
theorem global_broad_of_coarse_broad
    {ω ζ δ h ρ θ B m : ℝ} {n N : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hδρ : δ ≤ ρ)
    (hθ : 0 < θ) (hβ : 0 ≤ ω * ζ / 100) (hB : 1 ≤ B) (hm : 0 ≤ m)
    (hv : ∀ i, ‖v i‖ = 1)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hmult : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} ∈ Set.Icc m (2 * m))
    (hcoarse : ∀ p u R, ‖u‖ = 1 → ρ ≤ R → R ≤ θ →
      q N {k | (∃ i ∈ S, f i = k ∧ p ∈ Z i) ∧ pd (w k) u ≤ R} ≤
        B * (R / θ) ^ (ω * ζ / 100) *
          q N {k | ∃ i ∈ S, f i = k ∧ p ∈ Z i}) :
    ∀ p u r, ‖u‖ = 1 → δ ≤ r →
      q n {i | i ∈ S ∧ p ∈ Z i ∧ pd (v i) u ≤ r} ≤
        (2 * δ ^ (-h) * B * (5 : ℝ) ^ (ω * ζ / 100)) *
          (r / θ) ^ (ω * ζ / 100) * q n {i | i ∈ S ∧ p ∈ Z i} := by
  classical
  intro p u r hu hr
  let F := Finset.univ.filter (fun i => i ∈ S ∧ p ∈ Z i)
  let K := ({k | ∃ i ∈ S, f i = k ∧ p ∈ Z i} : Set (Fin N)).toFinset
  have hmap : ∀ i ∈ F, f i ∈ K := by
    intro i hi
    obtain ⟨_, hi, hp⟩ := Finset.mem_filter.mp hi
    exact Set.mem_toFinset.mpr ⟨i, hi, rfl, hp⟩
  have hcard (k : Fin N) : ((F.filter (fun i => f i = k)).card : ℝ) =
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
    simp [F, q, Set.ncard_eq_toFinset_card', Finset.filter_filter,
      and_left_comm, and_comm]
  have hlow (k : Fin N) (hk : k ∈ K) :
      m ≤ ((F.filter (fun i => f i = k)).card : ℝ) := by
    rw [hcard]
    have hk' : ∃ i ∈ S, f i = k ∧ p ∈ Z i := by
      simpa only [K, Set.mem_toFinset, Set.mem_ofPred_eq] using hk
    exact (hmult k p hk').1
  have hupp (k : Fin N) (hk : k ∈ K) :
      ((F.filter (fun i => f i = k)).card : ℝ) ≤ 2 * m := by
    rw [hcard]
    have hk' : ∃ i ∈ S, f i = k ∧ p ∈ Z i := by
      simpa only [K, Set.mem_toFinset, Set.mem_ofPred_eq] using hk
    exact (hmult k p hk').2
  have hclose (i : Fin n) (hi : i ∈ F) : pd (v i) (w (f i)) ≤ 4 * ρ := by
    have hiS := (Finset.mem_filter.mp hi).2.1
    exact (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.pd_lt_of_tube_subset
      hδ (hv i) (hC.2.2.1 (f i)) (hC.2.2.2.1 i hiS)).le
  have hfine (k : Fin N) (_hk : k ∈ K) (u : V) (r : ℝ)
      (hu : ‖u‖ = 1) (hr : δ ≤ r) (hrρ : r ≤ ρ) :
      ((F.filter (fun i => f i = k ∧ pd (v i) u ≤ r)).card : ℝ) ≤
        δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) *
          (F.filter (fun i => f i = k)).card := by
    simpa [F, pd, q, Set.ncard_eq_toFinset_card', Finset.filter_filter,
      and_assoc, and_left_comm, and_comm] using hbr k p u r hu hr hrρ
  have hcoarse' (u : V) (R : ℝ) (hu : ‖u‖ = 1) (hR : ρ ≤ R) (hRθ : R ≤ θ) :
      ((K.filter (fun k => pd (w k) u ≤ R)).card : ℝ) ≤
        B * (R / θ) ^ (ω * ζ / 100) * K.card := by
    simpa [K, q, Set.ncard_eq_toFinset_card', Finset.filter_filter] using hcoarse p u R hu hR hRθ
  have hresult := two_scale_broadness v w F K f hδ hδρ hθ hβ (by norm_num : (0 : ℝ) ≤ 4)
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith : -h ≤ 0))
    (zero_le_one.trans hB) hm (by norm_num : (0 : ℝ) ≤ 2) hmap hlow hupp hclose hfine
    (cap_bound_above_scale w K (hδ.trans_le hδρ) hθ hβ hB hcoarse') u r hu hr
  norm_num only [show (4 : ℝ) + 1 = 5 by norm_num] at hresult
  simpa [F, q, Set.ncard_eq_toFinset_card', Finset.filter_filter, and_assoc] using hresult

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
