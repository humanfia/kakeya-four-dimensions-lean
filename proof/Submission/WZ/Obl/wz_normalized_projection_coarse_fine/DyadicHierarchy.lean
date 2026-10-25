-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.DyadicHierarchy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.DyadicCells
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.UniformFibers

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Finset
open WangZahlLot.Obl.wz_tower_balanced_refinement

noncomputable section

attribute [local instance] Classical.propDecidable

/-- An occupied dyadic cell has at most the ambient number of finer descendants. -/
theorem dyadic_occupied_count_le {α : Type*} [DecidableEq α] {d j k : ℕ}
    (U : Finset α) (p : α → EuclideanSpace ℝ (Fin d)) (hjk : j ≤ k) :
    (U.image (fun a => dyadicLabel k (p a))).card ≤
      (U.image (fun a => dyadicLabel j (p a))).card * (2 ^ (k - j)) ^ d := by
  classical
  let M : ℕ := 2 ^ (k - j)
  have hM : 0 < M := by dsimp [M]; positivity
  have hMz : 0 < (M : ℤ) := by exact_mod_cast hM
  let C := U.image (fun a => dyadicLabel j (p a))
  let F := U.image (fun a => dyadicLabel k (p a))
  let coarse : (Fin d → ℤ) → (Fin d → ℤ) := fun l i => l i / M
  have hcoarse (l : F) : coarse l ∈ C := by
    obtain ⟨a, ha, hpa⟩ := Finset.mem_image.mp l.property
    refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
    funext i
    change dyadicLabel j (p a) i = l.val i / M
    rw [dyadicLabel_coarse hjk, ← hpa]
    simp [M]
  let g : F → C × (Fin d → Fin M) := fun l =>
    (⟨coarse l, hcoarse l⟩, fun i =>
      ⟨(l.val i % M).toNat,
        (Int.toNat_lt (Int.emod_nonneg _ hMz.ne')).mpr (Int.emod_lt_of_pos _ hMz)⟩)
  have hg : Function.Injective g := by
    intro l l' he
    apply Subtype.ext
    funext i
    have hc : l.val i / M = l'.val i / M := by
      exact congrFun (congrArg (fun a => a.1.val) he) i
    have hr : (l.val i % M).toNat = (l'.val i % M).toNat := by
      exact congrArg Fin.val (congrFun (congrArg Prod.snd he) i)
    have hr' : l.val i % M = l'.val i % M := by
      have hh := congrArg (fun a : ℕ => (a : ℤ)) hr
      simpa only [Int.toNat_of_nonneg (Int.emod_nonneg _ hMz.ne')] using hh
    calc
      l.val i = l.val i % M + (M : ℤ) * (l.val i / M) := (Int.emod_add_mul_ediv _ _).symm
      _ = l'.val i % M + (M : ℤ) * (l'.val i / M) := by rw [hr', hc]
      _ = l'.val i := Int.emod_add_mul_ediv _ _
  have hh := Fintype.card_le_of_injective g hg
  simpa [C, F, M, Fintype.card_prod, Fintype.card_fun] using hh

/-- Ambient dyadic packing transports a terminal count lower bound to every coarse level. -/
lemma dyadic_count_lower_of_terminal {α : Type*} [DecidableEq α] {d L k : ℕ}
    (U : Finset α) (p : α → EuclideanSpace ℝ (Fin d)) (hkL : k ≤ L)
    {A N : ℝ} (hterminal : N * (2 : ℝ) ^ A ≤
      (U.image (fun a => dyadicLabel L (p a))).card) :
    N * (2 : ℝ) ^ (A - d * (L - k : ℕ)) ≤
      (U.image (fun a => dyadicLabel k (p a))).card := by
  have hpacking := dyadic_occupied_count_le U p hkL
  have hp : ((U.image (fun a => dyadicLabel L (p a))).card : ℝ) ≤
      ((U.image (fun a => dyadicLabel k (p a))).card : ℝ) *
        (2 : ℝ) ^ ((d : ℝ) * (L - k : ℕ)) := by
    have he : (2 : ℝ) ^ ((d : ℝ) * (L - k : ℕ)) = ((2 : ℝ) ^ (L - k)) ^ d := by
      rw [mul_comm, Real.rpow_natCast_mul (by norm_num), Real.rpow_natCast]
    rw [he]
    exact_mod_cast hpacking
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < (2 : ℝ) ^ ((d : ℝ) * (L - k : ℕ)))).mp
  calc
    _ = N * (2 : ℝ) ^ A := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num)]
      congr 2
      ring
    _ ≤ (U.image (fun a => dyadicLabel L (p a))).card := hterminal
    _ ≤ _ := hp

/-- A balanced sparse dyadic hierarchy with enough terminal cells has a common coarse
level at which its fibers obey a Frostman count at every recorded finer level. -/
theorem balanced_dyadic_coarse_scale {α ι : Type*} [DecidableEq α] [Fintype ι]
    {d L : ℕ} (U : Finset α) (hU : U.Nonempty)
    (p : α → EuclideanSpace ℝ (Fin d)) (k : ι → ℕ) (i₀ : ι)
    {s e ε R : ℝ} (hL : k i₀ < L) (hs : 0 ≤ s) (he : 0 ≤ e)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hk : ∀ i, k i ≤ L)
    (hbal : ∀ i, Balanced U (fun a => dyadicLabel (k i) (p a)) R)
    (hterminal : ((U.image (fun a => dyadicLabel (k i₀) (p a))).card : ℝ) *
      (2 : ℝ) ^ (s * ((L : ℝ) - k i₀) - e) ≤
        (U.image (fun a => dyadicLabel L (p a))).card) :
    ∃ j, (k j : ℝ) ≤ L - ε * ((L : ℝ) - k i₀) ∧
      ∀ k', ∀ a ∈ U, ∀ b ∈ U,
        ((leafFiber U (fun a => dyadicLabel (k k') (p a)) b).card : ℝ) *
          (2 : ℝ) ^ (s * ((k k' : ℝ) - k j) -
            ((d : ℝ) * ε + e / ((L : ℝ) - k i₀)) * ((L : ℝ) - k j)) ≤
          R ^ 2 * (leafFiber U (fun a => dyadicLabel (k j) (p a)) a).card := by
  apply exists_uniform_frostman_scale U hU
    (fun i a => dyadicLabel (k i) (p a)) (fun i => (k i : ℝ)) i₀
    (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hL) hs (Nat.cast_nonneg d)
    he hε hε1 hR (fun i => by exact_mod_cast hk i) hbal
  intro i
  have hh := dyadic_count_lower_of_terminal U p (hk i) hterminal
  simpa only [Nat.cast_sub (hk i)] using hh

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
