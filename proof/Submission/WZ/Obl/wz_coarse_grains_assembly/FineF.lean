-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.FineF.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Restrict

/-!
# The coarse slab bound from the fine one

If every kept fibre has at least `s0` fine tubes and the coarse tubes of the kept fibres contain
their fine tubes, then a coarse tube inside a slab carries `≥ s0` fine tubes inside the slab, and
fibres are disjoint; so the fine slab bound `F d l n` gives the coarse one with constant `l n / s0`.
`cover_restrict'` is `cover_restrict` with the coarse slab bound supplied directly.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open MeasureTheory

theorem coarseF_of_fine {d l ρ' s0 : ℝ} {n N : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} (A : Finset (Fin N))
    (hF : F d l n x v) (hl : 0 ≤ l) (hs0 : 0 < s0)
    (hcont : ∀ i ∈ S, f i ∈ A → T d (x i) (v i) ⊆ T ρ' (y (f i)) (w (f i)))
    (hmin : ∀ k ∈ A, s0 ≤ q n {i | i ∈ S ∧ f i = k}) :
    ∀ u t r, ‖u‖ = 1 → 0 < r →
      O (q N {k | k ∈ A ∧ T ρ' (y k) (w k) ⊆ I ∩ Q u t r}) ≤
        O (l * n / s0) * μ (I ∩ Q u t r) := by
  classical
  intro u t r hu hr
  set D := I ∩ Q u t r with hD
  let K : Finset (Fin N) := A.filter (fun k => T ρ' (y k) (w k) ⊆ D)
  have hK : q N {k | k ∈ A ∧ T ρ' (y k) (w k) ⊆ D} = (K.card : ℝ) := by
    show ((Set.ncard _ : ℕ) : ℝ) = _
    congr 1
    rw [← Set.ncard_coe_finset K]
    congr 1
    ext k
    simp [K]
  -- fibres over K, as a finset of fine tubes
  let FS : Finset (Fin n) := S.filter (fun i => f i ∈ K)
  have hfib : (K.card : ℝ) * s0 ≤ (FS.card : ℝ) := by
    have hsum : (FS.card : ℝ) = ∑ k ∈ K, ((S.filter (fun i => f i = k)).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (s := FS) (t := K) (f := f)
        (fun i hi => (Finset.mem_filter.mp hi).2)
      rw [this, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      congr 2
      ext i
      simp only [FS, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hiS, -⟩, hik⟩; exact ⟨hiS, hik⟩
      · rintro ⟨hiS, hik⟩; exact ⟨⟨hiS, hik ▸ hk⟩, hik⟩
    rw [hsum, mul_comm]
    calc s0 * (K.card : ℝ) = ∑ _k ∈ K, s0 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ k ∈ K, ((S.filter (fun i => f i = k)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkA : k ∈ A := (Finset.mem_filter.mp hk).1
          have h1 := hmin k hkA
          have h2 : q n {i | i ∈ S ∧ f i = k} = ((S.filter (fun i => f i = k)).card : ℝ) := by
            show ((Set.ncard _ : ℕ) : ℝ) = _
            congr 1
            rw [← Set.ncard_coe_finset]
            congr 1
            ext i
            simp
          linarith
  have hFS : (FS.card : ℝ) ≤ q n {i | T d (x i) (v i) ⊆ D} := by
    have hsub : (↑FS : Set (Fin n)) ⊆ {i | T d (x i) (v i) ⊆ D} := by
      intro i hi
      have hi' := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
      have hkK := Finset.mem_filter.mp hi'.2
      exact (hcont i hi'.1 hkK.1).trans hkK.2
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at h1
    show (FS.card : ℝ) ≤ ((Set.ncard _ : ℕ) : ℝ)
    exact_mod_cast h1
  have hfine := hF u t r hu hr
  have hcnt : (K.card : ℝ) ≤ q n {i | T d (x i) (v i) ⊆ D} / s0 := by
    rw [le_div_iff₀ hs0]; linarith
  rw [hK]
  calc O (K.card : ℝ) ≤ O (q n {i | T d (x i) (v i) ⊆ D} / s0) := ENNReal.ofReal_le_ofReal hcnt
    _ = O (q n {i | T d (x i) (v i) ⊆ D}) * O (s0⁻¹) := by
        have hq0 : 0 ≤ q n {i | T d (x i) (v i) ⊆ D} := Nat.cast_nonneg _
        rw [div_eq_mul_inv]
        exact ENNReal.ofReal_mul hq0
    _ ≤ (O (l * n) * μ D) * O (s0⁻¹) := mul_le_mul_left hfine _
    _ = O (l * n / s0) * μ D := by
        rw [mul_right_comm]
        congr 1
        rw [div_eq_mul_inv]
        exact (ENNReal.ofReal_mul (by positivity)).symm

/-- `cover_restrict` with the coarse slab bound supplied directly. -/
theorem cover_restrict' {d h h' ρ ρ' : ℝ} {n N : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h') (hρρ' : ρ ≤ ρ')
    (hC : C d h n x v Y S Z ρ N y w f True)
    (A : Finset (Fin N)) (hA : A.Nonempty) (Z' : Fin n → Set V)
    (hZ' : ∀ i, M (Z' i) ∧ Z' i ⊆ Z i)
    (hmass : O (d ^ h') * ∑ i, μ (Y i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ A), μ (Z' i))
    (hFA : ∀ u t r, ‖u‖ = 1 → 0 < r →
      O (q N {k | k ∈ A ∧ T ρ' (y k) (w k) ⊆ I ∩ Q u t r}) ≤ O (d ^ (-h') * A.card) * μ (I ∩ Q u t r))
    (hX : ∀ k ∈ A, ∀ k' ∈ A, k ≠ k' →
      μ (T ρ' (y k) (w k) ∩ T ρ' (y k') (w k')) ≤ 1/2 * μ (T ρ' (y k) (w k)))
    (hmult : ∀ i ∈ S, f i ∈ A →
      q N {k | k ∈ A ∧ T d (x i) (v i) ⊆ T ρ' (y k) (w k)} ≤ d ^ (-h')) :
    C d h' n x v Y (S.filter (fun i => f i ∈ A)) (fun i => if f i ∈ A then Z' i else ∅) ρ'
      A.card (fun k => y (rIdx A k)) (fun k => w (rIdx A k)) (rFib A hA f) True := by
  obtain ⟨hp, hi⟩ := rpow_err_le hd hd1 hh
  obtain ⟨hz, hm, hw, ht, hf, hb, hbal, hx, hov⟩ := hC
  refine ⟨?_, ?_, fun k => hw _, ?_, ?_, trivial, ?_, ?_, ?_⟩
  · intro i
    beta_reduce
    by_cases hiA : f i ∈ A
    · rw [if_pos hiA]
      refine ⟨(hZ' i).1, (hZ' i).2.trans (hz i).2.1, fun hiS => ?_⟩
      have : i ∉ S := fun h => hiS (Finset.mem_filter.mpr ⟨h, hiA⟩)
      exact Set.subset_eq_empty (hZ' i).2 ((hz i).2.2 this)
    · rw [if_neg hiA]
      exact ⟨MeasurableSet.empty, Set.empty_subset _, fun _ => rfl⟩
  · refine hmass.trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro i hi
    simp [(Finset.mem_filter.mp hi).2]
  · intro i hi
    obtain ⟨hiS, hiA⟩ := Finset.mem_filter.mp hi
    show T d (x i) (v i) ⊆ T ρ' (y (rIdx A (rFib A hA f i))) (w (rIdx A (rFib A hA f i)))
    rw [rIdx_rFib A hA f hiA]
    exact (ht i hiS).trans (T_mono_radius hρρ' _ _)
  · intro u t r hu hr
    rw [q_rIdx A (fun k => T ρ' (y k) (w k) ⊆ I ∩ Q u t r)]
    exact hFA u t r hu hr
  · intro k k'
    rw [fibre_restrict A hA k, fibre_restrict A hA k']
    exact (hbal _ _).trans (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _))
  · intro k k' hkk'
    exact hX _ (rIdx_mem A k) _ (rIdx_mem A k') (fun h => hkk' (rIdx_injective A h))
  · intro i hi
    obtain ⟨hiS, hiA⟩ := Finset.mem_filter.mp hi
    rw [q_rIdx A (fun k => T d (x i) (v i) ⊆ T ρ' (y k) (w k))]
    exact hmult i hiS hiA

end WangZahlLot.Obl.wz_coarse_grains_assembly
