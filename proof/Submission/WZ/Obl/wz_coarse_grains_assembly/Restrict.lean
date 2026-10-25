-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.Restrict.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Mono

/-!
# Restricting a cover to a set of fibres

Given a cover `(S, Z, N, y, w, f)` and a nonempty `A : Finset (Fin N)`, keep the fibres in `A`,
reindexed by `Fin A.card`.  Every clause of `C` transfers, with the coarse radius possibly enlarged
from `ρ` to `ρ' ≥ ρ`, except the two that genuinely depend on `A` at the new radius
(pairwise overlap and the number of coarse tubes containing a fine tube), which are hypotheses;
the coarse slab bound transfers when `A` keeps a `d^(h'-h)` share of the fibres.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open MeasureTheory

variable {n N : ℕ}

/-- The reindexing of `A` by `Fin A.card`. -/
def rIdx (A : Finset (Fin N)) (k : Fin A.card) : Fin N := (A.equivFin.symm k).1

theorem rIdx_mem (A : Finset (Fin N)) (k : Fin A.card) : rIdx A k ∈ A := (A.equivFin.symm k).2

theorem rIdx_injective (A : Finset (Fin N)) : Function.Injective (rIdx A) := by
  intro k k' h
  exact A.equivFin.symm.injective (Subtype.ext h)

/-- The new fibre map: fibres in `A` are renumbered, the others sent to an arbitrary index. -/
def rFib (A : Finset (Fin N)) (hA : A.Nonempty) (f : Fin n → Fin N) (i : Fin n) : Fin A.card :=
  if h : f i ∈ A then A.equivFin ⟨f i, h⟩ else ⟨0, hA.card_pos⟩

theorem rIdx_rFib (A : Finset (Fin N)) (hA : A.Nonempty) (f : Fin n → Fin N) {i : Fin n}
    (hi : f i ∈ A) : rIdx A (rFib A hA f i) = f i := by
  simp [rIdx, rFib, hi]

theorem rFib_eq_iff (A : Finset (Fin N)) (hA : A.Nonempty) (f : Fin n → Fin N) {i : Fin n}
    (hi : f i ∈ A) (k : Fin A.card) : rFib A hA f i = k ↔ f i = rIdx A k := by
  constructor
  · rintro rfl; exact (rIdx_rFib A hA f hi).symm
  · intro h
    apply rIdx_injective A
    rw [rIdx_rFib A hA f hi, h]

/-- Counting a predicate over the reindexed fibres. -/
theorem q_rIdx (A : Finset (Fin N)) (P : Fin N → Prop) :
    q A.card {k | P (rIdx A k)} = q N {k | k ∈ A ∧ P k} := by
  show ((Set.ncard _ : ℕ) : ℝ) = ((Set.ncard _ : ℕ) : ℝ)
  congr 1
  have himg : rIdx A '' {k | P (rIdx A k)} = {k | k ∈ A ∧ P k} := by
    ext k
    constructor
    · rintro ⟨k', hk', rfl⟩; exact ⟨rIdx_mem A k', hk'⟩
    · rintro ⟨hkA, hk⟩
      refine ⟨A.equivFin ⟨k, hkA⟩, ?_, ?_⟩
      · show P (rIdx A _); simpa [rIdx] using hk
      · simp [rIdx]
  rw [← himg, Set.ncard_image_of_injective _ (rIdx_injective A)]

theorem q_le_of_subset {m : ℕ} {s t : Set (Fin m)} (h : s ⊆ t) : q m s ≤ q m t := by
  show ((Set.ncard s : ℕ) : ℝ) ≤ ((Set.ncard t : ℕ) : ℝ)
  exact_mod_cast Set.ncard_le_ncard h (Set.toFinite _)

theorem T_mono_radius {r r' : ℝ} (hr : r ≤ r') (p u : V) : T r p u ⊆ T r' p u :=
  Metric.thickening_mono hr _

/-- The restricted cover. -/
theorem cover_restrict {d h h' ρ ρ' : ℝ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h') (hρρ' : ρ ≤ ρ')
    (hC : C d h n x v Y S Z ρ N y w f True)
    (A : Finset (Fin N)) (hA : A.Nonempty)
    (hmass : O (d ^ h') * ∑ i, μ (Y i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ A), μ (Z i))
    (hcount : d ^ (-h) * N ≤ d ^ (-h') * A.card)
    (hX : ∀ k ∈ A, ∀ k' ∈ A, k ≠ k' →
      μ (T ρ' (y k) (w k) ∩ T ρ' (y k') (w k')) ≤ 1/2 * μ (T ρ' (y k) (w k)))
    (hmult : ∀ i ∈ S, f i ∈ A →
      q N {k | k ∈ A ∧ T d (x i) (v i) ⊆ T ρ' (y k) (w k)} ≤ d ^ (-h')) :
    C d h' n x v Y (S.filter (fun i => f i ∈ A)) (fun i => if f i ∈ A then Z i else ∅) ρ'
      A.card (fun k => y (rIdx A k)) (fun k => w (rIdx A k)) (rFib A hA f) True := by
  obtain ⟨hp, hi⟩ := rpow_err_le hd hd1 hh
  obtain ⟨hz, hm, hw, ht, hf, hb, hbal, hx, hov⟩ := hC
  refine ⟨?_, ?_, fun k => hw _, ?_, ?_, trivial, ?_, ?_, ?_⟩
  · intro i
    beta_reduce
    by_cases hiA : f i ∈ A
    · rw [if_pos hiA]
      refine ⟨(hz i).1, (hz i).2.1, fun hiS => ?_⟩
      have : i ∉ S := fun h => hiS (Finset.mem_filter.mpr ⟨h, hiA⟩)
      exact (hz i).2.2 this
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
    have hsub : q A.card {k | T ρ' (y (rIdx A k)) (w (rIdx A k)) ⊆ I ∩ Q u t r} ≤
        q N {k | T ρ (y k) (w k) ⊆ I ∩ Q u t r} := by
      rw [q_rIdx A (fun k => T ρ' (y k) (w k) ⊆ I ∩ Q u t r)]
      exact q_le_of_subset (fun k hk => (T_mono_radius hρρ' _ _).trans hk.2)
    calc O (q A.card {k | T ρ' (y (rIdx A k)) (w (rIdx A k)) ⊆ I ∩ Q u t r})
        ≤ O (q N {k | T ρ (y k) (w k) ⊆ I ∩ Q u t r}) := ENNReal.ofReal_le_ofReal hsub
      _ ≤ O (d ^ (-h) * N) * μ (I ∩ Q u t r) := hf u t r hu hr
      _ ≤ O (d ^ (-h') * A.card) * μ (I ∩ Q u t r) :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hcount) _
  · intro k k'
    have hset : ∀ k'' : Fin A.card,
        {i | i ∈ S.filter (fun i => f i ∈ A) ∧ rFib A hA f i = k''} =
          {i | i ∈ S ∧ f i = rIdx A k''} := by
      intro k''
      ext i
      simp only [Set.mem_ofPred_eq, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hiS, hiA⟩, hik⟩
        exact ⟨hiS, (rFib_eq_iff A hA f hiA k'').1 hik⟩
      · rintro ⟨hiS, hik⟩
        have hiA : f i ∈ A := hik ▸ rIdx_mem A k''
        exact ⟨⟨hiS, hiA⟩, (rFib_eq_iff A hA f hiA k'').2 hik⟩
    rw [hset k, hset k']
    exact (hbal _ _).trans (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _))
  · intro k k' hkk'
    exact hX _ (rIdx_mem A k) _ (rIdx_mem A k') (fun h => hkk' (rIdx_injective A h))
  · intro i hi
    obtain ⟨hiS, hiA⟩ := Finset.mem_filter.mp hi
    rw [q_rIdx A (fun k => T d (x i) (v i) ⊆ T ρ' (y k) (w k))]
    exact hmult i hiS hiA

/-- Broadness of the kept fibres. -/
theorem broad_restrict {ω ζ d h ρ : ℝ} {v : Fin n → V} {Z : Fin n → Set V}
    {S : Finset (Fin n)} {f : Fin n → Fin N} (A : Finset (Fin N)) (hA : A.Nonempty)
    (hb : Broad ω ζ d h ρ n N v S Z f) :
    Broad ω ζ d h ρ n A.card v (S.filter (fun i => f i ∈ A))
      (fun i => if f i ∈ A then Z i else ∅) (rFib A hA f) := by
  intro k p u r hu hdr hrρ
  have hset : ∀ P : Fin n → Prop,
      {i | i ∈ S.filter (fun i => f i ∈ A) ∧ rFib A hA f i = k ∧
          p ∈ (if f i ∈ A then Z i else ∅) ∧ P i} =
        {i | i ∈ S ∧ f i = rIdx A k ∧ p ∈ Z i ∧ P i} := by
    intro P
    ext i
    simp only [Set.mem_ofPred_eq, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hiS, hiA⟩, hik, hp, hP⟩
      rw [if_pos hiA] at hp
      exact ⟨hiS, (rFib_eq_iff A hA f hiA k).1 hik, hp, hP⟩
    · rintro ⟨hiS, hik, hp, hP⟩
      have hiA : f i ∈ A := hik ▸ rIdx_mem A k
      exact ⟨⟨hiS, hiA⟩, (rFib_eq_iff A hA f hiA k).2 hik, by simp [hiA, hp], hP⟩
  have h1 := hset (fun i => min ‖v i - u‖ ‖v i + u‖ ≤ r)
  have h2 := hset (fun _ => True)
  simp only [and_true] at h2
  rw [h1, h2]
  exact hb (rIdx A k) p u r hu hdr hrρ

/-- Fibre counts of the kept fibres. -/
theorem fibre_restrict {S : Finset (Fin n)} {f : Fin n → Fin N} (A : Finset (Fin N))
    (hA : A.Nonempty) (k : Fin A.card) :
    {i | i ∈ S.filter (fun i => f i ∈ A) ∧ rFib A hA f i = k} = {i | i ∈ S ∧ f i = rIdx A k} := by
  ext i
  simp only [Set.mem_ofPred_eq, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hiS, hiA⟩, hik⟩
    exact ⟨hiS, (rFib_eq_iff A hA f hiA k).1 hik⟩
  · rintro ⟨hiS, hik⟩
    have hiA : f i ∈ A := hik ▸ rIdx_mem A k
    exact ⟨⟨hiS, hiA⟩, (rFib_eq_iff A hA f hiA k).2 hik⟩

end WangZahlLot.Obl.wz_coarse_grains_assembly
