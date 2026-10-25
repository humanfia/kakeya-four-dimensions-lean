-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FiberRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.SplitProposal

/-!
# Restricting a cover by keeping whole fibers

A selection of coarse tubes must be accompanied by restriction of the fine family.
The below-slab count then has no loss, while the above-slab constant acquires the
ratio of the old and new numbers of coarse tubes. The mass bound is kept explicit.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory Set

noncomputable section

/-- Convex counting survives an injective restriction of the coarse family. -/
theorem k_comp_injective {d m : ℝ} {N M : ℕ} {y w : Fin N → V}
    (hK : K d m N y w) {e : Fin M → Fin N} (he : Function.Injective e) :
    K d m M (y ∘ e) (w ∘ e) := by
  intro W hW
  apply le_trans _ (hK W hW)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg d)
  apply Nat.cast_le.mpr
  exact Set.ncard_le_ncard_of_injOn e (fun i hi => hi) he.injOn (Set.toFinite _)

/-- Above-slab counting on a subfamily, with the precise change of normalization. -/
theorem f_comp_injective {d l : ℝ} {N M : ℕ} {y w : Fin N → V}
    (hF : F d l N y w) (hM : 0 < M) {e : Fin M → Fin N}
    (he : Function.Injective e) : F d (l * N / M) M (y ∘ e) (w ∘ e) := by
  intro u t r hu hr
  apply le_trans _ ((hF u t r hu hr).trans_eq _)
  · apply ENNReal.ofReal_le_ofReal
    apply Nat.cast_le.mpr
    exact Set.ncard_le_ncard_of_injOn e (fun i hi => hi) he.injOn (Set.toFinite _)
  · congr 2
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp

/-- A restricted assignment whose nonempty fibers are exactly selected original fibers. -/
theorem exists_restricted_assignment {n N M : ℕ} (S : Finset (Fin n))
    (f : Fin n → Fin N) (e : Fin M → Fin N) (he : Function.Injective e)
    (hM : 0 < M) :
    ∃ (S' : Finset (Fin n)) (g : Fin n → Fin M), S' ⊆ S ∧
      (∀ i, i ∈ S' ↔ i ∈ S ∧ f i ∈ Set.range e) ∧
      (∀ i ∈ S', e (g i) = f i) ∧
      (∀ k i, (i ∈ S' ∧ g i = k) ↔ (i ∈ S ∧ f i = e k)) := by
  classical
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  let g : Fin n → Fin M := Function.invFun e ∘ f
  let S' := S.filter fun i => f i ∈ Set.range e
  have hmem (i) : i ∈ S' ↔ i ∈ S ∧ f i ∈ Set.range e := Finset.mem_filter
  have hg (i) (hi : i ∈ S') : e (g i) = f i :=
    Function.invFun_eq (hmem i |>.mp hi).2
  refine ⟨S', g, Finset.filter_subset _ _, hmem, hg, ?_⟩
  intro k i
  constructor
  · rintro ⟨hi, hik⟩
    exact ⟨(hmem i |>.mp hi).1, (hg i hi).symm.trans (congrArg e hik)⟩
  · rintro ⟨hi, hfi⟩
    have hi' : i ∈ S' := (hmem i).mpr ⟨hi, ⟨k, hfi.symm⟩⟩
    exact ⟨hi', he ((hg i hi').trans hfi)⟩

/-- Keeping complete fibers preserves the normalized below-slab inequality exactly. -/
theorem b_restrict_fibers {d ρ l : ℝ} {n N M : ℕ} {x v : Fin n → V}
    {S S' : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    {e : Fin M → Fin N} {g : Fin n → Fin M}
    (hfib : ∀ k i, (i ∈ S' ∧ g i = k) ↔ (i ∈ S ∧ f i = e k))
    (hB : B d ρ l n N x v S y w f) :
    B d ρ l n M x v S' (y ∘ e) (w ∘ e) g := by
  intro k u t r hu hr
  have h1 : {i | i ∈ S' ∧ g i = k} = {i | i ∈ S ∧ f i = e k} :=
    Set.ext (hfib k)
  have h2 : {i | i ∈ S' ∧ g i = k ∧ T d (x i) (v i) ⊆
        T (2 * ρ) (y (e k) - (1 / 2 : ℝ) • w (e k)) (2 • w (e k)) ∩
          {p | |inner ℝ u p - t| ≤ r}} =
      {i | i ∈ S ∧ f i = e k ∧ T d (x i) (v i) ⊆
        T (2 * ρ) (y (e k) - (1 / 2 : ℝ) • w (e k)) (2 • w (e k)) ∩
          {p | |inner ℝ u p - t| ≤ r}} := by
    ext i
    simp only [Set.mem_ofPred_eq, ← and_assoc, hfib k i]
  simpa only [Function.comp_apply, h1, h2] using hB (e k) u t r hu hr

/-- A coarse subfamily with the required convex count gives the refined alternative
once its retained mass and the above-slab normalization loss are controlled. -/
theorem refined_of_selected_cover {ζ δ ρ h : ℝ} {n N M : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hC : C δ h n x v Y S Z ρ N y w f) (hM : 0 < M)
    (e : Fin M → Fin N) (he : Function.Injective e)
    (hK : K ρ (δ ^ (-ζ)) M (y ∘ e) (w ∘ e))
    (hF : δ ^ (-h) * N / M ≤ δ ^ (-ζ)) (hB : δ ^ (-h) ≤ δ ^ (-ζ))
    (hmass : o (δ ^ ζ) * ∑ i, μ (Y i) ≤
      ∑ i ∈ S with f i ∈ Set.range e, μ (Z i)) :
    Refined ζ δ ρ n x v Y S Z := by
  classical
  obtain ⟨S', g, hsub, hmem, hg, hfib⟩ := exists_restricted_assignment S f e he hM
  let Z' : Fin n → Set V := fun i => if i ∈ S' then Z i else ∅
  have hZ' (i) : MeasurableSet (Z' i) ∧ Z' i ⊆ Z i := by
    by_cases hi : i ∈ S'
    · simpa [Z', hi] using (show MeasurableSet (Z i) ∧ Z i ⊆ Z i from ⟨(hC.1 i).1, Subset.rfl⟩)
    · simp [Z', hi]
  refine ⟨S', Z', M, y ∘ e, w ∘ e, g, hsub, hZ', ?_, ?_, ?_, hK, ?_, ?_⟩
  · have hS' : S' = S.filter (fun i => f i ∈ Set.range e) := by
      ext i
      simp only [Finset.mem_filter, hmem]
    have hsum : (∑ i ∈ S', μ (Z' i)) = ∑ i ∈ S', μ (Z i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Z', ite_eq_left hi]
    rw [hsum, hS']
    exact hmass
  · exact fun k => hC.2.2.1 (e k)
  · intro i hi
    simpa only [Function.comp_apply, hg i hi] using hC.2.2.2.1 i (hsub hi)
  · exact f_mono (f_comp_injective hC.2.2.2.2.1 hM he) hF
  · exact b_mono (b_restrict_fibers hfib hC.2.2.2.2.2.1) hB

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
