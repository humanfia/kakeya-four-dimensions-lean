-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.RefineStep.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.SplitProposal

/-!
# WZ §9, Step 1: the refinement alternative

Given cover data `C` at error `δ^-h` and a sub-collection `U` of the `ρ`-tubes that obeys the
Katz–Tao convex count with error `δ^-ζ`, whose fibres carry a `δ^ζ` share of the shading mass and
which is not too small (`δ^-h N ≤ δ^-ζ #U`), the fibres over `U` with the `ρ`-tubes of `U`
(reindexed by `Fin #U`) carry o019's alternative (B) at error `ζ` (`Interfaces.Refined`).
The fibres are kept whole, so the below-slab counts are inherited from `C`; the Frostman slab
count of the new cover is inherited from `C` at the cost of the factor `N / #U`.
-/

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory

namespace Interfaces

/-- The number of elements of `U` with a property is the number of indices of `Fin #U` with it. -/
theorem ncard_reindex {N : ℕ} (U : Finset (Fin N)) (p : Fin N → Prop) :
    Set.ncard {k' : Fin U.card | p (U.equivFin.symm k').1} = Set.ncard {k | k ∈ U ∧ p k} := by
  classical
  refine Set.ncard_congr (fun k' _ => (U.equivFin.symm k').1) ?_ ?_ ?_
  · intro k' hk'
    exact ⟨(U.equivFin.symm k').2, hk'⟩
  · intro a b _ _ hab
    exact U.equivFin.symm.injective (Subtype.ext hab)
  · rintro k ⟨hkU, hpk⟩
    exact ⟨U.equivFin ⟨k, hkU⟩, by simpa using hpk, by simp⟩

theorem refined_of_subcover {ζ h δ ρ : ℝ} {n N : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    {S : Finset (Fin n)} {Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhζ : h ≤ ζ) (hC : C δ h n x v Y S Z ρ N y w f)
    (U : Finset (Fin N)) (hUne : U.Nonempty)
    (hmass : o (δ ^ ζ) * ∑ i, μ (Y i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ U), μ (Z i))
    (hKU : ∀ W, Convex ℝ W →
      o (q {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ o (δ ^ (-ζ)) * μ W)
    (hN : δ ^ (-h) * N ≤ δ ^ (-ζ) * U.card) :
    Refined ζ δ ρ n x v Y S Z := by
  classical
  obtain ⟨hZ, -, hw, hcover, hF, hB, -, -, -⟩ := hC
  obtain ⟨k₀, hk₀⟩ := hUne
  set e : Fin U.card ≃ {k // k ∈ U} := U.equivFin.symm with he
  let y' : Fin U.card → V := fun k' => y (e k').1
  let w' : Fin U.card → V := fun k' => w (e k').1
  let f' : Fin n → Fin U.card := fun i =>
    if hi : f i ∈ U then U.equivFin ⟨f i, hi⟩ else U.equivFin ⟨k₀, hk₀⟩
  have hf' : ∀ i, f i ∈ U → (e (f' i)).1 = f i := by
    intro i hi
    simp [f', hi, he]
  set S' := S.filter (fun i => f i ∈ U) with hS'
  have hfib : ∀ (k' : Fin U.card) (P : Fin n → Prop),
      {i | i ∈ S' ∧ f' i = k' ∧ P i} = {i | i ∈ S ∧ f i = (e k').1 ∧ P i} := by
    intro k' P
    ext i
    simp only [Set.mem_ofPred_eq, hS', Finset.mem_filter]
    constructor
    · rintro ⟨⟨hiS, hiU⟩, hik, hP⟩
      refine ⟨hiS, ?_, hP⟩
      rw [← hik, hf' i hiU]
    · rintro ⟨hiS, hik, hP⟩
      have hiU : f i ∈ U := hik ▸ (e k').2
      refine ⟨⟨hiS, hiU⟩, ?_, hP⟩
      apply e.injective
      apply Subtype.ext
      rw [hf' i hiU, hik]
  refine ⟨S', Z, U.card, y', w', f', Finset.filter_subset _ _, fun i => ⟨(hZ i).1, subset_rfl⟩,
    hmass, fun k' => hw _, ?_, ?_, ?_, ?_⟩
  · -- cover
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    show T δ (x i) (v i) ⊆ T ρ (y (e (f' i)).1) (w (e (f' i)).1)
    rw [hf' i hi'.2]
    exact hcover i hi'.1
  · -- Katz–Tao
    intro W hW
    have := ncard_reindex U (fun k => T ρ (y k) (w k) ⊆ W)
    simp only [q] at this ⊢
    rw [this]
    exact hKU W hW
  · -- Frostman slab count, inherited at the cost of `N / #U`
    intro u t r hu hr
    have hcount := ncard_reindex U (fun k => T ρ (y k) (w k) ⊆ I ∩ {p | |inner ℝ u p - t| ≤ r})
    simp only [q] at hcount ⊢
    rw [hcount]
    have hsub : Set.ncard {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ I ∩ {p | |inner ℝ u p - t| ≤ r}} ≤
        Set.ncard {k | T ρ (y k) (w k) ⊆ I ∩ {p | |inner ℝ u p - t| ≤ r}} :=
      Set.ncard_le_ncard (fun k hk => hk.2) (Set.toFinite _)
    calc o (Set.ncard {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ I ∩ {p | |inner ℝ u p - t| ≤ r}})
        ≤ o (Set.ncard {k | T ρ (y k) (w k) ⊆ I ∩ {p | |inner ℝ u p - t| ≤ r}}) :=
          ENNReal.ofReal_le_ofReal (by exact_mod_cast hsub)
      _ ≤ o (δ ^ (-h) * N) * μ (I ∩ {p | |inner ℝ u p - t| ≤ r}) := hF u t r hu hr
      _ ≤ o (δ ^ (-ζ) * U.card) * μ (I ∩ {p | |inner ℝ u p - t| ≤ r}) := by
          gcongr
          exact ENNReal.ofReal_le_ofReal hN
  · -- below-slab counts, fibre by fibre
    intro k' u t r hu hr
    have hle : δ ^ (-h) ≤ δ ^ (-ζ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have hBk := b_mono hB hle (e k').1 u t r hu hr
    have h1 := hfib k' (fun i => T δ (x i) (v i) ⊆
      T (2 * ρ) (y (e k').1 - (1 / 2 : ℝ) • w (e k').1) (2 • w (e k').1) ∩
        {p | |inner ℝ u p - t| ≤ r})
    have h2 := hfib k' (fun _ => True)
    simp only [and_true] at h2
    simp only [q] at hBk ⊢
    show o (Set.ncard {i | i ∈ S' ∧ f' i = k' ∧ T δ (x i) (v i) ⊆
        T (2 * ρ) (y (e k').1 - (1 / 2 : ℝ) • w (e k').1) (2 • w (e k').1) ∩
          {p | |inner ℝ u p - t| ≤ r}}) *
        μ (T (2 * ρ) (y (e k').1 - (1 / 2 : ℝ) • w (e k').1) (2 • w (e k').1)) ≤
      o (δ ^ (-ζ) * Set.ncard {i | i ∈ S' ∧ f' i = k'}) *
        μ (T (2 * ρ) (y (e k').1 - (1 / 2 : ℝ) • w (e k').1) (2 • w (e k').1) ∩
          {p | |inner ℝ u p - t| ≤ r})
    rw [h1, h2]
    exact hBk

end Interfaces

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
