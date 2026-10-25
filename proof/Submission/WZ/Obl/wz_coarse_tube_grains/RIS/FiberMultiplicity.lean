-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FiberMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalMultiplicity

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Finset

/-- Enumerating a selected family preserves each predicate count exactly. -/
theorem ncard_comp_equivFin {n : ℕ} (P : Finset (Fin n)) (r : Fin n → Prop) :
    Set.ncard {j : Fin P.card | r ((P.equivFin.symm j : P) : Fin n)} =
      Set.ncard {i | i ∈ P ∧ r i} := by
  apply Set.ncard_congr (fun j _ => ((P.equivFin.symm j : P) : Fin n))
  · intro j hj
    exact ⟨(P.equivFin.symm j).property, hj⟩
  · intro j j' _ _ hjj'
    exact P.equivFin.symm.injective (Subtype.ext hjj')
  · intro i hi
    refine ⟨P.equivFin ⟨i, hi.1⟩, ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, Equiv.symm_apply_apply] using hi.2
    · simp only [Equiv.symm_apply_apply]

namespace Interfaces

/-- The local multiplicity theorem applied to a selected fiber, without changing
its original fine-tube indexing. The below-slab condition is stated on that fiber. -/
theorem fiber_multiplicity_of_local_rescaling {σ ω : ℝ} (hR : R σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 →
    ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (y w : V)
      (P : Finset (Fin n)), P.Nonempty → ‖w‖ = 1 →
    (∀ i ∈ P, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ T ρ y w ∧
      MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) →
    X δ n x v → o (δ ^ η * P.card * δ ^ 2) ≤ ∑ i ∈ P, μ (Y i) →
    K δ m n x v →
    (∀ (u : V) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      o (q {i | i ∈ P ∧ T δ (x i) (v i) ⊆
        T (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w) ∩ {p | |inner ℝ u p - t| ≤ r}}) *
          μ (T (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w)) ≤
      o (l * P.card) * μ (T (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w) ∩
        {p | |inner ℝ u p - t| ≤ r})) →
    ∀ M : ℝ, 0 ≤ M →
    (∀ p, (∃ i ∈ P, p ∈ Y i) → M ≤ q {i | i ∈ P ∧ p ∈ Y i}) →
    M ≤ C * δ ^ (-ε) * (δ / ρ) ^ (-ω) * m *
      (m ^ (-(3 / 2 : ℝ)) * l * (P.card * δ / ρ)) ^ σ := by
  intro ε hε
  obtain ⟨C, hC, η, hη, hlocal⟩ := multiplicity_of_local_rescaling hR ε hε
  refine ⟨C, hC, η, hη, ?_⟩
  intro δ ρ hδ hδ100 hδρ hρ1 m l hm hl n x v Y y w P hP hw hdata hX hdense hK hB M hM hmult
  let e : Fin P.card → Fin n := fun j => ((P.equivFin.symm j : P) : Fin n)
  have heP (j) : e j ∈ P := (P.equivFin.symm j).property
  have he : Function.Injective e := fun j j' hj => P.equivFin.symm.injective (Subtype.ext hj)
  have hK' : K δ m P.card (x ∘ e) (v ∘ e) := Katz.comp_injective hK he
  have hB' : B δ ρ l P.card 1 (x ∘ e) (v ∘ e) Finset.univ
      (fun _ => y) (fun _ => w) (fun _ => 0) := by
    intro k u t r hu hr
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    have hcount := ncard_comp_equivFin P (fun i => T δ (x i) (v i) ⊆
      T (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w) ∩ {p | |inner ℝ u p - t| ≤ r})
    simpa only [q, Function.comp_apply, Finset.mem_univ, true_and, and_true, hcount,
      Set.ofPred_true, Set.ncard_univ, Nat.card_fin, e] using hB u t r hu hr
  refine hlocal δ ρ hδ hδ100 hδρ hρ1 m l hm hl P.card (x ∘ e) (v ∘ e) (Y ∘ e)
    y w (Finset.card_pos.mpr hP) hw (fun j => hdata (e j) (heP j))
    (fun j j' hne => hX (e j) (e j') (he.ne hne)) ?_ hK' hB' M hM ?_
  · have hsum := sum_comp_equivFin P (fun i => μ (Y i))
    change (∑ j : Fin P.card, μ (Y (e j))) = _ at hsum
    simpa only [Function.comp_apply, hsum] using hdense
  · intro p hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    have hbound := ENNReal.ofReal_le_ofReal (hmult p ⟨e j, heP j, hj⟩)
    rw [multiplicity_eq_ncard]
    change o M ≤ (Set.ncard {j : Fin P.card | p ∈ Y ((P.equivFin.symm j : P) : Fin n)} : ENNReal)
    rw [ncard_comp_equivFin P (fun i => p ∈ Y i)]
    simpa only [o, q, ENNReal.ofReal_natCast] using hbound


/-- The below-slab hypothesis of an assigned cover is exactly the hypothesis
needed for its complete fiber after enumeration. -/
theorem below_slab_on_fiber {δ ρ l : ℝ} {n N : ℕ} {x v : Fin n → V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    (hB : B δ ρ l n N x v S y w f) (k : Fin N) :
    ∀ (u : V) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      o (q {i | i ∈ S.filter (fun i => f i = k) ∧ T δ (x i) (v i) ⊆
        T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩
          {p | |inner ℝ u p - t| ≤ r}}) *
          μ (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)) ≤
      o (l * (S.filter (fun i => f i = k)).card) *
        μ (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩
          {p | |inner ℝ u p - t| ≤ r}) := by
  classical
  intro u t r hu hr
  have hcard : Set.ncard {i | i ∈ S ∧ f i = k} = (S.filter (fun i => f i = k)).card := by
    rw [← Finset.coe_filter, Set.ncard_coe_finset]
  simpa only [q, mem_filter, and_assoc, hcard] using hB k u t r hu hr

end Interfaces
end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
