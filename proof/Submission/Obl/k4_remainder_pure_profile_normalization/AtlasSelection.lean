/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/AtlasSelection.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.AtlasSequence
import Submission.Obl.k4_dyadic_crop_worlds.Assembly

/-! Selecting whole charts preserves the full assignments and terminal lists. -/

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open MeasureTheory

noncomputable def Atlas.selectIndex {p : Data} {k : ℕ} (a : Atlas p k)
    (S : Finset (Fin a.C)) (b : Fin S.card) : Fin a.C :=
  (S.equivFin.symm b).val

theorem Atlas.selectIndex_injective {p : Data} {k : ℕ} (a : Atlas p k)
    (S : Finset (Fin a.C)) : Function.Injective (a.selectIndex S) :=
  Submission.Obl.k4_dyadic_crop_worlds.injective_equivFin S

/-- Keep the original trajectory sets and the whole chosen incidence sets. -/
noncomputable def Atlas.select {p : Data} {k : ℕ} (a : Atlas p k)
    (S : Finset (Fin a.C)) : Atlas p k where
  κ := a.κ
  T := a.T
  C := S.card
  γ := a.γ ∘ a.selectIndex S
  j := a.j ∘ a.selectIndex S
  c := a.c ∘ a.selectIndex S
  u := a.u ∘ a.selectIndex S
  Q := a.Q ∘ a.selectIndex S
  R := a.R ∘ a.selectIndex S
  A := a.A ∘ a.selectIndex S
  F := a.F ∘ a.selectIndex S

noncomputable def Atlas.selectList {p : Data} {k : ℕ} (a : Atlas p k)
    (S : Finset (Fin a.C)) (lst : Fin (p.W k) → Observation → Finset (Fin a.C))
    (γ : Fin (p.W k)) (o : Observation) : Finset (Fin S.card) :=
  Finset.univ.filter fun b => a.selectIndex S b ∈ lst γ o

theorem Atlas.selectList_card_le {p : Data} {k : ℕ} (a : Atlas p k)
    (S : Finset (Fin a.C)) (lst : Fin (p.W k) → Observation → Finset (Fin a.C))
    (γ : Fin (p.W k)) (o : Observation) :
    (a.selectList S lst γ o).card ≤ (lst γ o).card := by
  apply Finset.card_le_card_of_injOn (a.selectIndex S)
  · intro b hb
    exact (Finset.mem_filter.mp hb).2
  · exact a.selectIndex_injective S |>.injOn

/-- The mass is the original sum over the selected labels. -/
theorem Atlas.select_mass {p : Data} {k : ℕ} (a : Atlas p k) (S : Finset (Fin a.C)) :
    (a.select S).mass = ∑ b ∈ S, ENNReal.ofReal (p.ω k (a.γ b)) *
      ((p.ν k (a.γ b)).prod volume) (a.F b) := by
  exact Submission.Obl.k4_dyadic_crop_worlds.sum_equivFin S
    (fun b => ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume) (a.F b))

/-- Chart selection costs only the explicit change in total mass and slack. -/
theorem Atlas.KnownAt.select {p : Data} {k M D : ℕ} {a : Atlas p k} {r κ : ℝ}
    (ha : a.KnownAt M D r) (S : Finset (Fin a.C))
    (hN : 1 ≤ p.N k) (hκ : 0 < a.κ) (hκ' : a.κ ≤ κ)
    (hB : ∀ γ, 0 ≤ p.B k γ) (hmass : ENNReal.ofReal κ⁻¹ ≤ (a.select S).mass) :
    ((a.select S).withSlack κ).KnownAt M D r := by
  rcases ha with ⟨lst, hC, hsep, hlist, hchart, _⟩
  refine ⟨a.selectList S lst, ?_, ?_, ?_, ?_, hmass⟩
  · exact (Nat.cast_le.mpr (S.card_le_univ.trans_eq (by simp))).trans hC
  · intro b b' hne hγ hj
    exact hsep _ _ (fun h => hne (a.selectIndex_injective S h)) hγ hj
  · intro γ o
    exact (Nat.cast_le.mpr (a.selectList_card_le S lst γ o)).trans ((hlist γ o).trans hκ')
  · intro b
    apply Submission.Obl.k4_quadratic_atlas_normalization.chart_mono
      hN le_rfl le_rfl hκ hκ' (hB _) (hchart (a.selectIndex S b))
    intro hex q hq
    change b ∈ a.selectList S lst (a.γ (a.selectIndex S b))
      (obs (p.B k (a.γ (a.selectIndex S b))) (δ (p.N k) p.L) q)
    unfold Atlas.selectList
    exact (@Finset.mem_filter (Fin S.card)
      (fun b' => a.selectIndex S b' ∈ lst (a.γ (a.selectIndex S b))
        (obs (p.B k (a.γ (a.selectIndex S b))) (δ (p.N k) p.L) q))
      (fun b' => Finset.decidableMem _ _) Finset.univ b).mpr
      ⟨Finset.mem_univ _, hex q hq⟩

end Submission.Obl.k4_remainder_pure_profile_normalization
