import Submission.Obl.k4_finite_width_path_realization.SplitInterfaces
import Submission.Obl.k4_finite_width_path_realization.Toolkit.Subatlases

namespace Submission.Obl.k4_finite_width_path_realization

open MeasureTheory Filter

structure Forest (p : Data) (k : ℕ) where
  κ : ℝ
  T : ℕ → ℕ
  C : ℕ
  lev : Fin C → ℕ
  par : Fin C → Fin C
  γ : Fin C → Fin (p.W k)
  j : Fin C → ℕ
  c : Fin C → Spatial
  u : Fin C → Spatial
  Q : Fin C → Frame
  R : Fin C → Test
  A : Fin C → Set Trajectory
  F : Fin C → Set Incidence
  width : Fin C → ℝ
  lst : ℕ → Fin (p.W k) → Observation → Finset (Fin C)

noncomputable def Forest.mass {p : Data} {k : ℕ} (a : Forest p k) (b : Fin a.C) : ENNReal :=
  ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume) (a.F b)

noncomputable def Forest.layerMass {p : Data} {k : ℕ} (a : Forest p k) (i : ℕ) : ENNReal :=
  ∑ b, if a.lev b = i then a.mass b else 0

noncomputable def Forest.Core {p : Data} {k : ℕ} (a : Forest p k)
    (M D m : ℕ) (r : ℕ → ℝ) : Prop :=
  CoreExpanded p.N p.K p.W p.ω p.ν p.E p.B p.f M D k m r a.T a.κ a.C
    a.lev a.par a.γ a.j a.c a.u a.Q a.R a.A a.F

noncomputable def Forest.Prepared {p : Data} {k : ℕ} (a : Forest p k) (r : ℕ → ℝ) : Prop :=
  (∀ i γ o, ((a.lst i γ o).card : ℝ) ≤ a.κ) ∧
  (∀ b, p.ν k (a.γ b) (a.A b) ≤ ENNReal.ofReal
      (a.κ * p.N k ^ (-p.f (r (a.lev b))) * |Matrix.det (a.Q b)|) ∧
    ∀ x ∈ a.F b, b ∈ a.lst (a.lev b) (a.γ b)
      (obs (p.B k (a.γ b)) (δ (p.N k) (r (a.lev b))) x))

noncomputable def Forest.Budget {p : Data} {k : ℕ} (a : Forest p k) : Prop :=
  (∀ b, a.mass b ≠ ⊤) ∧
  ∀ z, (∑ b, if 0 < a.lev b ∧ a.par b = z then a.mass b else 0) ≤ a.mass z

noncomputable def Forest.LowerWidths {p : Data} {k : ℕ} (a : Forest p k)
    (M : ℕ) (r : ℕ → ℝ) (w q : ℝ) : Prop :=
  ∀ b, |a.width b| ≤ (M : ℝ) ∧
    p.N k ^ (-a.width b) = |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T (a.lev b) ∧
    (a.lev b = 0 → w * r 0 - q ≤ a.width b) ∧
    (0 < a.lev b → a.width (a.par b) + w * (r (a.lev b) - r (a.lev (a.par b))) - q ≤ a.width b)

noncomputable def Forest.pullList {p : Data} {k : ℕ} (a : Forest p k)
    {C' : ℕ} (e : Fin C' ↪ Fin a.C) (i : ℕ) (γ : Fin (p.W k)) (o : Observation) :
    Finset (Fin C') := by
  classical
  exact Finset.univ.filter (fun b => e b ∈ a.lst i γ o)

theorem Forest.pullList_card {p : Data} {k : ℕ} (a : Forest p k)
    {C' : ℕ} (e : Fin C' ↪ Fin a.C) (i : ℕ) (γ : Fin (p.W k)) (o : Observation) :
    (a.pullList e i γ o).card ≤ (a.lst i γ o).card := by
  classical
  apply Finset.card_le_card_of_injOn e
  · intro b hb
    exact (Finset.mem_filter.mp hb).2
  · exact fun _ _ _ _ h => e.injective h

noncomputable def Forest.reindex {p : Data} {k : ℕ} (a : Forest p k)
    {C' : ℕ} (e : Fin C' ↪ Fin a.C) (par' : Fin C' → Fin C') (κ' : ℝ) : Forest p k where
  κ := κ'
  T := a.T
  C := C'
  lev := a.lev ∘ e
  par := par'
  γ := a.γ ∘ e
  j := a.j ∘ e
  c := a.c ∘ e
  u := a.u ∘ e
  Q := a.Q ∘ e
  R := a.R ∘ e
  A := a.A ∘ e
  F := a.F ∘ e
  width := a.width ∘ e
  lst := a.pullList e

theorem Chart.floor_mono {p : Data} (hp : p.Valid) {k M D T : ℕ}
    {κ κ' j r : ℝ} {γ : Fin (p.W k)} {c u : Spatial} {Q : Frame} {R : Test}
    {A : Set Trajectory} {F : Set Incidence}
    (hκ : 1 ≤ κ) (hκ' : κ ≤ κ')
    (hc : Chart (p.N k) M D κ T j r (p.B k γ) (p.E k γ) c u Q R A F
      (ENNReal.ofReal (p.N k ^ (-p.f r) * |Matrix.det Q| / ((2 : ℝ) ^ T * κ)) ≤
        ((p.ν k γ).prod volume) F)) :
    Chart (p.N k) M D κ' T j r (p.B k γ) (p.E k γ) c u Q R A F
      (ENNReal.ofReal (p.N k ^ (-p.f r) * |Matrix.det Q| / ((2 : ℝ) ^ T * κ')) ≤
        ((p.ν k γ).prod volume) F) := by
  apply Chart.mono (by linarith [hp.N_ge k]) le_rfl le_rfl
    (lt_of_lt_of_le zero_lt_one hκ) hκ' (hp.B_pos k γ).le _ hc
  intro hf
  apply le_trans (ENNReal.ofReal_le_ofReal _) hf
  apply div_le_div_of_nonneg_left
    (mul_nonneg (Real.rpow_nonneg (by linarith [hp.N_ge k]) _) (abs_nonneg _))
    (mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one hκ))
  exact mul_le_mul_of_nonneg_left hκ' (by positivity)

theorem Forest.Core.mono {p : Data} (hp : p.Valid) {k M D m : ℕ}
    {a : Forest p k} {r : ℕ → ℝ} (ha : a.Core M D m r) {κ' : ℝ}
    (hκ' : a.κ ≤ κ') :
    ({a with κ := κ'} : Forest p k).Core M D m r := by
  rcases ha with ⟨hκ, hK, hC, hmass, hdis, hc⟩
  refine ⟨hκ.trans hκ', hK.trans hκ', hC, ?_, hdis, fun b => ?_⟩
  · intro i hi
    exact (ENNReal.ofReal_le_ofReal (by
      simpa only [one_div] using one_div_le_one_div_of_le
        (lt_of_lt_of_le zero_lt_one hκ) hκ')).trans (hmass i hi)
  · exact ⟨(hc b).1, (hc b).2.1, Chart.floor_mono hp hκ hκ' (hc b).2.2.1,
      (hc b).2.2.2⟩

theorem Forest.Core.reindex {p : Data} (hp : p.Valid) {k M D m : ℕ}
    {a : Forest p k} {r : ℕ → ℝ} (ha : a.Core M D m r) {C' : ℕ}
    (e : Fin C' ↪ Fin a.C) (par' : Fin C' → Fin C') {κ' : ℝ}
    (hC : C' ≤ a.C) (hκ : a.κ ≤ κ')
    (hpar : ∀ b, 0 < a.lev (e b) → e (par' b) = a.par (e b))
    (hmass : ∀ i, i < m → ENNReal.ofReal κ'⁻¹ ≤
      ∑ b, if a.lev (e b) = i then a.mass (e b) else 0) :
    (a.reindex e par' κ').Core M D m r := by
  rcases ha with ⟨hκ1, hK, hbound, _, hdis, hc⟩
  refine ⟨hκ1.trans hκ, hK.trans hκ, ?_, hmass, ?_, fun b => ?_⟩
  · exact le_trans (by exact_mod_cast hC) hbound
  · intro b b' hne hl hγ hj
    exact hdis (e b) (e b') (fun h => hne (e.injective h)) hl hγ hj
  · refine ⟨(hc (e b)).1, (hc (e b)).2.1,
      Chart.floor_mono hp hκ1 hκ (hc (e b)).2.2.1, ?_⟩
    intro hb
    have hx := (hc (e b)).2.2.2 hb
    dsimp only [Forest.reindex, Function.comp_apply]
    simp only [hpar b hb]
    exact hx

theorem Forest.Prepared.reindex {p : Data} (hp : p.Valid) {k : ℕ}
    {a : Forest p k} {r : ℕ → ℝ} (ha : a.Prepared r) {C' : ℕ}
    (e : Fin C' ↪ Fin a.C) (par' : Fin C' → Fin C') {κ' : ℝ}
    (hκ : a.κ ≤ κ') : (a.reindex e par' κ').Prepared r := by
  classical
  unfold Forest.Prepared
  dsimp only [Forest.reindex, Function.comp_apply]
  refine ⟨fun i γ o => le_trans (by exact_mod_cast a.pullList_card e i γ o)
    ((ha.1 i γ o).trans hκ), fun b => ⟨?_, ?_⟩⟩
  · exact ((ha.2 (e b)).1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ
        (Real.rpow_nonneg (by linarith [hp.N_ge k]) _)) (abs_nonneg _)))
  · intro x hx
    change b ∈ Finset.univ.filter (fun z => e z ∈ a.lst (a.lev (e b)) (a.γ (e b))
      (obs (p.B k (a.γ (e b))) (δ (p.N k) (r (a.lev (e b)))) x))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (ha.2 (e b)).2 x hx

end Submission.Obl.k4_finite_width_path_realization
