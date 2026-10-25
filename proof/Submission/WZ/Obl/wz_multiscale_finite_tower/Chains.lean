-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Chains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Tower
import Submission.WZ.Obl.wz_multiscale_finite_tower.Counts

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- A finite composable chain, with its number of edges recorded. -/
inductive Chain {X : Type*} (R : X → X → Prop) : X → X → ℕ → Prop where
  | refl (x : X) : Chain R x x 0
  | step {x y z : X} {k : ℕ} : R x y → Chain R y z k → Chain R x z (k + 1)

theorem Chain.trans {X : Type*} {R : X → X → Prop} {x y z : X} {k l : ℕ}
    (h : Chain R x y k) (h' : Chain R y z l) : Chain R x z (k + l) := by
  induction h with
  | refl => simpa using h'
  | step hxy hyz ih =>
    simpa only [Nat.succ_add] using Chain.step hxy (ih h')

/-- Weakening an edge relation preserves the chain and its length. -/
theorem Chain.mono {X : Type*} {R S : X → X → Prop}
    (hRS : ∀ x y, R x y → S x y) {x y : X} {k : ℕ}
    (h : Chain R x y k) : Chain S x y k := by
  induction h with
  | refl x => exact Chain.refl x
  | step hxy hyz ih => exact Chain.step (hRS _ _ hxy) ih

/-- Replacing each old edge by one or two edges at most doubles the length. -/
theorem Chain.replace {X : Type*} {R S : X → X → Prop}
    (replace : ∀ x y, R x y → ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ∧ Chain S x y k)
    {x y : X} {k : ℕ} (h : Chain R x y k) :
    ∃ l : ℕ, k ≤ l ∧ l ≤ 2 * k ∧ Chain S x y l := by
  induction h with
  | refl x => exact ⟨0, le_rfl, by omega, Chain.refl x⟩
  | @step x y z k hxy hyz ih =>
    obtain ⟨l, hl1, hl2, hxy'⟩ := replace x y hxy
    obtain ⟨m, hm1, hm2, hyz'⟩ := ih
    exact ⟨l + m, by omega, by omega, hxy'.trans hyz'⟩

/-- Turn a chain into the natural-number indexing used by the frozen tower. -/
theorem Chain.exists_sequence {X : Type*} {R : X → X → Prop} {x y : X} {k : ℕ}
    (h : Chain R x y k) :
    ∃ s : ℕ → X, s 0 = x ∧ s k = y ∧ ∀ j, j < k → R (s j) (s (j + 1)) := by
  induction h with
  | refl x => exact ⟨fun _ => x, rfl, rfl, fun j hj => by omega⟩
  | @step x y z k hxy hyz ih =>
    obtain ⟨s, hs0, hsk, hs⟩ := ih
    let t : ℕ → X := fun j => match j with | 0 => x | j + 1 => s j
    refine ⟨t, rfl, hsk, ?_⟩
    intro j hj
    cases j with
    | zero => simpa only [t, hs0] using hxy
    | succ j => exact hs j (by omega)

/-- Consecutive edges of a sequence form a finite chain. -/
theorem Chain.of_sequence {X : Type*} {R : X → X → Prop} (s : ℕ → X) (J : ℕ) :
    (∀ j, j < J → R (s j) (s (j + 1))) → Chain R (s 0) (s J) J := by
  induction J with
  | zero => intro _; exact Chain.refl _
  | succ J ih =>
    intro hs
    have hprev := ih (fun j hj => hs j (by omega))
    exact hprev.trans (Chain.step (hs J (by omega)) (Chain.refl _))

/-- The finite-indexed variant avoids dependent transports at the last layer. -/
theorem Chain.of_fin_sequence {X : Type*} {R : X → X → Prop} (J : ℕ) :
    ∀ s : Fin (J + 1) → X,
      (∀ i : Fin J, R (s i.castSucc) (s i.succ)) →
      Chain R (s 0) (s (Fin.last J)) J := by
  induction J with
  | zero => intro s _; exact Chain.refl _
  | succ J ih =>
    intro s hs
    have hprev := ih (fun i => s i.castSucc) (fun i => hs i.castSucc)
    exact hprev.trans (Chain.step (hs (Fin.last J)) (Chain.refl _))

/-- A nonempty finite tube family at one scale. -/
structure Layer where
  radius : ℝ
  card : ℕ
  card_pos : 0 < card
  position : Fin card → Space
  direction : Fin card → Space
  unit : ∀ i, ‖direction i‖ = 1

/-- The local geometric and convex-count data between two consecutive layers. -/
def LocalEdge (θ L : ℝ) (p c : Layer) : Prop :=
  0 < c.radius ∧ c.radius < p.radius ∧ θ * p.radius ≤ c.radius ∧
    ∃ f : Fin c.card → Fin p.card,
      (∀ i, Tube c.radius (c.position i) (c.direction i) ⊆
        Tube p.radius (p.position (f i)) (p.direction (f i))) ∧
      ∀ k W, Convex ℝ W →
        ENNReal.ofReal ((Set.ncard {i | f i = k ∧
          Tube c.radius (c.position i) (c.direction i) ⊆ W} : ℝ) * c.radius ^ 2) ≤
            ENNReal.ofReal L * volume W

/-- Relaxing the two numerical bounds preserves an edge. -/
theorem LocalEdge.mono {θ θ' L L' : ℝ} {p c : Layer}
    (h : LocalEdge θ L p c) (hθ : θ' ≤ θ) (hL : L ≤ L') : LocalEdge θ' L' p c := by
  obtain ⟨hpos, hlt, hgap, f, hsub, hcount⟩ := h
  refine ⟨hpos, hlt, le_trans ?_ hgap, f, hsub, ?_⟩
  · exact mul_le_mul_of_nonneg_right hθ (hpos.trans hlt).le
  · intro k W hW
    exact (hcount k W hW).trans (by gcongr)

/-- Select a nonempty indexed subfamily of one layer. -/
def Layer.select (p : Layer) {m : ℕ} (hm : 0 < m) (u : Fin m → Fin p.card) : Layer where
  radius := p.radius
  card := m
  card_pos := hm
  position := p.position ∘ u
  direction := p.direction ∘ u
  unit i := p.unit (u i)

/-- A local edge survives restricting its children. -/
theorem LocalEdge.select_child {θ L : ℝ} {p c : Layer} (h : LocalEdge θ L p c)
    {m : ℕ} (hm : 0 < m) (u : Fin m → Fin c.card) (hu : Function.Injective u) :
    LocalEdge θ L p (c.select hm u) := by
  obtain ⟨hpos, hlt, hgap, f, hsub, hcount⟩ := h
  refine ⟨hpos, hlt, hgap, f ∘ u, fun i => hsub (u i), ?_⟩
  intro k W hW
  apply le_trans (ENNReal.ofReal_le_ofReal _) (hcount k W hW)
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (count_comp_le u hu (fun i => f i = k ∧
      Tube c.radius (c.position i) (c.direction i) ⊆ W))) (sq_nonneg c.radius)

/-- Restricting the last layer leaves all earlier layers and the length unchanged. -/
theorem Chain.restrict_bottom {θ L : ℝ} {p c : Layer} {J : ℕ}
    (h : Chain (LocalEdge θ L) p c J) (hJ : 1 ≤ J)
    {m : ℕ} (hm : 0 < m) (u : Fin m → Fin c.card) (hu : Function.Injective u) :
    Chain (LocalEdge θ L) p (c.select hm u) J := by
  induction h with
  | refl => omega
  | @step x y z k hxy hyz ih =>
    cases k with
    | zero =>
      cases hyz
      exact Chain.step (hxy.select_child hm u hu) (Chain.refl _)
    | succ k =>
      exact Chain.step hxy (ih (by omega) u hu)

/-- The list-like chain formulation entails exactly the requested local tower certificate. -/
theorem tower_of_chain {d L g : ℝ} {B J : ℕ} {p c : Layer}
    (hp : p.radius = 1) (hpN : p.card = 1) (hc : c.radius = d)
    (hJ : 1 ≤ J) (hJB : J ≤ B) (h : Chain (LocalEdge (d ^ g) L) p c J) :
    Tower false d L g B c.card c.position c.direction := by
  classical
  obtain ⟨s, hs0, hsJ, hs⟩ := h.exists_sequence
  let r : ℕ → ℝ := fun j => (s j).radius
  let N : ℕ → ℕ := fun j => (s j).card
  let y : ∀ j, Fin (N j) → Space := fun j => (s j).position
  let w : ∀ j, Fin (N j) → Space := fun j => (s j).direction
  let f : ∀ j, Fin (N (j + 1)) → Fin (N j) := fun j =>
    if hj : j < J then (hs j hj).2.2.2.choose else fun _ => ⟨0, (s j).card_pos⟩
  refine ⟨J, hJ, hJB, r, N, y, w, f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [r, hs0] using hp
  · simpa only [r, hsJ] using hc
  · simpa only [N, hs0] using hpN
  · cases hsJ
    exact ⟨Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩
  · intro j hj i
    exact (s j).unit i
  · intro j hj
    obtain ⟨hpos, hlt, hgap, hparent⟩ := hs j hj
    refine ⟨hpos, hlt, hgap, ?_⟩
    simpa only [f, dite_eq_left hj] using hparent.choose_spec.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro j hj k W hW
    simpa only [f, dite_eq_left hj] using (hs j hj).2.2.2.choose_spec.2 k W hW

/-- Absorb a multiplicative mesh constant before realizing the final tower. -/
theorem tower_of_chain_mesh {d L g θ : ℝ} {B J : ℕ} {p c : Layer}
    (hp : p.radius = 1) (hpN : p.card = 1) (hc : c.radius = d)
    (hJ : 1 ≤ J) (hJB : J ≤ B) (hmesh : d ^ g ≤ θ)
    (h : Chain (LocalEdge θ L) p c J) :
    Tower false d L g B c.card c.position c.direction :=
  tower_of_chain hp hpN hc hJ hJB (h.mono fun _ _ he => he.mono hmesh le_rfl)

end WangZahlLot.Obl.wz_multiscale_finite_tower
