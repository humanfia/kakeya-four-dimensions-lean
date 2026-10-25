import Mathlib

/- Adapted from this LOT tree o015, session x0051,
   Submission/Lib/K4SwitchingExperiment.lean (branch x0051, 2026-10-21).
   The original is self-authored within this tree; only the namespace is changed. -/

/-!
# A finite switching experiment with full-past kernel domination

General finite-probability lemmas for the switching experiment of the paper's
Lemma 3.3 (two-colour matching): refresh on a fine atom, choose a colour
adaptively, resample on the chosen arm's atom, and kill steps with a bad palette
likelihood, a light arm atom, a separation failure, or a broken invariant.

* `SwitchData.pathValue_le_freeBound`: the unnormalized killed path mass is at most
  the free iterated bound with step factor `exp θ * (ρ / lam)` (nothing is
  renormalized and no kernel is conditioned on future survival).
* `SwitchData.freeBound_le`: the free iterated bound is at most
  `(c * (2 * #Nbr))^n` times any supersolution of the time-cell recursion.
* `SwitchData.one_sub_le_sum_pathValue`: averaged over starts, the killed path mass
  is at least `1 - (2^n - 1) X`, where `X` collects the bad palette mass, the light
  atom masses of both colours, and the separation failure bound.
* `card_bad_steps_mul_le`: Markov over steps for a summed positive log-likelihood bound.

Written for o015 (`k4_two_color_matching`) by session x0051; no outside code.
-/

set_option linter.unusedSectionVars false

namespace Submission.Obl.k4_matching_abstract_switching_mixture.Finite

open Finset

section Atoms

variable {Ω γ : Type*} [Fintype Ω] [DecidableEq γ]

/-- The `P`-mass of the fibre `K = c`. -/
noncomputable def fiberMass (P : Ω → ℝ) (K : Ω → γ) (c : γ) : ℝ :=
  ∑ ω' ∈ univ.filter (fun ω' => K ω' = c), P ω'

/-- The `P`-mass of the fibre of `K` through `ω`. -/
noncomputable def atomMass (P : Ω → ℝ) (K : Ω → γ) (ω : Ω) : ℝ :=
  fiberMass P K (K ω)

lemma fiberMass_nonneg {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (K : Ω → γ) (c : γ) :
    0 ≤ fiberMass P K c :=
  sum_nonneg fun ω _ => hP ω

lemma le_atomMass {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (K : Ω → γ) (ω : Ω) :
    P ω ≤ atomMass P K ω := by
  unfold atomMass fiberMass
  exact single_le_sum (f := P) (fun ω _ => hP ω) (by simp)

lemma atomMass_pos {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (K : Ω → γ) {ω : Ω} (hω : 0 < P ω) :
    0 < atomMass P K ω :=
  lt_of_lt_of_le hω (le_atomMass hP K ω)

/-- Summing the fibre masses over the image recovers the total mass. -/
lemma sum_fiberMass_image (P : Ω → ℝ) (K : Ω → γ) :
    ∑ c ∈ univ.image K, fiberMass P K c = ∑ ω, P ω := by
  unfold fiberMass
  exact sum_fiberwise_of_maps_to (fun ω _ => mem_image_of_mem K (mem_univ ω)) P

/-- The key fibre identity: dividing by the atom mass and summing counts each
atom of positive mass once. -/
lemma sum_mul_div_atomMass (P : Ω → ℝ) (K : Ω → γ) (g : γ → ℝ) :
    ∑ ω, P ω * g (K ω) / atomMass P K ω
      = ∑ c ∈ univ.image K, if fiberMass P K c = 0 then 0 else g c := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image K) (g := K)
    (fun ω _ => mem_image_of_mem K (mem_univ ω))]
  refine sum_congr rfl fun c _ => ?_
  have h : ∀ ω ∈ univ.filter (fun ω => K ω = c),
      P ω * g (K ω) / atomMass P K ω = P ω * (g c / fiberMass P K c) := by
    intro ω hω
    rw [mem_filter] at hω
    simp only [atomMass, hω.2]
    ring
  rw [sum_congr rfl h, ← sum_mul]
  change fiberMass P K c * (g c / fiberMass P K c) = _
  split_ifs with h0
  · simp [h0]
  · field_simp

end Atoms

section CondOwn

variable {Ω α β : Type*} [Fintype Ω] [DecidableEq α] [DecidableEq β]

/-- `P(Z = Z ω | G = G ω)`. -/
noncomputable def condOwn (P : Ω → ℝ) (Z : Ω → α) (G : Ω → β) (ω : Ω) : ℝ :=
  atomMass P (fun ω' => (G ω', Z ω')) ω / atomMass P G ω

/-- `∑ P log P(Z | G)`, minus the conditional entropy of `Z` given `G`. -/
noncomputable def negCondEnt (P : Ω → ℝ) (Z : Ω → α) (G : Ω → β) : ℝ :=
  ∑ ω, P ω * Real.log (condOwn P Z G ω)

lemma condOwn_pos {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (Z : Ω → α) (G : Ω → β) {ω : Ω}
    (hω : 0 < P ω) : 0 < condOwn P Z G ω :=
  div_pos (atomMass_pos hP _ hω) (atomMass_pos hP _ hω)

lemma condOwn_le_one {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (Z : Ω → α) (G : Ω → β) (ω : Ω) :
    condOwn P Z G ω ≤ 1 := by
  unfold condOwn
  rcases (fiberMass_nonneg hP G (G ω)).eq_or_lt with h | h
  · simp [atomMass, ← h]
  · rw [div_le_one (by simpa [atomMass] using h)]
    unfold atomMass fiberMass
    refine sum_le_sum_of_subset_of_nonneg ?_ fun ω _ _ => hP ω
    intro ω' hω'
    simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq] at hω' ⊢
    exact hω'.1

lemma negCondEnt_nonpos {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (Z : Ω → α) (G : Ω → β) :
    negCondEnt P Z G ≤ 0 := by
  refine sum_nonpos fun ω _ => mul_nonpos_of_nonneg_of_nonpos (hP ω) ?_
  rcases (hP ω).eq_or_lt with h | h
  · -- the log of a nonnegative number at most one
    exact Real.log_nonpos (div_nonneg (fiberMass_nonneg hP _ _) (fiberMass_nonneg hP _ _))
      (condOwn_le_one hP Z G ω)
  · exact Real.log_nonpos (condOwn_pos hP Z G h).le (condOwn_le_one hP Z G ω)


end CondOwn

section CondKey

variable {Ω γ : Type*} [Fintype Ω] [DecidableEq γ]

/-- Weight of `ω` under `P` conditioned on the `K`-atom of `ω₀`. -/
noncomputable def condKey (P : Ω → ℝ) (K : Ω → γ) (ω₀ ω : Ω) : ℝ :=
  if K ω = K ω₀ then P ω / atomMass P K ω₀ else 0

lemma condKey_nonneg {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (K : Ω → γ) (ω₀ ω : Ω) :
    0 ≤ condKey P K ω₀ ω := by
  unfold condKey
  split_ifs
  · exact div_nonneg (hP ω) (fiberMass_nonneg hP K _)
  · exact le_refl 0

lemma sum_condKey_eq_one {P : Ω → ℝ} (K : Ω → γ) {ω₀ : Ω} (h : atomMass P K ω₀ ≠ 0) :
    ∑ ω, condKey P K ω₀ ω = 1 := by
  unfold condKey
  rw [← sum_filter, ← sum_div]
  exact div_self h

lemma sum_condKey_eq_one_of_pos {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (K : Ω → γ) {ω₀ : Ω}
    (h : 0 < P ω₀) : ∑ ω, condKey P K ω₀ ω = 1 :=
  sum_condKey_eq_one K (atomMass_pos hP K h).ne'

lemma condKey_pos_of_ne {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (K : Ω → γ) {ω₀ ω : Ω}
    (h : condKey P K ω₀ ω ≠ 0) : 0 < P ω := by
  unfold condKey at h
  split_ifs at h with hk
  · rcases (hP ω).eq_or_lt with h0 | h0
    · rw [← h0, zero_div] at h; exact absurd rfl h
    · exact h0
  · exact absurd rfl h

lemma condKey_key_eq {P : Ω → ℝ} (K : Ω → γ) {ω₀ ω : Ω} (h : condKey P K ω₀ ω ≠ 0) :
    K ω = K ω₀ := by
  unfold condKey at h
  split_ifs at h with hk
  · exact hk
  · exact absurd rfl h

/-- Stationarity: averaging the conditioned laws over `P` returns `P`. -/
lemma sum_mul_condKey {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (K : Ω → γ) (ω : Ω) :
    ∑ ω₀, P ω₀ * condKey P K ω₀ ω = P ω := by
  unfold condKey
  have h : ∀ ω₀, P ω₀ * (if K ω = K ω₀ then P ω / atomMass P K ω₀ else 0)
      = if K ω₀ = K ω then P ω₀ * (P ω / atomMass P K ω) else 0 := by
    intro ω₀
    by_cases hk : K ω₀ = K ω
    · rw [if_pos hk.symm, if_pos hk, atomMass, atomMass, hk]
    · rw [if_neg (Ne.symm hk), if_neg hk, mul_zero]
  rw [sum_congr rfl fun ω₀ _ => h ω₀, ← sum_filter, ← sum_mul]
  change atomMass P K ω * (P ω / atomMass P K ω) = P ω
  rcases (hP ω).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · field_simp [(atomMass_pos hP K h0).ne']

/-- A law dominated by `C P` stays dominated by `C P` after conditioning on atoms. -/
lemma sum_mul_condKey_le {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (K : Ω → γ) {ρ : Ω → ℝ} {C : ℝ}
    (hρ : ∀ ω, ρ ω ≤ C * P ω) (ω : Ω) :
    ∑ ω₀, ρ ω₀ * condKey P K ω₀ ω ≤ C * P ω := by
  calc ∑ ω₀, ρ ω₀ * condKey P K ω₀ ω ≤ ∑ ω₀, C * P ω₀ * condKey P K ω₀ ω :=
        sum_le_sum fun ω₀ _ => mul_le_mul_of_nonneg_right (hρ ω₀) (condKey_nonneg hP K ω₀ ω)
    _ = C * ∑ ω₀, P ω₀ * condKey P K ω₀ ω := by rw [mul_sum]; simp only [mul_assoc]
    _ = C * P ω := by rw [sum_mul_condKey hP K ω]

end CondKey

section Switching

variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf] [DecidableEq Sc]
  [DecidableEq Ar] [DecidableEq Iv] [DecidableEq Pal] [Fintype Tc] [DecidableEq Tc]

/-- The data of a switching experiment. -/
structure SwitchData (Ω Sf Sc Ar Iv Pal Tc : Type*) where
  /-- the event law -/
  P : Ω → ℝ
  /-- fine state (level `a + C b`) -/
  fine : Ω → Sf
  /-- coarse state (level `a`) -/
  coarse : Ω → Sc
  /-- palette -/
  Z : Ω → Pal
  /-- the arm of colour `κ` -/
  arm : Ω → Bool → Ar
  /-- coarse time interval -/
  ival : Ω → Iv
  /-- time cell -/
  cell : Ω → Tc
  /-- control of the colour-`κ` arm, from palette and coarse state -/
  Ψ : Pal → Sc → Bool → ℝ
  /-- log-likelihood threshold of the palette -/
  θ : ℝ

variable (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)

open Classical

/-- The atom key of the colour-`κ` arm: its index and the interval. -/
def SwitchData.armKey (κ : Bool) (ω : Ω) : Ar × Iv := (X.arm ω κ, X.ival ω)

/-- The control of the colour-`κ` arm of `ω`. -/
def SwitchData.ctrl (ω : Ω) (κ : Bool) : ℝ := X.Ψ (X.Z ω) (X.coarse ω) κ

/-- Good palette likelihood at a refreshed event. -/
def SwitchData.good (ω : Ω) : Prop :=
  condOwn X.P X.Z X.fine ω ≤ Real.exp X.θ * condOwn X.P X.Z X.coarse ω

/-- The colour-`κ` arm atom of `ω` is heavy for priors `π` and threshold `lam`. -/
def SwitchData.heavy (π : Bool → Ar → ℝ) (lam : ℝ) (ω : Ω) (κ : Bool) : Prop :=
  π κ (X.arm ω κ) * lam ≤ atomMass X.P (X.armKey κ) ω

/-- The coarse palette law `P(Z = z | coarse = x)`. -/
noncomputable def SwitchData.condPal (x : Sc) (z : Pal) : ℝ :=
  fiberMass X.P (fun ω => (X.coarse ω, X.Z ω)) (x, z) / fiberMass X.P X.coarse x

/-- The current event of a path. -/
def curEvent (e₀ : Ω) (path : List (Ω × Bool × Ω)) : Ω :=
  match path.getLast? with
  | none => e₀
  | some q => q.2.2

@[simp] lemma curEvent_nil (e₀ : Ω) : curEvent e₀ ([] : List (Ω × Bool × Ω)) = e₀ := rfl

@[simp] lemma curEvent_append (e₀ : Ω) (path : List (Ω × Bool × Ω)) (q : Ω × Bool × Ω) :
    curEvent e₀ (path ++ [q]) = q.2.2 := by
  simp [curEvent]

/-- The (control, cell) record of a path. -/
def SwitchData.proj (path : List (Ω × Bool × Ω)) : List (ℝ × Tc) :=
  path.map fun q => (X.ctrl q.1 q.2.1, X.cell q.2.2)

@[simp] lemma SwitchData.proj_append (path : List (Ω × Bool × Ω)) (q : Ω × Bool × Ω) :
    X.proj (path ++ [q]) = X.proj path ++ [(X.ctrl q.1 q.2.1, X.cell q.2.2)] := by
  simp [SwitchData.proj]

/-- The unnormalized killed path mass with terminal test `τ`, from path `path`, with `n`
traversals left. -/
noncomputable def SwitchData.pathValue (π : Bool → Ar → ℝ) (lam : ℝ)
    (χ : Ω → List (Ω × Bool × Ω) → Ω → Bool)
    (sepOK : ℕ → List (Ω × Bool × Ω) → Ω → Prop)
    (Q : Ω → List (Ω × Bool × Ω) → Prop) (τ : Ω → List (Ω × Bool × Ω) → ℝ) :
    ℕ → Ω → List (Ω × Bool × Ω) → ℝ
  | 0, e₀, path => τ e₀ path
  | n + 1, e₀, path =>
    ∑ er, condKey X.P X.fine (curEvent e₀ path) er *
      (if X.good er then
        ∑ e', condKey X.P (X.armKey (χ e₀ path er)) er e' *
          (if X.heavy π lam er (χ e₀ path er) ∧ sepOK n path e' ∧
              Q e₀ (path ++ [(er, χ e₀ path er, e')])
            then SwitchData.pathValue π lam χ sepOK Q τ n e₀ (path ++ [(er, χ e₀ path er, e')])
            else 0)
      else 0)

/-- The free iterated bound: each step contributes `c` times the coarse palette laws of
the neighbour states and a sum over time cells. -/
noncomputable def SwitchData.freeBound (c : ℝ) (Nbr : Finset Sc) (τ' : List (ℝ × Tc) → ℝ) :
    ℕ → List (ℝ × Tc) → ℝ
  | 0, l => τ' l
  | n + 1, l => c * ∑ x ∈ Nbr, ∑ κ : Bool, ∑ z ∈ univ.image X.Z, X.condPal x z *
      ∑ t : Tc, SwitchData.freeBound c Nbr τ' n (l ++ [(X.Ψ z x κ, t)])

lemma SwitchData.condPal_nonneg (hP : ∀ ω, 0 ≤ X.P ω) (x : Sc) (z : Pal) :
    0 ≤ X.condPal x z :=
  div_nonneg (fiberMass_nonneg hP _ _) (fiberMass_nonneg hP _ _)

lemma SwitchData.freeBound_nonneg (hP : ∀ ω, 0 ≤ X.P ω) {c : ℝ} (hc : 0 ≤ c) (Nbr : Finset Sc)
    {τ' : List (ℝ × Tc) → ℝ} (hτ' : ∀ l, 0 ≤ τ' l) :
    ∀ n l, 0 ≤ X.freeBound c Nbr τ' n l := by
  intro n
  induction n with
  | zero => exact fun l => hτ' l
  | succ n ih =>
    intro l
    simp only [SwitchData.freeBound]
    exact mul_nonneg hc (sum_nonneg fun x _ => sum_nonneg fun κ _ => sum_nonneg fun z _ =>
      mul_nonneg (X.condPal_nonneg hP x z) (sum_nonneg fun t _ => ih _))

/-- The time-cell bound of one traversal: after conditioning on a heavy arm atom, each
time cell has weight at most `ρ / lam`. -/
lemma SwitchData.sum_condKey_cell_le (hP : ∀ ω, 0 ≤ X.P ω) (π : Bool → Ar → ℝ)
    {lam ρ : ℝ} (hlam : 0 < lam) (hρ : 0 ≤ ρ)
    (hcell : ∀ κ a t, fiberMass X.P (fun ω => (X.arm ω κ, X.cell ω)) (a, t) ≤ π κ a * ρ)
    (er : Ω) (κ : Bool) (hheavy : X.heavy π lam er κ) (h : Tc → ℝ) (hh : ∀ t, 0 ≤ h t) :
    ∑ e', condKey X.P (X.armKey κ) er e' * h (X.cell e') ≤ ρ / lam * ∑ t, h t := by
  set m := atomMass X.P (X.armKey κ) er with hm
  have hm0 : 0 ≤ m := fiberMass_nonneg hP _ _
  -- regroup by cells
  have e1 : ∑ e', condKey X.P (X.armKey κ) er e' * h (X.cell e')
      = ∑ t, h t * ((∑ e' ∈ univ.filter (fun e' => X.cell e' = t ∧
          X.armKey κ e' = X.armKey κ er), X.P e') / m) := by
    rw [← sum_fiberwise (s := univ) (g := X.cell)]
    refine sum_congr rfl fun t _ => ?_
    have hterm : ∀ i ∈ univ.filter (fun i => X.cell i = t),
        condKey X.P (X.armKey κ) er i * h (X.cell i)
          = h t * (if X.armKey κ i = X.armKey κ er then X.P i / m else 0) := by
      intro i hi
      rw [mem_filter] at hi
      rw [hi.2]
      unfold condKey
      rw [← hm]
      ring
    rw [sum_congr rfl hterm, ← mul_sum, ← sum_filter, filter_filter, sum_div]
  rw [e1, mul_sum]
  refine sum_le_sum fun t _ => ?_
  -- each cell has conditional weight at most `ρ / lam`
  have hfib : ∑ e' ∈ univ.filter (fun e' => X.cell e' = t ∧ X.armKey κ e' = X.armKey κ er),
      X.P e' ≤ π κ (X.arm er κ) * ρ := by
    refine le_trans ?_ (hcell κ (X.arm er κ) t)
    unfold fiberMass
    refine sum_le_sum_of_subset_of_nonneg ?_ fun ω _ _ => hP ω
    intro e' he'
    simp only [mem_filter, mem_univ, true_and, SwitchData.armKey, Prod.mk.injEq] at he' ⊢
    exact ⟨he'.2.1, he'.1⟩
  have hnum : 0 ≤ ∑ e' ∈ univ.filter (fun e' => X.cell e' = t ∧
      X.armKey κ e' = X.armKey κ er), X.P e' := sum_nonneg fun ω _ => hP ω
  have hratio : (∑ e' ∈ univ.filter (fun e' => X.cell e' = t ∧
      X.armKey κ e' = X.armKey κ er), X.P e') / m ≤ ρ / lam := by
    rcases hm0.eq_or_lt with hm0' | hm0'
    · rw [← hm0', div_zero]; exact div_nonneg hρ hlam.le
    · rw [div_le_div_iff₀ hm0' hlam]
      unfold SwitchData.heavy at hheavy
      rw [← hm] at hheavy
      calc (∑ e' ∈ univ.filter (fun e' => X.cell e' = t ∧ X.armKey κ e' = X.armKey κ er),
            X.P e') * lam ≤ π κ (X.arm er κ) * ρ * lam :=
            mul_le_mul_of_nonneg_right hfib hlam.le
        _ = ρ * (π κ (X.arm er κ) * lam) := by ring
        _ ≤ ρ * m := mul_le_mul_of_nonneg_left hheavy hρ
  calc h t * ((∑ e' ∈ univ.filter (fun e' => X.cell e' = t ∧
        X.armKey κ e' = X.armKey κ er), X.P e') / m) ≤ h t * (ρ / lam) :=
        mul_le_mul_of_nonneg_left hratio (hh t)
    _ = ρ / lam * h t := mul_comm _ _

/-- On one palette value, the refreshed good mass is at most `exp θ` times the coarse
palette law. -/
lemma SwitchData.sum_good_fiber_le (hP : ∀ ω, 0 ≤ X.P ω) {g : Sf → Sc}
    (hcoarse : ∀ ω, X.coarse ω = g (X.fine ω)) (e : Ω) (z : Pal) :
    ∑ er ∈ univ.filter (fun er => X.Z er = z),
        condKey X.P X.fine e er * (if X.good er then 1 else 0)
      ≤ Real.exp X.θ * X.condPal (X.coarse e) z := by
  have hnn : 0 ≤ Real.exp X.θ * X.condPal (X.coarse e) z :=
    mul_nonneg (Real.exp_pos _).le (X.condPal_nonneg hP _ _)
  by_cases hex : ∃ er₀, X.Z er₀ = z ∧ X.fine er₀ = X.fine e ∧ X.good er₀
  · obtain ⟨er₀, hz, hf, hg⟩ := hex
    calc ∑ er ∈ univ.filter (fun er => X.Z er = z),
          condKey X.P X.fine e er * (if X.good er then 1 else 0)
        ≤ ∑ er ∈ univ.filter (fun er => X.Z er = z), condKey X.P X.fine e er := by
          refine sum_le_sum fun er _ => ?_
          split_ifs
          · rw [mul_one]
          · rw [mul_zero]; exact condKey_nonneg hP _ _ _
      _ = condOwn X.P X.Z X.fine er₀ := by
          unfold condKey condOwn atomMass fiberMass
          simp only [hf, hz]
          rw [← sum_filter, filter_filter, ← sum_div]
          congr 2
          ext ω
          simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq]
          tauto
      _ ≤ Real.exp X.θ * condOwn X.P X.Z X.coarse er₀ := hg
      _ = Real.exp X.θ * X.condPal (X.coarse e) z := by
          have hc : X.coarse er₀ = X.coarse e := by rw [hcoarse, hcoarse e, hf]
          unfold condOwn SwitchData.condPal atomMass
          simp only [hc, hz]
  · push Not at hex
    calc ∑ er ∈ univ.filter (fun er => X.Z er = z),
          condKey X.P X.fine e er * (if X.good er then 1 else 0) = 0 := by
          refine sum_eq_zero fun er her => ?_
          rw [mem_filter] at her
          by_cases hr : condKey X.P X.fine e er = 0
          · rw [hr, zero_mul]
          · have hf := condKey_key_eq (P := X.P) X.fine hr
            rw [if_neg (hex er her.2 hf), mul_zero]
      _ ≤ _ := hnn

/-- The palette step of the full-past domination: after a refresh from the fine atom of
`e`, the law of the chosen control on good palette values is dominated by `exp θ` times
the coarse palette laws, summed over both colours. -/
lemma SwitchData.sum_good_ctrl_le (hP : ∀ ω, 0 ≤ X.P ω) {g : Sf → Sc}
    (hcoarse : ∀ ω, X.coarse ω = g (X.fine ω)) (e : Ω) (κf : Ω → Bool) (φ : ℝ → ℝ)
    (hφ : ∀ u, 0 ≤ φ u) :
    ∑ er, condKey X.P X.fine e er * (if X.good er then φ (X.ctrl er (κf er)) else 0)
      ≤ Real.exp X.θ * ∑ κ : Bool, ∑ z ∈ univ.image X.Z, X.condPal (X.coarse e) z *
          φ (X.Ψ z (X.coarse e) κ) := by
  set x := X.coarse e with hx
  set w : Ω → ℝ := fun er => condKey X.P X.fine e er * (if X.good er then 1 else 0) with hw
  have hw0 : ∀ er, 0 ≤ w er := fun er =>
    mul_nonneg (condKey_nonneg hP _ _ _) (by split_ifs <;> norm_num)
  -- replace the chosen colour by both colours and the coarse state by `x`
  have h1 : ∀ er, condKey X.P X.fine e er * (if X.good er then φ (X.ctrl er (κf er)) else 0)
      ≤ ∑ κ : Bool, w er * φ (X.Ψ (X.Z er) x κ) := by
    intro er
    by_cases hr : condKey X.P X.fine e er = 0
    · simp [hw, hr]
    have hfe := condKey_key_eq (P := X.P) X.fine hr
    have hcx : X.coarse er = x := by rw [hx, hcoarse er, hcoarse e, hfe]
    simp only [hw]
    by_cases hg : X.good er
    · simp only [if_pos hg, mul_one, SwitchData.ctrl, hcx, Fintype.sum_bool]
      have h0 := mul_nonneg (condKey_nonneg hP X.fine e er) (hφ (X.Ψ (X.Z er) x true))
      have h0' := mul_nonneg (condKey_nonneg hP X.fine e er) (hφ (X.Ψ (X.Z er) x false))
      cases κf er <;> linarith
    · simp [hg]
  calc ∑ er, condKey X.P X.fine e er * (if X.good er then φ (X.ctrl er (κf er)) else 0)
      ≤ ∑ er, ∑ κ : Bool, w er * φ (X.Ψ (X.Z er) x κ) := sum_le_sum fun er _ => h1 er
    _ = ∑ κ : Bool, ∑ z ∈ univ.image X.Z, (∑ er ∈ univ.filter (fun er => X.Z er = z), w er) *
          φ (X.Ψ z x κ) := by
        rw [sum_comm]
        refine sum_congr rfl fun κ _ => ?_
        rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image X.Z) (g := X.Z)
          (fun ω _ => mem_image_of_mem _ (mem_univ ω))]
        refine sum_congr rfl fun z _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun er her => ?_
        rw [mem_filter] at her
        rw [her.2]
    _ ≤ ∑ κ : Bool, ∑ z ∈ univ.image X.Z, Real.exp X.θ * X.condPal x z * φ (X.Ψ z x κ) := by
        refine sum_le_sum fun κ _ => sum_le_sum fun z _ => ?_
        exact mul_le_mul_of_nonneg_right (X.sum_good_fiber_le hP hcoarse e z) (hφ _)
    _ = Real.exp X.θ * ∑ κ : Bool, ∑ z ∈ univ.image X.Z, X.condPal x z * φ (X.Ψ z x κ) := by
        rw [mul_sum]
        refine sum_congr rfl fun κ _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun z _ => ?_
        ring

/-- **Full-past domination.** On every path satisfying the invariant, the killed path mass
is at most the free iterated bound with step factor `exp θ * (ρ / lam)`. -/
theorem SwitchData.pathValue_le_freeBound (hP : ∀ ω, 0 ≤ X.P ω) {g : Sf → Sc}
    (hcoarse : ∀ ω, X.coarse ω = g (X.fine ω)) (π : Bool → Ar → ℝ)
    {lam ρ : ℝ} (hlam : 0 < lam) (hρ : 0 ≤ ρ)
    (hcell : ∀ κ a t, fiberMass X.P (fun ω => (X.arm ω κ, X.cell ω)) (a, t) ≤ π κ a * ρ)
    (χ : Ω → List (Ω × Bool × Ω) → Ω → Bool) (sepOK : ℕ → List (Ω × Bool × Ω) → Ω → Prop)
    (Q : Ω → List (Ω × Bool × Ω) → Prop) (τ : Ω → List (Ω × Bool × Ω) → ℝ) (e₀ : Ω)
    (Nbr : Finset Sc) (τ' : List (ℝ × Tc) → ℝ) (hτ' : ∀ l, 0 ≤ τ' l) (L₀ : ℕ)
    (hτ : ∀ path, path.length ≤ L₀ → Q e₀ path → τ e₀ path ≤ τ' (X.proj path))
    (hNbr : ∀ path, path.length < L₀ → Q e₀ path → X.coarse (curEvent e₀ path) ∈ Nbr) :
    ∀ n path, path.length + n ≤ L₀ → Q e₀ path → X.pathValue π lam χ sepOK Q τ n e₀ path
      ≤ X.freeBound (Real.exp X.θ * (ρ / lam)) Nbr τ' n (X.proj path) := by
  have hc : 0 ≤ Real.exp X.θ * (ρ / lam) :=
    mul_nonneg (Real.exp_pos _).le (div_nonneg hρ hlam.le)
  have hF0 := X.freeBound_nonneg hP hc Nbr hτ'
  intro n
  induction n with
  | zero =>
    intro path hlen hQ
    simp only [SwitchData.pathValue, SwitchData.freeBound]
    exact hτ path (by omega) hQ
  | succ n ih =>
    intro path hlen hQ
    set e := curEvent e₀ path with he
    set F : ℝ → Tc → ℝ := fun u t =>
      X.freeBound (Real.exp X.θ * (ρ / lam)) Nbr τ' n (X.proj path ++ [(u, t)]) with hF
    have hFnn : ∀ u t, 0 ≤ F u t := fun u t => hF0 n _
    -- the inner traversal sum
    have hinner : ∀ er, X.good er →
        ∑ e', condKey X.P (X.armKey (χ e₀ path er)) er e' *
          (if X.heavy π lam er (χ e₀ path er) ∧ sepOK n path e' ∧
              Q e₀ (path ++ [(er, χ e₀ path er, e')])
            then X.pathValue π lam χ sepOK Q τ n e₀ (path ++ [(er, χ e₀ path er, e')])
            else 0)
          ≤ ρ / lam * ∑ t, F (X.ctrl er (χ e₀ path er)) t := by
      intro er _
      set κ := χ e₀ path er with hκ
      by_cases hh : X.heavy π lam er κ
      · calc ∑ e', condKey X.P (X.armKey κ) er e' *
              (if X.heavy π lam er κ ∧ sepOK n path e' ∧ Q e₀ (path ++ [(er, κ, e')])
                then X.pathValue π lam χ sepOK Q τ n e₀ (path ++ [(er, κ, e')]) else 0)
            ≤ ∑ e', condKey X.P (X.armKey κ) er e' * F (X.ctrl er κ) (X.cell e') := by
              refine sum_le_sum fun e' _ => ?_
              refine mul_le_mul_of_nonneg_left ?_ (condKey_nonneg hP _ _ _)
              split_ifs with hcond
              · have := ih (path ++ [(er, κ, e')])
                  (by simp only [List.length_append, List.length_singleton]; omega) hcond.2.2
                simpa [hF] using this
              · exact hFnn _ _
          _ ≤ ρ / lam * ∑ t, F (X.ctrl er κ) t :=
              X.sum_condKey_cell_le hP π hlam hρ hcell er κ hh _ fun t => hFnn _ t
      · have : ∀ e', condKey X.P (X.armKey κ) er e' *
            (if X.heavy π lam er κ ∧ sepOK n path e' ∧ Q e₀ (path ++ [(er, κ, e')])
              then X.pathValue π lam χ sepOK Q τ n e₀ (path ++ [(er, κ, e')]) else 0) = 0 := by
          intro e'
          rw [if_neg (fun h => hh h.1), mul_zero]
        rw [sum_congr rfl fun e' _ => this e', sum_const_zero]
        exact mul_nonneg (div_nonneg hρ hlam.le) (sum_nonneg fun t _ => hFnn _ t)
    calc X.pathValue π lam χ sepOK Q τ (n + 1) e₀ path
        ≤ ∑ er, condKey X.P X.fine e er *
            (if X.good er then ρ / lam * ∑ t, F (X.ctrl er (χ e₀ path er)) t else 0) := by
          simp only [SwitchData.pathValue]
          refine sum_le_sum fun er _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (condKey_nonneg hP _ _ _)
          split_ifs with hg
          · exact hinner er hg
          · exact le_refl 0
      _ ≤ Real.exp X.θ * ∑ κ : Bool, ∑ z ∈ univ.image X.Z, X.condPal (X.coarse e) z *
            (ρ / lam * ∑ t, F (X.Ψ z (X.coarse e) κ) t) :=
          X.sum_good_ctrl_le hP hcoarse e (χ e₀ path) (fun u => ρ / lam * ∑ t, F u t)
            fun u => mul_nonneg (div_nonneg hρ hlam.le) (sum_nonneg fun t _ => hFnn u t)
      _ ≤ Real.exp X.θ * ∑ x ∈ Nbr, ∑ κ : Bool, ∑ z ∈ univ.image X.Z, X.condPal x z *
            (ρ / lam * ∑ t, F (X.Ψ z x κ) t) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact single_le_sum (f := fun x => ∑ κ : Bool, ∑ z ∈ univ.image X.Z, X.condPal x z *
            (ρ / lam * ∑ t, F (X.Ψ z x κ) t))
            (fun x _ => sum_nonneg fun κ _ => sum_nonneg fun z _ =>
              mul_nonneg (X.condPal_nonneg hP x z)
                (mul_nonneg (div_nonneg hρ hlam.le) (sum_nonneg fun t _ => hFnn _ t)))
            (hNbr path (by omega) hQ)
      _ = X.freeBound (Real.exp X.θ * (ρ / lam)) Nbr τ' (n + 1) (X.proj path) := by
          simp only [SwitchData.freeBound, hF, mul_sum]
          refine sum_congr rfl fun x _ => sum_congr rfl fun κ _ => sum_congr rfl fun z _ =>
            sum_congr rfl fun t _ => ?_
          ring

/-- The failure bound: kills by a bad palette, a light atom (either colour), a separation
failure (mass at most `s`), and the failures further on (either colour). -/
noncomputable def SwitchData.failBound (π : Bool → Ar → ℝ) (lam s : ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, e => ∑ er, condKey X.P X.fine e er *
      ((if X.good er then 0 else 1) + ∑ κ : Bool, (if X.heavy π lam er κ then 0 else 1) + s +
        ∑ κ : Bool, ∑ e', condKey X.P (X.armKey κ) er e' * SwitchData.failBound π lam s n e')

lemma SwitchData.failBound_nonneg (hP : ∀ ω, 0 ≤ X.P ω) (π : Bool → Ar → ℝ) (lam : ℝ) {s : ℝ}
    (hs : 0 ≤ s) : ∀ n e, 0 ≤ X.failBound π lam s n e := by
  intro n
  induction n with
  | zero => intro e; simp [SwitchData.failBound]
  | succ n ih =>
    intro e
    simp only [SwitchData.failBound]
    refine sum_nonneg fun er _ => mul_nonneg (condKey_nonneg hP _ _ _) ?_
    refine add_nonneg (add_nonneg (add_nonneg (by split_ifs <;> norm_num)
      (sum_nonneg fun κ _ => by split_ifs <;> norm_num)) hs) ?_
    exact sum_nonneg fun κ _ => sum_nonneg fun e' _ =>
      mul_nonneg (condKey_nonneg hP _ _ _) (ih e')

/-- **Success lower bound along a path.** -/
theorem SwitchData.one_sub_failBound_le_pathValue (hP : ∀ ω, 0 ≤ X.P ω)
    (π : Bool → Ar → ℝ) (lam : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (χ : Ω → List (Ω × Bool × Ω) → Ω → Bool) (sepOK : ℕ → List (Ω × Bool × Ω) → Ω → Prop)
    (Q : Ω → List (Ω × Bool × Ω) → Prop) (τ : Ω → List (Ω × Bool × Ω) → ℝ) (e₀ : Ω)
    (L₀ : ℕ)
    (hτ1 : ∀ path, path.length ≤ L₀ → Q e₀ path → 1 ≤ τ e₀ path)
    (hQ : ∀ n path er e', path.length + n + 1 ≤ L₀ → Q e₀ path →
      condKey X.P X.fine (curEvent e₀ path) er ≠ 0 →
      X.good er → condKey X.P (X.armKey (χ e₀ path er)) er e' ≠ 0 →
      X.heavy π lam er (χ e₀ path er) → sepOK n path e' →
      Q e₀ (path ++ [(er, χ e₀ path er, e')]))
    (hsep : ∀ n path er κ, path.length + n + 1 ≤ L₀ → X.heavy π lam er κ →
      ∑ e', condKey X.P (X.armKey κ) er e' * (if sepOK n path e' then 0 else 1) ≤ s) :
    ∀ n path, path.length + n ≤ L₀ → Q e₀ path → 0 < X.P (curEvent e₀ path) →
      1 - X.failBound π lam s n (curEvent e₀ path)
        ≤ X.pathValue π lam χ sepOK Q τ n e₀ path := by
  have hG0 := X.failBound_nonneg hP π lam hs
  intro n
  induction n with
  | zero =>
    intro path hlen hQp _
    simp only [SwitchData.failBound, SwitchData.pathValue, sub_zero]
    exact hτ1 path (by omega) hQp
  | succ n ih =>
    intro path hlen hQp hpos
    set e := curEvent e₀ path with he
    have hsum1 : ∑ er, condKey X.P X.fine e er = 1 := sum_condKey_eq_one_of_pos hP _ hpos
    simp only [SwitchData.failBound, SwitchData.pathValue]
    rw [← he]
    -- termwise comparison
    have key : ∀ er, condKey X.P X.fine e er * 1 - condKey X.P X.fine e er *
        ((if X.good er then 0 else 1) + ∑ κ : Bool, (if X.heavy π lam er κ then 0 else 1) + s +
          ∑ κ : Bool, ∑ e', condKey X.P (X.armKey κ) er e' * X.failBound π lam s n e')
        ≤ condKey X.P X.fine e er *
          (if X.good er then
            ∑ e', condKey X.P (X.armKey (χ e₀ path er)) er e' *
              (if X.heavy π lam er (χ e₀ path er) ∧ sepOK n path e' ∧
                  Q e₀ (path ++ [(er, χ e₀ path er, e')])
                then X.pathValue π lam χ sepOK Q τ n e₀ (path ++ [(er, χ e₀ path er, e')])
                else 0)
          else 0) := by
      intro er
      rw [← mul_sub]
      by_cases hr : condKey X.P X.fine e er = 0
      · simp [hr]
      refine mul_le_mul_of_nonneg_left ?_ (condKey_nonneg hP _ _ _)
      have hper : 0 < X.P er := condKey_pos_of_ne hP _ hr
      set κ := χ e₀ path er with hκ
      have hGsum : 0 ≤ ∑ κ' : Bool, ∑ e', condKey X.P (X.armKey κ') er e' *
          X.failBound π lam s n e' := sum_nonneg fun κ' _ => sum_nonneg fun e' _ =>
            mul_nonneg (condKey_nonneg hP _ _ _) (hG0 n e')
      have hlight : 0 ≤ ∑ κ' : Bool, (if X.heavy π lam er κ' then (0 : ℝ) else 1) :=
        sum_nonneg fun κ' _ => by split_ifs <;> norm_num
      by_cases hg : X.good er
      swap
      · rw [if_neg hg, if_neg hg]; linarith
      rw [if_pos hg, if_pos hg, zero_add]
      by_cases hh : X.heavy π lam er κ
      swap
      · -- a light chosen atom: the failure term is at least one
        have h1 : (1 : ℝ) ≤ ∑ κ' : Bool, (if X.heavy π lam er κ' then (0 : ℝ) else 1) := by
          rw [← add_sum_erase (s := univ) (a := κ) _ (mem_univ κ), if_neg hh]
          have : 0 ≤ ∑ κ' ∈ univ.erase κ, (if X.heavy π lam er κ' then (0 : ℝ) else 1) :=
            sum_nonneg fun κ' _ => by split_ifs <;> norm_num
          linarith
        have h2 : ∀ e', condKey X.P (X.armKey κ) er e' *
            (if X.heavy π lam er κ ∧ sepOK n path e' ∧ Q e₀ (path ++ [(er, κ, e')])
              then X.pathValue π lam χ sepOK Q τ n e₀ (path ++ [(er, κ, e')]) else 0) = 0 := by
          intro e'; rw [if_neg (fun h => hh h.1), mul_zero]
        rw [sum_congr rfl fun e' _ => h2 e', sum_const_zero]
        linarith
      -- a heavy chosen atom
      have hsumT : ∑ e', condKey X.P (X.armKey κ) er e' = 1 :=
        sum_condKey_eq_one_of_pos hP _ hper
      have hterm : ∀ e', condKey X.P (X.armKey κ) er e' *
          (1 - (if sepOK n path e' then 0 else 1) - X.failBound π lam s n e')
          ≤ condKey X.P (X.armKey κ) er e' *
            (if X.heavy π lam er κ ∧ sepOK n path e' ∧ Q e₀ (path ++ [(er, κ, e')])
              then X.pathValue π lam χ sepOK Q τ n e₀ (path ++ [(er, κ, e')]) else 0) := by
        intro e'
        by_cases ht : condKey X.P X.fine e er = 0
        · exact absurd ht hr
        by_cases hte : condKey X.P (X.armKey κ) er e' = 0
        · simp [hte]
        refine mul_le_mul_of_nonneg_left ?_ (condKey_nonneg hP _ _ _)
        by_cases hsp : sepOK n path e'
        · have hQ' : Q e₀ (path ++ [(er, κ, e')]) :=
            hQ n path er e' (by omega) hQp hr hg hte hh hsp
          rw [if_pos hsp, if_pos ⟨hh, hsp, hQ'⟩]
          have hpos' : 0 < X.P (curEvent e₀ (path ++ [(er, κ, e')])) := by
            rw [curEvent_append]; exact condKey_pos_of_ne hP _ hte
          have := ih (path ++ [(er, κ, e')])
            (by simp only [List.length_append, List.length_singleton]; omega) hQ' hpos'
          rw [curEvent_append] at this
          linarith
        · rw [if_neg hsp, if_neg (fun h => hsp h.2.1)]
          linarith [hG0 n e']
      have hlow := sum_le_sum fun e' (_ : e' ∈ univ) => hterm e'
      have hsplit : ∑ e', condKey X.P (X.armKey κ) er e' *
          (1 - (if sepOK n path e' then 0 else 1) - X.failBound π lam s n e')
          = ∑ e', condKey X.P (X.armKey κ) er e'
            - ∑ e', condKey X.P (X.armKey κ) er e' * (if sepOK n path e' then 0 else 1)
            - ∑ e', condKey X.P (X.armKey κ) er e' * X.failBound π lam s n e' := by
        rw [← sum_sub_distrib, ← sum_sub_distrib]
        refine sum_congr rfl fun e' _ => ?_
        ring
      rw [hsplit, hsumT] at hlow
      have hsep' := hsep n path er κ (by omega) hh
      have hone : ∑ e', condKey X.P (X.armKey κ) er e' * X.failBound π lam s n e'
          ≤ ∑ κ' : Bool, ∑ e', condKey X.P (X.armKey κ') er e' * X.failBound π lam s n e' :=
        single_le_sum (f := fun κ' => ∑ e', condKey X.P (X.armKey κ') er e' *
            X.failBound π lam s n e')
          (fun κ' _ => sum_nonneg fun e' _ => mul_nonneg (condKey_nonneg hP _ _ _) (hG0 n e'))
          (mem_univ κ)
      linarith
    have := sum_le_sum fun er (_ : er ∈ univ) => key er
    rw [sum_sub_distrib, ← sum_mul, hsum1, one_mul] at this
    exact this

/-- **Average failure bound.** For a starting law dominated by `C₀ P`, the averaged failure
bound is at most `C₀ (2^n - 1) Xbad`, where `Xbad` is the bad palette mass plus the light
atom masses of both colours plus `s`. -/
theorem SwitchData.sum_mul_failBound_le (hP : ∀ ω, 0 ≤ X.P ω) (hP1 : ∑ ω, X.P ω = 1)
    (π : Bool → Ar → ℝ) (lam : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ∀ n (ρ₀ : Ω → ℝ) (C₀ : ℝ), 0 ≤ C₀ → (∀ ω, 0 ≤ ρ₀ ω) → (∀ ω, ρ₀ ω ≤ C₀ * X.P ω) →
      ∑ e, ρ₀ e * X.failBound π lam s n e
        ≤ C₀ * (2 ^ n - 1) * (∑ er, X.P er * ((if X.good er then 0 else 1) +
            ∑ κ : Bool, (if X.heavy π lam er κ then 0 else 1)) + s) := by
  have hG0 := X.failBound_nonneg hP π lam hs
  set Xb := ∑ er, X.P er * ((if X.good er then (0 : ℝ) else 1) +
      ∑ κ : Bool, (if X.heavy π lam er κ then 0 else 1)) + s with hXb
  have hXb0 : 0 ≤ Xb := add_nonneg (sum_nonneg fun er _ => mul_nonneg (hP er)
    (add_nonneg (by split_ifs <;> norm_num) (sum_nonneg fun κ _ => by split_ifs <;> norm_num))) hs
  intro n
  induction n with
  | zero => intro ρ₀ C₀ _ _ _; simp [SwitchData.failBound]
  | succ n ih =>
    intro ρ₀ C₀ hC₀ hρ0 hρ
    -- the refreshed law
    set ρt : Ω → ℝ := fun er => ∑ e, ρ₀ e * condKey X.P X.fine e er with hρt
    have hρt0 : ∀ er, 0 ≤ ρt er := fun er =>
      sum_nonneg fun e _ => mul_nonneg (hρ0 e) (condKey_nonneg hP _ _ _)
    have hρtC : ∀ er, ρt er ≤ C₀ * X.P er := sum_mul_condKey_le hP X.fine hρ
    -- the law after a traversal of either colour
    set ρ₁ : Ω → ℝ := fun e' => ∑ er, ρt er * ∑ κ : Bool, condKey X.P (X.armKey κ) er e'
      with hρ₁
    have hρ₁0 : ∀ e', 0 ≤ ρ₁ e' := fun e' => sum_nonneg fun er _ => mul_nonneg (hρt0 er)
      (sum_nonneg fun κ _ => condKey_nonneg hP _ _ _)
    have hρ₁C : ∀ e', ρ₁ e' ≤ (2 * C₀) * X.P e' := by
      intro e'
      calc ρ₁ e' = ∑ κ : Bool, ∑ er, ρt er * condKey X.P (X.armKey κ) er e' := by
            simp only [hρ₁, mul_sum]; rw [sum_comm]
        _ ≤ ∑ κ : Bool, C₀ * X.P e' :=
            sum_le_sum fun κ _ => sum_mul_condKey_le hP (X.armKey κ) hρtC e'
        _ = (2 * C₀) * X.P e' := by rw [Fintype.sum_bool]; ring
    have hrec := ih ρ₁ (2 * C₀) (by linarith) hρ₁0 hρ₁C
    -- unfold one step
    have fub : ∀ (ρ : Ω → ℝ) (H : Ω → ℝ),
        ∑ e, ρ e * ∑ er, condKey X.P X.fine e er * H er
          = ∑ er, (∑ e, ρ e * condKey X.P X.fine e er) * H er := by
      intro ρ H
      simp only [mul_sum, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun er _ => sum_congr rfl fun e _ => by ring
    have fub2 : ∑ er, ρt er * ∑ κ : Bool, ∑ e', condKey X.P (X.armKey κ) er e' *
          X.failBound π lam s n e'
        = ∑ e', ρ₁ e' * X.failBound π lam s n e' := by
      calc ∑ er, ρt er * ∑ κ : Bool, ∑ e', condKey X.P (X.armKey κ) er e' *
            X.failBound π lam s n e'
          = ∑ er, ∑ κ : Bool, ∑ e', ρt er * condKey X.P (X.armKey κ) er e' *
              X.failBound π lam s n e' := by
            refine sum_congr rfl fun er _ => ?_
            rw [mul_sum]
            refine sum_congr rfl fun κ _ => ?_
            rw [mul_sum]
            exact sum_congr rfl fun e' _ => by ring
        _ = ∑ κ : Bool, ∑ er, ∑ e', ρt er * condKey X.P (X.armKey κ) er e' *
              X.failBound π lam s n e' := sum_comm
        _ = ∑ κ : Bool, ∑ e', ∑ er, ρt er * condKey X.P (X.armKey κ) er e' *
              X.failBound π lam s n e' := sum_congr rfl fun κ _ => sum_comm
        _ = ∑ e', ∑ κ : Bool, ∑ er, ρt er * condKey X.P (X.armKey κ) er e' *
              X.failBound π lam s n e' := sum_comm
        _ = ∑ e', ∑ er, ∑ κ : Bool, ρt er * condKey X.P (X.armKey κ) er e' *
              X.failBound π lam s n e' := sum_congr rfl fun e' _ => sum_comm
        _ = ∑ e', ρ₁ e' * X.failBound π lam s n e' := by
            refine sum_congr rfl fun e' _ => ?_
            rw [hρ₁, sum_mul]
            refine sum_congr rfl fun er _ => ?_
            rw [mul_sum, sum_mul]
    have e1 : ∑ e, ρ₀ e * X.failBound π lam s (n + 1) e
        = ∑ er, ρt er * ((if X.good er then 0 else 1) +
            ∑ κ : Bool, (if X.heavy π lam er κ then 0 else 1) + s)
          + ∑ e', ρ₁ e' * X.failBound π lam s n e' := by
      simp only [SwitchData.failBound]
      rw [fub, ← fub2, ← sum_add_distrib]
      exact sum_congr rfl fun er _ => by rw [hρt]; ring
    rw [e1]
    have hA : ∑ er, ρt er * ((if X.good er then 0 else 1) +
          ∑ κ : Bool, (if X.heavy π lam er κ then 0 else 1) + s) ≤ C₀ * Xb := by
      have hsumρt : ∑ er, ρt er ≤ C₀ := by
        calc ∑ er, ρt er ≤ ∑ er, C₀ * X.P er := sum_le_sum fun er _ => hρtC er
          _ = C₀ := by rw [← mul_sum, hP1, mul_one]
      calc ∑ er, ρt er * ((if X.good er then 0 else 1) +
            ∑ κ : Bool, (if X.heavy π lam er κ then 0 else 1) + s)
          = ∑ er, ρt er * ((if X.good er then 0 else 1) +
              ∑ κ : Bool, (if X.heavy π lam er κ then 0 else 1)) + s * ∑ er, ρt er := by
            rw [mul_sum, ← sum_add_distrib]
            exact sum_congr rfl fun er _ => by ring
        _ ≤ ∑ er, C₀ * X.P er * ((if X.good er then 0 else 1) +
              ∑ κ : Bool, (if X.heavy π lam er κ then 0 else 1)) + s * C₀ := by
            refine add_le_add (sum_le_sum fun er _ => ?_) (mul_le_mul_of_nonneg_left hsumρt hs)
            exact mul_le_mul_of_nonneg_right (hρtC er)
              (add_nonneg (by split_ifs <;> norm_num) (sum_nonneg fun κ _ => by
                split_ifs <;> norm_num))
        _ = C₀ * Xb := by
            rw [hXb, mul_add, mul_sum]
            congr 1
            · exact sum_congr rfl fun er _ => by ring
            · ring
    have h2 : (2 : ℝ) ^ (n + 1) - 1 = 1 + 2 * (2 ^ n - 1) := by ring
    rw [h2]
    nlinarith [hrec, hA]

/-- **Success lower bound, averaged over starts.** -/
theorem SwitchData.one_sub_le_sum_pathValue (hP : ∀ ω, 0 ≤ X.P ω) (hP1 : ∑ ω, X.P ω = 1)
    (π : Bool → Ar → ℝ) (lam : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (χ : Ω → List (Ω × Bool × Ω) → Ω → Bool) (sepOK : ℕ → List (Ω × Bool × Ω) → Ω → Prop)
    (Q : Ω → List (Ω × Bool × Ω) → Prop) (τ : Ω → List (Ω × Bool × Ω) → ℝ) (n : ℕ)
    (hQ0 : ∀ e₀, 0 < X.P e₀ → Q e₀ [])
    (hτ1 : ∀ e₀ path, path.length ≤ n → Q e₀ path → 1 ≤ τ e₀ path)
    (hQ : ∀ e₀ n' path er e', path.length + n' + 1 ≤ n → Q e₀ path →
      condKey X.P X.fine (curEvent e₀ path) er ≠ 0 →
      X.good er → condKey X.P (X.armKey (χ e₀ path er)) er e' ≠ 0 →
      X.heavy π lam er (χ e₀ path er) → sepOK n' path e' →
      Q e₀ (path ++ [(er, χ e₀ path er, e')]))
    (hsep : ∀ n' path er κ, path.length + n' + 1 ≤ n → X.heavy π lam er κ →
      ∑ e', condKey X.P (X.armKey κ) er e' * (if sepOK n' path e' then 0 else 1) ≤ s) :
    1 - (2 ^ n - 1) * (∑ er, X.P er * ((if X.good er then 0 else 1) +
        ∑ κ : Bool, (if X.heavy π lam er κ then 0 else 1)) + s)
      ≤ ∑ e₀, X.P e₀ * X.pathValue π lam χ sepOK Q τ n e₀ [] := by
  have havg := X.sum_mul_failBound_le hP hP1 π lam hs n X.P 1 zero_le_one hP
    (fun ω => by rw [one_mul])
  rw [one_mul] at havg
  have hterm : ∀ e₀, X.P e₀ * (1 - X.failBound π lam s n e₀)
      ≤ X.P e₀ * X.pathValue π lam χ sepOK Q τ n e₀ [] := by
    intro e₀
    rcases (hP e₀).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (hP e₀)
      have := X.one_sub_failBound_le_pathValue hP π lam hs χ sepOK Q τ e₀ n (hτ1 e₀)
        (hQ e₀) hsep n [] (by simp) (hQ0 e₀ h0) (by simpa using h0)
      simpa using this
  calc 1 - (2 ^ n - 1) * (∑ er, X.P er * ((if X.good er then 0 else 1) +
          ∑ κ : Bool, (if X.heavy π lam er κ then 0 else 1)) + s)
      ≤ 1 - ∑ e, X.P e * X.failBound π lam s n e := by linarith
    _ = ∑ e₀, X.P e₀ * (1 - X.failBound π lam s n e₀) := by
        simp only [mul_sub, mul_one, sum_sub_distrib, hP1]
    _ ≤ ∑ e₀, X.P e₀ * X.pathValue π lam χ sepOK Q τ n e₀ [] := sum_le_sum fun e₀ _ => hterm e₀

/-- The coarse palette law sums to at most one. -/
lemma SwitchData.sum_condPal_le_one (hP : ∀ ω, 0 ≤ X.P ω) (x : Sc) :
    ∑ z ∈ univ.image X.Z, X.condPal x z ≤ 1 := by
  unfold SwitchData.condPal
  rw [← sum_div]
  have hsum : ∑ z ∈ univ.image X.Z, fiberMass X.P (fun ω => (X.coarse ω, X.Z ω)) (x, z)
      = fiberMass X.P X.coarse x := by
    unfold fiberMass
    rw [← sum_fiberwise_of_maps_to (s := univ.filter fun ω => X.coarse ω = x)
      (t := univ.image X.Z) (g := X.Z) (fun ω _ => mem_image_of_mem X.Z (mem_univ ω))]
    refine sum_congr rfl fun z _ => ?_
    rw [filter_filter]
    congr 1
  rw [hsum]
  exact div_self_le_one _

/-- **The free iterated bound against a supersolution.** If `Bd` dominates the terminal
test and every one-step time-cell sum over the controls of the neighbour states, then the
free bound with step factor `c` is at most `(c * (2 * #Nbr))^n * Bd n l`. -/
theorem SwitchData.freeBound_le (hP : ∀ ω, 0 ≤ X.P ω) {c : ℝ} (hc : 0 ≤ c) (Nbr : Finset Sc)
    (τ' : List (ℝ × Tc) → ℝ) (Bd : ℕ → List (ℝ × Tc) → ℝ) (hBd0 : ∀ n l, 0 ≤ Bd n l)
    (hτ' : ∀ l, τ' l ≤ Bd 0 l)
    (hstep : ∀ n l, ∀ x ∈ Nbr, ∀ κ : Bool, ∀ z ∈ univ.image X.Z,
      ∑ t : Tc, Bd n (l ++ [(X.Ψ z x κ, t)]) ≤ Bd (n + 1) l) :
    ∀ n l, X.freeBound c Nbr τ' n l ≤ (c * (2 * Nbr.card)) ^ n * Bd n l := by
  intro n
  induction n with
  | zero => intro l; simpa [SwitchData.freeBound] using hτ' l
  | succ n ih =>
    intro l
    simp only [SwitchData.freeBound]
    have hcn : 0 ≤ (c * (2 * Nbr.card)) ^ n :=
      pow_nonneg (mul_nonneg hc (by positivity)) n
    calc c * ∑ x ∈ Nbr, ∑ κ : Bool, ∑ z ∈ univ.image X.Z, X.condPal x z *
          ∑ t : Tc, X.freeBound c Nbr τ' n (l ++ [(X.Ψ z x κ, t)])
        ≤ c * ∑ x ∈ Nbr, ∑ κ : Bool, ∑ z ∈ univ.image X.Z, X.condPal x z *
            ((c * (2 * Nbr.card)) ^ n * Bd (n + 1) l) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun x hx => sum_le_sum fun κ _ =>
            sum_le_sum fun z hz => ?_) hc
          refine mul_le_mul_of_nonneg_left ?_ (X.condPal_nonneg hP x z)
          calc ∑ t : Tc, X.freeBound c Nbr τ' n (l ++ [(X.Ψ z x κ, t)])
              ≤ ∑ t : Tc, (c * (2 * Nbr.card)) ^ n * Bd n (l ++ [(X.Ψ z x κ, t)]) :=
                sum_le_sum fun t _ => ih _
            _ = (c * (2 * Nbr.card)) ^ n * ∑ t : Tc, Bd n (l ++ [(X.Ψ z x κ, t)]) := by
                rw [mul_sum]
            _ ≤ (c * (2 * Nbr.card)) ^ n * Bd (n + 1) l :=
                mul_le_mul_of_nonneg_left (hstep n l x hx κ z hz) hcn
      _ = c * ((c * (2 * Nbr.card)) ^ n * Bd (n + 1) l) *
            ∑ x ∈ Nbr, ∑ κ : Bool, ∑ z ∈ univ.image X.Z, X.condPal x z := by
          simp only [mul_sum]
          refine sum_congr rfl fun x _ => sum_congr rfl fun κ _ => sum_congr rfl fun z _ => ?_
          ring
      _ ≤ c * ((c * (2 * Nbr.card)) ^ n * Bd (n + 1) l) * ∑ x ∈ Nbr, ∑ κ : Bool, (1 : ℝ) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => sum_le_sum fun κ _ =>
            X.sum_condPal_le_one hP x) (mul_nonneg hc (mul_nonneg hcn (hBd0 _ _)))
      _ = (c * (2 * Nbr.card)) ^ (n + 1) * Bd (n + 1) l := by
          simp only [sum_const, card_univ, Fintype.card_bool, nsmul_eq_mul]
          ring

/-- The control indices of the free bound: a neighbour state, a colour and a palette value. -/
def SwitchData.ctrlIdx (Nbr : Finset Sc) : Finset (Sc × Bool × Pal) :=
  Nbr ×ˢ ((univ : Finset Bool) ×ˢ univ.image X.Z)

/-- The control of an index. -/
def SwitchData.idxCtrl (c : Sc × Bool × Pal) : ℝ := X.Ψ c.2.2 c.1 c.2.1

/-- The weight of an index: its coarse palette probability. -/
noncomputable def SwitchData.idxWeight (c : Sc × Bool × Pal) : ℝ := X.condPal c.1 c.2.2

/-- The time-cell sum of the terminal test along fixed controls. -/
noncomputable def timeSum (τ' : List (ℝ × Tc) → ℝ) (l : List (ℝ × Tc)) {n : ℕ}
    (us : Fin n → ℝ) : ℝ :=
  ∑ ts : Fin n → Tc, τ' (l ++ List.ofFn fun i => (us i, ts i))

lemma sum_fin_succ_fun {α M : Type*} [Fintype α] [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n + 1) → α) → M) :
    ∑ p, f p = ∑ a, ∑ p' : Fin n → α, f (Fin.cons a p') := by
  rw [← Fintype.sum_prod_type' (fun a (p' : Fin n → α) => f (Fin.cons a p'))]
  exact (Equiv.sum_comp (Fin.consEquiv fun _ => α) f).symm

lemma timeSum_cons (τ' : List (ℝ × Tc) → ℝ) (l : List (ℝ × Tc)) {n : ℕ} (u₀ : ℝ)
    (us : Fin n → ℝ) :
    timeSum τ' l (Fin.cons u₀ us : Fin (n + 1) → ℝ)
      = ∑ t : Tc, timeSum τ' (l ++ [(u₀, t)]) us := by
  unfold timeSum
  rw [sum_fin_succ_fun]
  refine sum_congr rfl fun t _ => sum_congr rfl fun ts' _ => ?_
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.append_assoc,
    List.singleton_append]

/-- **Unfolding the free bound.** Since nothing but the terminal test depends on the time
cells, the free bound is `c^n` times a weighted sum over control-index tuples of the
time-cell sums along their controls. -/
theorem SwitchData.freeBound_eq_sum (c : ℝ) (Nbr : Finset Sc) (τ' : List (ℝ × Tc) → ℝ) :
    ∀ n l, X.freeBound c Nbr τ' n l
      = c ^ n * ∑ cs : Fin n → X.ctrlIdx Nbr, (∏ i, X.idxWeight (cs i)) *
          timeSum τ' l (fun i => X.idxCtrl (cs i)) := by
  intro n
  induction n with
  | zero =>
    intro l
    simp [SwitchData.freeBound, timeSum]
  | succ n ih =>
    intro l
    -- the triple sum over indices as a sum over the index subtype
    have htriple : ∀ G : Sc × Bool × Pal → ℝ,
        ∑ x ∈ Nbr, ∑ κ : Bool, ∑ z ∈ univ.image X.Z, G (x, κ, z)
          = ∑ ci : X.ctrlIdx Nbr, G ci := by
      intro G
      rw [Finset.sum_coe_sort (X.ctrlIdx Nbr) G, SwitchData.ctrlIdx, sum_product]
      refine sum_congr rfl fun x _ => ?_
      rw [sum_product]
    have e1 := htriple (fun ci => X.idxWeight ci *
      ∑ t : Tc, X.freeBound c Nbr τ' n (l ++ [(X.idxCtrl ci, t)]))
    calc X.freeBound c Nbr τ' (n + 1) l
        = c * ∑ ci : X.ctrlIdx Nbr, X.idxWeight ci *
            ∑ t : Tc, X.freeBound c Nbr τ' n (l ++ [(X.idxCtrl ci, t)]) := by
          simp only [SwitchData.freeBound]
          rw [← e1]
          simp only [SwitchData.idxWeight, SwitchData.idxCtrl]
      _ = ∑ ci : X.ctrlIdx Nbr, ∑ cs' : Fin n → X.ctrlIdx Nbr,
            c ^ (n + 1) * ((X.idxWeight ci * ∏ i, X.idxWeight (cs' i)) *
              ∑ t : Tc, timeSum τ' (l ++ [(X.idxCtrl ci, t)]) fun i => X.idxCtrl (cs' i)) := by
          rw [mul_sum]
          refine sum_congr rfl fun ci _ => ?_
          simp only [ih]
          have hswap : ∑ t : Tc, c ^ n * ∑ cs' : Fin n → X.ctrlIdx Nbr,
              (∏ i, X.idxWeight (cs' i)) *
                timeSum τ' (l ++ [(X.idxCtrl ci, t)]) (fun i => X.idxCtrl (cs' i))
              = c ^ n * ∑ cs' : Fin n → X.ctrlIdx Nbr, (∏ i, X.idxWeight (cs' i)) *
                  ∑ t : Tc, timeSum τ' (l ++ [(X.idxCtrl ci, t)]) (fun i => X.idxCtrl (cs' i)) := by
            rw [← mul_sum, sum_comm]
            congr 1
            refine sum_congr rfl fun cs' _ => ?_
            rw [mul_sum]
          rw [hswap]
          simp only [mul_sum]
          refine sum_congr rfl fun cs' _ => sum_congr rfl fun t _ => ?_
          ring
      _ = c ^ (n + 1) * ∑ cs : Fin (n + 1) → X.ctrlIdx Nbr, (∏ i, X.idxWeight (cs i)) *
            timeSum τ' l (fun i => X.idxCtrl (cs i)) := by
          conv_rhs => rw [mul_sum, sum_fin_succ_fun]
          refine sum_congr rfl fun ci _ => sum_congr rfl fun cs' _ => ?_
          have hc : (fun i : Fin (n + 1) => X.idxCtrl ((Fin.cons ci cs' : Fin (n + 1) → _) i))
              = Fin.cons (X.idxCtrl ci) (fun i => X.idxCtrl (cs' i)) := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp only [Fin.cons_zero]
            · simp only [Fin.cons_succ]
          rw [hc, timeSum_cons, Fin.prod_univ_succ, Fin.cons_zero]
          simp only [Fin.cons_succ]

/-- The index weights sum to at most `2 #Nbr`. -/
lemma SwitchData.sum_idxWeight_le (hP : ∀ ω, 0 ≤ X.P ω) (Nbr : Finset Sc) :
    ∑ ci : X.ctrlIdx Nbr, X.idxWeight ci ≤ 2 * Nbr.card := by
  have e : ∑ ci : X.ctrlIdx Nbr, X.idxWeight ci = ∑ c ∈ X.ctrlIdx Nbr, X.idxWeight c :=
    Finset.sum_coe_sort (X.ctrlIdx Nbr) X.idxWeight
  rw [e, SwitchData.ctrlIdx, sum_product]
  have h2 : ∀ x ∈ Nbr, ∑ y ∈ (univ : Finset Bool) ×ˢ univ.image X.Z, X.idxWeight (x, y) ≤ 2 := by
    intro x _
    rw [sum_product]
    calc ∑ κ : Bool, ∑ z ∈ univ.image X.Z, X.idxWeight (x, κ, z)
        ≤ ∑ κ : Bool, (1 : ℝ) := sum_le_sum fun κ _ => X.sum_condPal_le_one hP x
      _ = 2 := by rw [sum_const, card_univ, Fintype.card_bool]; norm_num
  calc ∑ x ∈ Nbr, ∑ y ∈ (univ : Finset Bool) ×ˢ univ.image X.Z, X.idxWeight (x, y)
      ≤ ∑ x ∈ Nbr, (2 : ℝ) := sum_le_sum h2
    _ = 2 * Nbr.card := by rw [sum_const, nsmul_eq_mul, mul_comm]

/-- The index weights of a tuple sum to at most `(2 #Nbr)^n`. -/
lemma SwitchData.sum_prod_idxWeight_le (hP : ∀ ω, 0 ≤ X.P ω) (Nbr : Finset Sc) (n : ℕ) :
    ∑ cs : Fin n → X.ctrlIdx Nbr, ∏ i, X.idxWeight (cs i) ≤ (2 * Nbr.card) ^ n := by
  have h0 : 0 ≤ ∑ ci : X.ctrlIdx Nbr, X.idxWeight ci :=
    sum_nonneg fun ci _ => X.condPal_nonneg hP _ _
  have hpow := Fintype.sum_pow (fun ci : X.ctrlIdx Nbr => X.idxWeight ci) n
  rw [← hpow]
  exact pow_le_pow_left₀ h0 (X.sum_idxWeight_le hP Nbr) n

end Switching


section Markov

variable {ι Ω : Type*} [Fintype Ω]

/-- **Bad steps are few.** If the positive parts of step log-likelihood ratios have total
expectation at most `B`, then the number of steps whose bad mass `{θ < X a}` exceeds `ρ`
is at most `B / (θ ρ)`. -/
theorem card_bad_steps_mul_le (s : Finset ι) (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (X : ι → Ω → ℝ) {B θ ρ : ℝ} (hθ : 0 < θ)
    (hB : ∑ a ∈ s, ∑ x, p x * max 0 (X a x) ≤ B) :
    ((s.filter fun a => ρ < ∑ x ∈ univ.filter (fun x => θ < X a x), p x).card : ℝ) * (θ * ρ)
      ≤ B := by
  classical
  have hmarkov : ∀ a, (∑ x ∈ univ.filter (fun x => θ < X a x), p x) * θ
      ≤ ∑ x, p x * max 0 (X a x) := by
    intro a
    rw [sum_mul]
    calc ∑ x ∈ univ.filter (fun x => θ < X a x), p x * θ
        ≤ ∑ x ∈ univ.filter (fun x => θ < X a x), p x * max 0 (X a x) := by
          refine sum_le_sum fun x hx => ?_
          rw [mem_filter] at hx
          exact mul_le_mul_of_nonneg_left (le_max_of_le_right hx.2.le) (hp x)
      _ ≤ ∑ x, p x * max 0 (X a x) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ =>
            mul_nonneg (hp x) (le_max_left _ _)
  have hnn : ∀ a, 0 ≤ ∑ x, p x * max 0 (X a x) := fun a =>
    sum_nonneg fun x _ => mul_nonneg (hp x) (le_max_left _ _)
  calc ((s.filter fun a => ρ < ∑ x ∈ univ.filter (fun x => θ < X a x), p x).card : ℝ) *
        (θ * ρ)
      = ∑ a ∈ s.filter (fun a => ρ < ∑ x ∈ univ.filter (fun x => θ < X a x), p x),
          ρ * θ := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ a ∈ s.filter (fun a => ρ < ∑ x ∈ univ.filter (fun x => θ < X a x), p x),
          (∑ x ∈ univ.filter (fun x => θ < X a x), p x) * θ := by
        refine sum_le_sum fun a ha => ?_
        rw [mem_filter] at ha
        exact mul_le_mul_of_nonneg_right ha.2.le hθ.le
    _ ≤ ∑ a ∈ s.filter (fun a => ρ < ∑ x ∈ univ.filter (fun x => θ < X a x), p x),
          ∑ x, p x * max 0 (X a x) := sum_le_sum fun a _ => hmarkov a
    _ ≤ ∑ a ∈ s, ∑ x, p x * max 0 (X a x) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ => hnn a
    _ ≤ B := hB

end Markov







end Submission.Obl.k4_matching_abstract_switching_mixture.Finite
