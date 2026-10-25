import Mathlib
import Submission.Obl.k4_matching_abstract_switching_mixture.FiniteModel
import Submission.Obl.k4_matching_abstract_switching_mixture.Estimates

/-!
# The switching data of the finite model

`D.sw G Ψ θ` is the finite switching experiment (`Finite.SwitchData`) on the depth-`G`
model of `D : Data n₁ n₂`: weights `D.wt G`, fine/coarse records and palette of the
representatives, arms `Sum.inl` (first index, colour `true`) and `Sum.inr` (second index,
colour `false`) and the level-`H` interval in `Fin (2^H)`, all read off the representative,
and the cell itself as time cell.  The control map `Ψ` and the log-threshold `θ` are
parameters.  Since arms and intervals are those of the representatives (which lie in `S` for
every cell, of positive weight or not), a legal step between any two cells is a legal step of
the frozen path clause between their representatives (`armKey_eq_iff`, `ival_eq_of_fine_eq`);
on cells of positive weight they agree with the cell's own indices (`armRep_of_pos`,
`ivalRep_of_pos`).

The hypotheses of the general switching theorems hold on it:
* `sw_cell`: arm/time-cell fibres have weight at most `prior κ a * (B / 2^G)`;
* `sw_coarse`: the coarse record is a function of the fine one;
* `sw_bad_le`: the bad palette mass is at most the frozen exceptional mass;
* `sw_light_le`: light atoms of either colour have mass at most `2^H * lam`;
* `sw_near_le`: within one arm atom, cells whose representative's normalized time is within
  `r` of `t₀` have weight at most `prior κ a * (2 B (r / 2^H + 1 / 2^G))`.
-/

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open MeasureTheory Finset
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {n₁ n₂ : ℕ}

/-- The arm of colour `κ` of an event: its first index for `true`, its second for `false`. -/
def armOfEv (e : Ev n₁ n₂) (κ : Bool) : Fin n₁ ⊕ Fin n₂ :=
  if κ then Sum.inl e.1.1 else Sum.inr e.1.2

/-- The level-`H` interval index of a time (reduced mod `2^H`, exact on `[0, 1)`). -/
noncomputable def ivalOfTime (H : ℕ) (t : ℝ) : Fin (2 ^ H) :=
  ⟨⌊t * (2 : ℝ) ^ H⌋₊ % 2 ^ H, Nat.mod_lt _ (by positivity)⟩

lemma ivalOfTime_val {H : ℕ} {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ((ivalOfTime H t : Fin (2 ^ H)) : ℕ) = ⌊t * (2 : ℝ) ^ H⌋₊ := by
  unfold ivalOfTime
  simp only
  apply Nat.mod_eq_of_lt
  have h2 : (0 : ℝ) < 2 ^ H := by positivity
  rw [Nat.floor_lt (mul_nonneg ht.1 h2.le)]
  push_cast
  calc t * 2 ^ H < 1 * 2 ^ H := mul_lt_mul_of_pos_right ht.2 h2
    _ = 2 ^ H := one_mul _

lemma ivalOfTime_eq_iff {H : ℕ} {s t : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ivalOfTime H s = ivalOfTime H t ↔
      Int.floor (s * (2 : ℝ) ^ H) = Int.floor (t * (2 : ℝ) ^ H) := by
  have h2 : (0 : ℝ) ≤ 2 ^ H := by positivity
  rw [Fin.ext_iff, ivalOfTime_val hs, ivalOfTime_val ht,
    ← Int.natCast_floor_eq_floor (mul_nonneg hs.1 h2),
    ← Int.natCast_floor_eq_floor (mul_nonneg ht.1 h2)]
  exact ⟨fun h => by rw [h], fun h => by exact_mod_cast h⟩

namespace Data

variable (D : Data n₁ n₂)

/-- The prior of an arm of colour `κ` (zero on arms of the other colour). -/
noncomputable def prior : Bool → Fin n₁ ⊕ Fin n₂ → ℝ
  | true, Sum.inl i => D.π₁ i
  | false, Sum.inr i => D.π₂ i
  | _, _ => 0

lemma prior_nonneg (κ : Bool) (a : Fin n₁ ⊕ Fin n₂) : 0 ≤ D.prior κ a := by
  cases κ <;> cases a <;> simp [prior, D.hπ₁, D.hπ₂]

lemma sum_prior (κ : Bool) : ∑ a, D.prior κ a = 1 := by
  cases κ
  · simp [prior, Fintype.sum_sum_type, D.hs₂]
  · simp [prior, Fintype.sum_sum_type, D.hs₁]

/-- The arm of colour `κ` of a cell, read off its representative. -/
noncomputable def armRep (G : ℕ) (ω : Om n₁ n₂ G) (κ : Bool) : Fin n₁ ⊕ Fin n₂ :=
  armOfEv (D.rep G ω) κ

/-- The level-`H` interval of a cell, read off its representative. -/
noncomputable def ivalRep (G : ℕ) (ω : Om n₁ n₂ G) : Fin (2 ^ D.H) :=
  ivalOfTime D.H (D.rep G ω).2

/-- The switching data of the depth-`G` model with control map `Ψ` and log-threshold `θ`. -/
noncomputable def sw (G : ℕ) (Ψ : ℤ × ℤ → ℕ → Bool → ℝ) (θ : ℝ) :
    SwitchData (Om n₁ n₂ G) ℕ ℕ (Fin n₁ ⊕ Fin n₂) (Fin (2 ^ D.H)) (ℤ × ℤ) (Fin (2 ^ G)) where
  P := D.wt G
  fine := D.fine G
  coarse := D.coarse G
  Z := D.pal G
  arm := D.armRep G
  ival := D.ivalRep G
  cell := fun ω => ω.2.2
  Ψ := Ψ
  θ := θ

variable (G : ℕ) (Ψ : ℤ × ℤ → ℕ → Bool → ℝ) (θ : ℝ)

@[simp] lemma sw_P : (D.sw G Ψ θ).P = D.wt G := rfl
@[simp] lemma sw_fine : (D.sw G Ψ θ).fine = D.fine G := rfl
@[simp] lemma sw_coarse_eq : (D.sw G Ψ θ).coarse = D.coarse G := rfl
@[simp] lemma sw_Z : (D.sw G Ψ θ).Z = D.pal G := rfl
@[simp] lemma sw_arm (ω : Om n₁ n₂ G) (κ : Bool) : (D.sw G Ψ θ).arm ω κ = D.armRep G ω κ := rfl
@[simp] lemma sw_ival (ω : Om n₁ n₂ G) : (D.sw G Ψ θ).ival ω = D.ivalRep G ω := rfl
@[simp] lemma sw_cell_eq (ω : Om n₁ n₂ G) : (D.sw G Ψ θ).cell ω = ω.2.2 := rfl
@[simp] lemma sw_Ψ : (D.sw G Ψ θ).Ψ = Ψ := rfl
@[simp] lemma sw_θ : (D.sw G Ψ θ).θ = θ := rfl

lemma sw_ctrl (ω : Om n₁ n₂ G) (κ : Bool) :
    (D.sw G Ψ θ).ctrl ω κ = Ψ (D.pal G ω) (D.coarse G ω) κ := rfl

lemma sw_P_nonneg (ω : Om n₁ n₂ G) : 0 ≤ (D.sw G Ψ θ).P ω := D.wt_nonneg G ω

lemma sw_sum_P : ∑ ω, (D.sw G Ψ θ).P ω = 1 := D.sum_wt G

/-- The coarse record is a function of the fine record. -/
lemma sw_coarse : ∃ g : ℕ → ℕ, ∀ ω, (D.sw G Ψ θ).coarse ω = g ((D.sw G Ψ θ).fine ω) :=
  D.coarse_of_fine G

/-- The arm of colour `κ` of a cell, read off the cell's own indices. -/
def armIdx {G : ℕ} (ω : Om n₁ n₂ G) (κ : Bool) : Fin n₁ ⊕ Fin n₂ :=
  if κ then Sum.inl ω.1 else Sum.inr ω.2.1

/-- On a cell of positive weight the representative's arm is the cell's arm. -/
lemma armRep_of_pos {G : ℕ} {ω : Om n₁ n₂ G} (hω : 0 < D.wt G ω) (κ : Bool) :
    D.armRep G ω κ = armIdx ω κ := by
  cases κ
  · simp [armRep, armOfEv, armIdx, D.rep_fst_snd G hω]
  · simp [armRep, armOfEv, armIdx, D.rep_fst_fst G hω]

/-- On a cell of positive weight the representative's interval is the cell's interval. -/
lemma ivalRep_of_pos {G : ℕ} (hG : D.H ≤ G) {ω : Om n₁ n₂ G} (hω : 0 < D.wt G ω) :
    ((D.ivalRep G ω : Fin (2 ^ D.H)) : ℕ) = (ω.2.2 : ℕ) / 2 ^ (G - D.H) := by
  unfold ivalRep
  rw [ivalOfTime_val (D.hSt _ (D.rep_mem G ω))]
  have h := D.rep_floor_H hG hω
  have h2 : (0 : ℝ) ≤ 2 ^ D.H := by positivity
  rw [← Int.natCast_floor_eq_floor (mul_nonneg (D.hSt _ (D.rep_mem G ω)).1 h2)] at h
  unfold ival at h
  exact_mod_cast h

/-- Weights over a predicate are bounded by weights over any predicate it implies on cells
of positive weight. -/
lemma sum_wt_filter_le_of_pos {G : ℕ} (Q Q' : Om n₁ n₂ G → Prop) [DecidablePred Q]
    [DecidablePred Q'] (h : ∀ ω, 0 < D.wt G ω → Q ω → Q' ω) :
    ∑ ω ∈ univ.filter Q, D.wt G ω ≤ ∑ ω ∈ univ.filter Q', D.wt G ω := by
  classical
  calc ∑ ω ∈ univ.filter Q, D.wt G ω
      = ∑ ω ∈ (univ.filter Q).filter (fun ω => 0 < D.wt G ω), D.wt G ω := by
        refine (sum_subset (filter_subset _ _) fun ω hω hne => ?_).symm
        have : ¬ 0 < D.wt G ω := fun h' => hne (mem_filter.mpr ⟨hω, h'⟩)
        exact le_antisymm (not_lt.mp this) (D.wt_nonneg G ω)
    _ ≤ ∑ ω ∈ univ.filter Q', D.wt G ω := by
        refine sum_le_sum_of_subset_of_nonneg (fun ω hω => ?_) fun ω _ _ => D.wt_nonneg G ω
        rw [mem_filter] at hω
        rw [mem_filter] at hω ⊢
        exact ⟨mem_univ _, h ω hω.2 hω.1.2⟩

/-- **Cell marginals.** -/
lemma sw_cell (κ : Bool) (a : Fin n₁ ⊕ Fin n₂) (t : Fin (2 ^ G)) :
    fiberMass (D.sw G Ψ θ).P (fun ω => ((D.sw G Ψ θ).arm ω κ, (D.sw G Ψ θ).cell ω)) (a, t)
      ≤ D.prior κ a * (D.B / 2 ^ G) := by
  classical
  unfold fiberMass
  have hnn : ∀ ω : Om n₁ n₂ G, 0 ≤ D.wt G ω := D.wt_nonneg G
  refine le_trans (D.sum_wt_filter_le_of_pos _ (fun ω => (armIdx ω κ, ω.2.2) = (a, t))
    fun ω hω h => ?_) ?_
  · simp only [sw_arm, sw_cell_eq] at h
    rw [← D.armRep_of_pos hω κ]
    exact h
  cases κ with
  | true =>
    cases a with
    | inl i =>
      calc ∑ ω ∈ univ.filter (fun ω : Om n₁ n₂ G => (armIdx ω true, ω.2.2) = (Sum.inl i, t)),
            D.wt G ω
          ≤ ∑ ω ∈ (univ : Finset (Fin n₂)).image (fun i₂ => (i, i₂, t)), D.wt G ω := by
            refine sum_le_sum_of_subset_of_nonneg (fun ω hω => ?_) (fun ω _ _ => hnn ω)
            rw [mem_filter] at hω
            obtain ⟨-, h⟩ := hω
            simp only [armIdx, if_true, Prod.mk.injEq, Sum.inl.injEq] at h
            rw [mem_image]
            refine ⟨ω.2.1, mem_univ _, ?_⟩
            rcases ω with ⟨i₁, i₂, c⟩
            simp only at h ⊢
            rw [h.1, h.2]
        _ = ∑ i₂ : Fin n₂, D.wt G (i, i₂, t) := by
            rw [sum_image (fun i₂ _ i₂' _ h => by simpa using h)]
        _ ≤ D.B * D.π₁ i / 2 ^ G := D.sum_wt_fst_le G i t
        _ = D.prior true (Sum.inl i) * (D.B / 2 ^ G) := by simp only [prior]; ring
    | inr i =>
      have h0 : ∑ ω ∈ univ.filter (fun ω : Om n₁ n₂ G =>
          (armIdx ω true, ω.2.2) = (Sum.inr i, t)), D.wt G ω = 0 := by
        refine sum_eq_zero fun ω hω => ?_
        rw [mem_filter] at hω
        simp [armIdx] at hω
      rw [h0]
      simp [prior]
  | false =>
    cases a with
    | inr i =>
      calc ∑ ω ∈ univ.filter (fun ω : Om n₁ n₂ G => (armIdx ω false, ω.2.2) = (Sum.inr i, t)),
            D.wt G ω
          ≤ ∑ ω ∈ (univ : Finset (Fin n₁)).image (fun i₁ => (i₁, i, t)), D.wt G ω := by
            refine sum_le_sum_of_subset_of_nonneg (fun ω hω => ?_) (fun ω _ _ => hnn ω)
            rw [mem_filter] at hω
            obtain ⟨-, h⟩ := hω
            simp only [armIdx, Bool.false_eq_true, if_false, Prod.mk.injEq, Sum.inr.injEq] at h
            rw [mem_image]
            refine ⟨ω.1, mem_univ _, ?_⟩
            rcases ω with ⟨i₁, i₂, c⟩
            simp only at h ⊢
            rw [h.1, h.2]
        _ = ∑ i₁ : Fin n₁, D.wt G (i₁, i, t) := by
            rw [sum_image (fun i₁ _ i₁' _ h => by simpa using h)]
        _ ≤ D.B * D.π₂ i / 2 ^ G := D.sum_wt_snd_le G i t
        _ = D.prior false (Sum.inr i) * (D.B / 2 ^ G) := by simp only [prior]; ring
    | inl i =>
      have h0 : ∑ ω ∈ univ.filter (fun ω : Om n₁ n₂ G =>
          (armIdx ω false, ω.2.2) = (Sum.inl i, t)), D.wt G ω = 0 := by
        refine sum_eq_zero fun ω hω => ?_
        rw [mem_filter] at hω
        simp [armIdx] at hω
      rw [h0]
      simp [prior]

lemma exp_mul_log {N θ : ℝ} (hN : 0 < N) : Real.exp (θ * Real.log N) = N ^ θ := by
  rw [Real.rpow_def_of_pos hN, mul_comm]

open Classical in
/-- **Bad palette mass**, for the log-threshold `θ * log N`. -/
lemma sw_bad_le {G : ℕ} (hG : D.H' ≤ G) {N θ : ℝ} (hN : 0 < N) :
    ∑ ω, (D.sw G Ψ (θ * Real.log N)).P ω * (if (D.sw G Ψ (θ * Real.log N)).good ω then 0 else 1)
      ≤ (D.μ {x | x ∈ D.S ∧ N ^ θ * D.post D.F₀ x < D.post D.F₁ x}).toReal := by
  have h := D.sum_bad_le hG (N ^ θ)
  refine le_trans (le_of_eq ?_) h
  refine sum_congr rfl fun ω _ => ?_
  have e : (D.sw G Ψ (θ * Real.log N)).good ω ↔
      condOwn (D.wt G) (D.pal G) (D.fine G) ω ≤ N ^ θ * condOwn (D.wt G) (D.pal G) (D.coarse G) ω := by
    simp only [SwitchData.good, sw_P, sw_Z, sw_fine, sw_coarse_eq, sw_θ, exp_mul_log hN]
  by_cases hg : (D.sw G Ψ (θ * Real.log N)).good ω
  · rw [if_pos hg, if_pos (e.mp hg)]; rfl
  · rw [if_neg hg, if_neg (fun h' => hg (e.mpr h'))]; rfl

open Classical in
/-- **Light atoms.** -/
lemma sw_light_le (lam : ℝ) (hlam : 0 ≤ lam) (κ : Bool) :
    ∑ ω, (D.sw G Ψ θ).P ω * (if (D.sw G Ψ θ).heavy D.prior lam ω κ then (0 : ℝ) else 1)
      ≤ 2 ^ D.H * lam := by
  have h := sum_light_le (D.sw G Ψ θ) (D.sw_P_nonneg G Ψ θ) D.prior D.prior_nonneg lam hlam κ
  rwa [D.sum_prior, mul_one, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at h

/-- The normalized time of a cell's representative (up to the start's shift). -/
noncomputable def ntime (ω : Om n₁ n₂ G) : ℝ := (D.rep G ω).2 * 2 ^ D.H

/-- **Near arrivals.** Within the colour-`κ` arm atom of `er`, the cells whose
representative's normalized time is within `r` of `t₀` have weight at most
`prior κ a * (2 B (r / 2^H + 1 / 2^G))`, `a` the arm of `er`. -/
lemma sw_near_le (κ : Bool) (er : Om n₁ n₂ G) (t₀ r : ℝ) (hr : 0 ≤ r) :
    ∑ e ∈ univ.filter (fun e => (D.sw G Ψ θ).armKey κ e = (D.sw G Ψ θ).armKey κ er ∧
        |D.ntime G e - t₀| < r), (D.sw G Ψ θ).P e
      ≤ D.prior κ ((D.sw G Ψ θ).arm er κ) * (2 * D.B * (r / 2 ^ D.H + 1 / 2 ^ G)) := by
  classical
  have h2H : (0 : ℝ) < 2 ^ D.H := by positivity
  set s := univ.filter (fun e => (D.sw G Ψ θ).armKey κ e = (D.sw G Ψ θ).armKey κ er ∧
        |D.ntime G e - t₀| < r) with hs
  -- only positive cells count
  have hpos : ∑ e ∈ s.filter (fun e => 0 < D.wt G e), D.wt G e = ∑ e ∈ s, (D.sw G Ψ θ).P e := by
    refine sum_subset (filter_subset _ _) fun e he hne => ?_
    have : ¬ 0 < D.wt G e := fun h => hne (mem_filter.mpr ⟨he, h⟩)
    exact le_antisymm (not_lt.mp this) (D.wt_nonneg G e)
  rw [← hpos]
  -- the time condition in raw time
  have hnear : ∀ e ∈ s.filter (fun e => 0 < D.wt G e),
      |(D.rep G e).2 - t₀ / 2 ^ D.H| ≤ r / 2 ^ D.H := by
    intro e he
    simp only [hs, mem_filter, mem_univ, true_and] at he
    have h := he.1.2
    unfold ntime at h
    have e1 : (D.rep G e).2 - t₀ / 2 ^ D.H = ((D.rep G e).2 * 2 ^ D.H - t₀) / 2 ^ D.H := by
      field_simp
    rw [e1, abs_div, abs_of_pos h2H]
    exact div_le_div_of_nonneg_right h.le h2H.le
  have hr' : 0 ≤ r / 2 ^ D.H := div_nonneg hr h2H.le
  cases κ with
  | true =>
    have harm : ∀ e ∈ s.filter (fun e => 0 < D.wt G e), e.1 = (D.rep G er).1.1 := by
      intro e he
      have hpos := (mem_filter.mp he).2
      simp only [hs, mem_filter, mem_univ, true_and, SwitchData.armKey, sw_arm,
        Prod.mk.injEq] at he
      have h := he.1.1.1
      rw [D.armRep_of_pos hpos] at h
      simpa [armIdx, armRep, armOfEv] using h
    have h := D.sum_wt_near_fst_le G (s.filter (fun e => 0 < D.wt G e)) (D.rep G er).1.1
      (t₀ / 2 ^ D.H) (r / 2 ^ D.H) hr' (fun e he => ⟨harm e he, (mem_filter.mp he).2, hnear e he⟩)
    calc ∑ e ∈ s.filter (fun e => 0 < D.wt G e), D.wt G e
        ≤ D.B * D.π₁ (D.rep G er).1.1 * (2 * (r / 2 ^ D.H + 1 / 2 ^ G)) := h
      _ = D.prior true ((D.sw G Ψ θ).arm er true) * (2 * D.B * (r / 2 ^ D.H + 1 / 2 ^ G)) := by
          simp only [sw_arm, armRep, armOfEv, if_true, prior]; ring
  | false =>
    have harm : ∀ e ∈ s.filter (fun e => 0 < D.wt G e), e.2.1 = (D.rep G er).1.2 := by
      intro e he
      have hpos := (mem_filter.mp he).2
      simp only [hs, mem_filter, mem_univ, true_and, SwitchData.armKey, sw_arm,
        Prod.mk.injEq] at he
      have h := he.1.1.1
      rw [D.armRep_of_pos hpos] at h
      simpa [armIdx, armRep, armOfEv] using h
    have h := D.sum_wt_near_snd_le G (s.filter (fun e => 0 < D.wt G e)) (D.rep G er).1.2
      (t₀ / 2 ^ D.H) (r / 2 ^ D.H) hr' (fun e he => ⟨harm e he, (mem_filter.mp he).2, hnear e he⟩)
    calc ∑ e ∈ s.filter (fun e => 0 < D.wt G e), D.wt G e
        ≤ D.B * D.π₂ (D.rep G er).1.2 * (2 * (r / 2 ^ D.H + 1 / 2 ^ G)) := h
      _ = D.prior false ((D.sw G Ψ θ).arm er false) * (2 * D.B * (r / 2 ^ D.H + 1 / 2 ^ G)) := by
          simp only [sw_arm, armRep, armOfEv, Bool.false_eq_true, if_false, prior]; ring

/-! ### Legal steps are legal for the representatives -/

/-- A traversal of colour `κ` keeps the chosen arm index and the level-`H` interval of the
representatives (for all cells). -/
lemma rep_of_armKey_eq {κ : Bool} {ω ω' : Om n₁ n₂ G}
    (h : (D.sw G Ψ θ).armKey κ ω' = (D.sw G Ψ θ).armKey κ ω) :
    (if κ then (D.rep G ω).1.1 = (D.rep G ω').1.1 else (D.rep G ω).1.2 = (D.rep G ω').1.2) ∧
      Int.floor ((D.rep G ω).2 * (2 : ℝ) ^ D.H) =
        Int.floor ((D.rep G ω').2 * (2 : ℝ) ^ D.H) := by
  simp only [SwitchData.armKey, sw_arm, sw_ival, Prod.mk.injEq] at h
  refine ⟨?_, ?_⟩
  · cases κ
    · simpa [armRep, armOfEv, eq_comm] using h.1
    · simpa [armRep, armOfEv, eq_comm] using h.1
  · exact ((ivalOfTime_eq_iff (D.hSt _ (D.rep_mem G ω')) (D.hSt _ (D.rep_mem G ω))).mp
      h.2).symm

/-- Equal fine records give equal intervals (for all cells). -/
lemma ival_eq_of_fine_eq {ω ω' : Om n₁ n₂ G}
    (h : (D.sw G Ψ θ).fine ω = (D.sw G Ψ θ).fine ω') :
    (D.sw G Ψ θ).ival ω = (D.sw G Ψ θ).ival ω' := by
  simp only [sw_fine, sw_ival] at h ⊢
  have hc := D.hF₁₀ _ (D.rep_mem G ω) _ (D.rep_mem G ω') h
  have hf := D.hF₀H _ (D.rep_mem G ω) _ (D.rep_mem G ω') hc
  exact (ivalOfTime_eq_iff (D.hSt _ (D.rep_mem G ω)) (D.hSt _ (D.rep_mem G ω'))).mpr hf

/-- The fine record of a refresh is the frozen fine record of the representatives. -/
lemma rep_fine_eq {ω ω' : Om n₁ n₂ G} (h : (D.sw G Ψ θ).fine ω = (D.sw G Ψ θ).fine ω') :
    D.F₁ (D.rep G ω) = D.F₁ (D.rep G ω') := h

/-! ### Normalized time cells around a start -/

/-- The normalized time `σ a e` of the frozen statement. -/
noncomputable def sigma (H : ℕ) (a e : Ev n₁ n₂) : ℝ :=
  (e.2 - (((Int.floor (a.2 * (2 : ℝ) ^ H) : ℝ) + 1 / 2) / (2 : ℝ) ^ H)) * (2 : ℝ) ^ H

/-- The interval index of the start's representative. -/
noncomputable def startIdx (G : ℕ) (a₀ : Om n₁ n₂ G) : ℤ :=
  Int.floor ((D.rep G a₀).2 * (2 : ℝ) ^ D.H)

/-- The normalized time cells around the start cell `a₀`. -/
def normCells (G : ℕ) (a₀ : Om n₁ n₂ G) (t : Fin (2 ^ G)) : Set ℝ :=
  normCell D.H G (D.startIdx G a₀) t

/-- The normalized time of a cell's representative around the start cell `a₀`. -/
noncomputable def sTime (G : ℕ) (a₀ e : Om n₁ n₂ G) : ℝ :=
  sigma D.H (D.rep G a₀) (D.rep G e)

lemma sTime_eq (G : ℕ) (a₀ e : Om n₁ n₂ G) :
    D.sTime G a₀ e = D.ntime G e - D.startIdx G a₀ - 1 / 2 := by
  unfold sTime sigma ntime startIdx
  exact sigma_eq D.H _ _

/-- `hshift`: differences of normalized times are differences of `ntime`. -/
lemma sTime_sub (G : ℕ) (a₀ e f : Om n₁ n₂ G) :
    D.sTime G a₀ e - D.sTime G a₀ f = D.ntime G e - D.ntime G f := by
  rw [D.sTime_eq, D.sTime_eq]; ring

lemma measurableSet_normCells (G : ℕ) (a₀ : Om n₁ n₂ G) (t : Fin (2 ^ G)) :
    MeasurableSet (D.normCells G a₀ t) := measurableSet_normCell _ _ _ _

lemma volume_normCells (G : ℕ) (a₀ : Om n₁ n₂ G) (t : Fin (2 ^ G)) :
    volume (D.normCells G a₀ t) = ENNReal.ofReal (2 ^ D.H / 2 ^ G) := volume_normCell _ _ _ _

lemma normCells_disjoint (G : ℕ) (a₀ : Om n₁ n₂ G) :
    Pairwise (fun s t : Fin (2 ^ G) => Disjoint (D.normCells G a₀ s) (D.normCells G a₀ t)) :=
  fun _ _ hst => normCell_disjoint _ _ _ (fun h => hst (Fin.ext h))

/-- `hclose`: a point of the normalized cell of a positive cell is within the cell width of
the cell's normalized time. -/
lemma normCells_close (G : ℕ) (a₀ : Om n₁ n₂ G) {e : Om n₁ n₂ G} (he : 0 < D.wt G e) {y : ℝ}
    (hy : y ∈ D.normCells G a₀ e.2.2) : |y - D.sTime G a₀ e| ≤ 2 ^ D.H / 2 ^ G := by
  have hmem : D.sTime G a₀ e ∈ D.normCells G a₀ e.2.2 := by
    rw [D.sTime_eq]
    exact mem_normCell_of_mem_cellSet _ (D.rep_time_mem G he)
  exact abs_sub_le_of_mem_normCell hy hmem

/-- `hunit`: a positive cell in the start's interval has its normalized cell in `[-1, 1]`. -/
lemma normCells_unit {G : ℕ} (hG : D.H ≤ G) (a₀ : Om n₁ n₂ G) {e : Om n₁ n₂ G}
    (he : 0 < D.wt G e) (hiv : D.ivalRep G e = D.ivalRep G a₀) {y : ℝ}
    (hy : y ∈ D.normCells G a₀ e.2.2) : |y| ≤ 1 := by
  have hfl : Int.floor ((D.rep G e).2 * (2 : ℝ) ^ D.H) = D.startIdx G a₀ :=
    (ivalOfTime_eq_iff (D.hSt _ (D.rep_mem G e)) (D.hSt _ (D.rep_mem G a₀))).mp hiv
  rw [D.rep_floor_H hG he] at hfl
  have h := normCell_subset_Icc hG (c := (e.2.2 : ℕ)) (k := D.startIdx G a₀) (by
    unfold ival at hfl; exact hfl) hy
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- The start's own normalized time is at most `1/2` in absolute value. -/
lemma abs_sTime_self_le (G : ℕ) (a₀ : Om n₁ n₂ G) : |D.sTime G a₀ a₀| ≤ 1 := by
  rw [D.sTime_eq]
  unfold ntime startIdx
  set t := (D.rep G a₀).2 * (2 : ℝ) ^ D.H
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  rw [abs_le]
  constructor <;> linarith

end Data

end Submission.Obl.k4_matching_abstract_switching_mixture
