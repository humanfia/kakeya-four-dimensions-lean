-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.Triples.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Selecting a popular pattern triple

`triple_selection`: given a finite set `A` of points with distinct positions `x`, a finite set
`Q₀` and a relation `N`, where every point of `A` is related to at least `τ` elements of `Q₀`
and few pairs of points are `c`-close, there are two `c`-far points `p₁, p₂` with many common
neighbours `Q`, and many points `p` between them, nearer to `p₁`, related to many elements of `Q`.

Proof: double counting of the pattern triples `(p₁, p, p₂)` (with `NearFirst x p₁ p p₂`) over
the common neighbours `q`. Among the six orderings of three points one is a pattern, so the
number of patterns related to `q` is at least `m_q ^ 3 / 6`, where `m_q` is the number of
neighbours of `q`; Jensen's inequality bounds `∑ m_q ^ 3` from below, close pairs contribute
little, and averaging over the pairs `(p₁, p₂)` gives the claim.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- `p` lies between `p₁` and `p₂` (by position `x`) and is at least as close to `p₁`. -/
def NearFirst {α : Type*} (x : α → ℝ) (p₁ p p₂ : α) : Prop :=
  min (x p₁) (x p₂) ≤ x p ∧ x p ≤ max (x p₁) (x p₂) ∧ |x p - x p₁| ≤ |x p - x p₂|

/-- Decidability of `NearFirst` (classical), used locally in this file. -/
@[instance_reducible]
noncomputable def triple_sel_decNearFirst {α : Type*} (x : α → ℝ) (p₁ p p₂ : α) :
    Decidable (NearFirst x p₁ p p₂) :=
  Classical.dec _

attribute [local instance] triple_sel_decNearFirst

/-! ### Three reals -/

/-- Of three reals, one lies between the other two. -/
theorem triple_sel_median (u v w : ℝ) :
    (min v w ≤ u ∧ u ≤ max v w) ∨ (min u w ≤ v ∧ v ≤ max u w) ∨
      (min u v ≤ w ∧ w ≤ max u v) := by
  simp only [min_le_iff, le_max_iff]
  rcases le_total u v with h1 | h1 <;> rcases le_total v w with h2 | h2 <;>
    rcases le_total u w with h3 | h3 <;> tauto

theorem triple_sel_nf_of_between (u v w : ℝ) (h1 : min u w ≤ v) (h2 : v ≤ max u w) :
    (min u w ≤ v ∧ v ≤ max u w ∧ |v - u| ≤ |v - w|) ∨
      (min w u ≤ v ∧ v ≤ max w u ∧ |v - w| ≤ |v - u|) := by
  rcases le_total |v - u| |v - w| with h | h
  · exact Or.inl ⟨h1, h2, h⟩
  · exact Or.inr ⟨by rwa [min_comm], by rwa [max_comm], h⟩

/-- Among the six orderings of three points, one is a `NearFirst` pattern. -/
theorem triple_sel_six {α : Type*} (x : α → ℝ) (a p b : α) :
    NearFirst x a p b ∨ NearFirst x b p a ∨ NearFirst x p a b ∨ NearFirst x b a p ∨
      NearFirst x a b p ∨ NearFirst x p b a := by
  unfold NearFirst
  rcases triple_sel_median (x a) (x p) (x b) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases triple_sel_nf_of_between (x p) (x a) (x b) h1 h2 with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases triple_sel_nf_of_between (x a) (x p) (x b) h1 h2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases triple_sel_nf_of_between (x a) (x b) (x p) h1 h2 with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem triple_sel_ite_six (s₁ s₂ s₃ s₄ s₅ s₆ : Prop) [Decidable s₁] [Decidable s₂]
    [Decidable s₃] [Decidable s₄] [Decidable s₅] [Decidable s₆]
    (h : s₁ ∨ s₂ ∨ s₃ ∨ s₄ ∨ s₅ ∨ s₆) :
    (1 : ℝ) ≤ (if s₁ then 1 else 0) + (if s₂ then 1 else 0) + (if s₃ then 1 else 0) +
      (if s₄ then 1 else 0) + (if s₅ then 1 else 0) + (if s₆ then 1 else 0) := by
  have h0 : ∀ (s : Prop) [Decidable s], (0 : ℝ) ≤ if s then 1 else 0 := by
    intro s _; split_ifs <;> norm_num
  have e1 := h0 s₁; have e2 := h0 s₂; have e3 := h0 s₃
  have e4 := h0 s₄; have e5 := h0 s₅; have e6 := h0 s₆
  rcases h with h | h | h | h | h | h
  · rw [ite_eq_left h]; linarith
  · rw [ite_eq_left h]; linarith
  · rw [ite_eq_left h]; linarith
  · rw [ite_eq_left h]; linarith
  · rw [ite_eq_left h]; linarith
  · rw [ite_eq_left h]; linarith

/-! ### Triple sums -/

theorem triple_sel_sum_perm6 {α : Type*} (A : Finset α) (f : α → α → α → ℝ) :
    ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A,
        (f a p b + f b p a + f p a b + f b a p + f a b p + f p b a) =
      6 * ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f a p b := by
  have e2 : ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f b p a = ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f a p b := by
    calc ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f b p a = ∑ a ∈ A, ∑ b ∈ A, ∑ p ∈ A, f b p a :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ b ∈ A, ∑ a ∈ A, ∑ p ∈ A, f b p a := Finset.sum_comm
      _ = ∑ b ∈ A, ∑ p ∈ A, ∑ a ∈ A, f b p a :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  have e3 : ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f p a b = ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f a p b :=
    Finset.sum_comm
  have e4 : ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f b a p = ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f a p b := by
    calc ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f b a p = ∑ a ∈ A, ∑ b ∈ A, ∑ p ∈ A, f b a p :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ b ∈ A, ∑ a ∈ A, ∑ p ∈ A, f b a p := Finset.sum_comm
  have e5 : ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f a b p = ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f a p b :=
    Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  have e6 : ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f p b a = ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f a p b := by
    calc ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, f p b a = ∑ p ∈ A, ∑ a ∈ A, ∑ b ∈ A, f p b a :=
          Finset.sum_comm
      _ = ∑ p ∈ A, ∑ b ∈ A, ∑ a ∈ A, f p b a :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  simp only [Finset.sum_add_distrib, e2, e3, e4, e5, e6]
  ring

/-- Weighted count of patterns: `(∑ w) ^ 3 ≤ 6 ∑ w a w p w b g a p b` when, for every triple,
one of its six orderings has `g ≥ 1`. -/
theorem triple_sel_weighted_count {α : Type*} (A : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ A, 0 ≤ w a) (g : α → α → α → ℝ)
    (hg : ∀ a p b, 1 ≤ g a p b + g b p a + g p a b + g b a p + g a b p + g p b a) :
    (∑ a ∈ A, w a) ^ 3 ≤ 6 * ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, w a * w p * w b * g a p b := by
  have hcube : ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, w a * w p * w b = (∑ a ∈ A, w a) ^ 3 := by
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hperm := triple_sel_sum_perm6 A (fun a p b => w a * w p * w b * g a p b)
  rw [← hcube, ← hperm]
  apply Finset.sum_le_sum; intro a ha
  apply Finset.sum_le_sum; intro p hp
  apply Finset.sum_le_sum; intro b hb
  have h0 : 0 ≤ w a * w p * w b := mul_nonneg (mul_nonneg (hw a ha) (hw p hp)) (hw b hb)
  have h1 := mul_le_mul_of_nonneg_left (hg a p b) h0
  calc w a * w p * w b = w a * w p * w b * 1 := by ring
    _ ≤ w a * w p * w b * (g a p b + g b p a + g p a b + g b a p + g a b p + g p b a) := h1
    _ = _ := by ring

/-- Lower bound for the total weighted number of patterns, by Jensen's inequality. -/
theorem triple_sel_lower {α β : Type*} (A : Finset α) (Q₀ : Finset β)
    (w : β → α → ℝ) (g : α → α → α → ℝ) (hw : ∀ q a, 0 ≤ w q a)
    (hg : ∀ a p b, 1 ≤ g a p b + g b p a + g p a b + g b a p + g a b p + g p b a)
    {τ : ℝ} (hτ : 0 ≤ τ) (hdeg : ∀ a ∈ A, τ ≤ ∑ q ∈ Q₀, w q a) :
    ((A.card : ℝ) * τ) ^ 3 ≤ 6 * (Q₀.card : ℝ) ^ 2 *
      ∑ a ∈ A, ∑ b ∈ A, ∑ p ∈ A, ∑ q ∈ Q₀, w q a * w q p * w q b * g a p b := by
  have h1 : ∀ q ∈ Q₀, (∑ a ∈ A, w q a) ^ 3 ≤
      6 * ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, w q a * w q p * w q b * g a p b :=
    fun q _ => triple_sel_weighted_count A (w q) (fun a _ => hw q a) g hg
  have h2 : ∑ q ∈ Q₀, (∑ a ∈ A, w q a) ^ 3 ≤
      6 * ∑ q ∈ Q₀, ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, w q a * w q p * w q b * g a p b := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum h1
  have h3 : (∑ q ∈ Q₀, ∑ a ∈ A, w q a) ^ 3 ≤
      (Q₀.card : ℝ) ^ 2 * ∑ q ∈ Q₀, (∑ a ∈ A, w q a) ^ 3 :=
    pow_sum_le_card_mul_sum_pow (fun q _ => Finset.sum_nonneg (fun a _ => hw q a)) 2
  have h4 : (A.card : ℝ) * τ ≤ ∑ q ∈ Q₀, ∑ a ∈ A, w q a := by
    rw [Finset.sum_comm]
    calc (A.card : ℝ) * τ = A.card • τ := (nsmul_eq_mul _ _).symm
      _ ≤ ∑ a ∈ A, ∑ q ∈ Q₀, w q a :=
        Finset.card_nsmul_le_sum A (fun a => ∑ q ∈ Q₀, w q a) τ hdeg
  have h5 : ((A.card : ℝ) * τ) ^ 3 ≤ (∑ q ∈ Q₀, ∑ a ∈ A, w q a) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hτ) h4 3
  have h6 : ∑ q ∈ Q₀, ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, w q a * w q p * w q b * g a p b =
      ∑ a ∈ A, ∑ b ∈ A, ∑ p ∈ A, ∑ q ∈ Q₀, w q a * w q p * w q b * g a p b := by
    calc ∑ q ∈ Q₀, ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, w q a * w q p * w q b * g a p b
        = ∑ a ∈ A, ∑ q ∈ Q₀, ∑ p ∈ A, ∑ b ∈ A, w q a * w q p * w q b * g a p b :=
          Finset.sum_comm
      _ = ∑ a ∈ A, ∑ p ∈ A, ∑ q ∈ Q₀, ∑ b ∈ A, w q a * w q p * w q b * g a p b :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A, ∑ q ∈ Q₀, w q a * w q p * w q b * g a p b :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
      _ = ∑ a ∈ A, ∑ b ∈ A, ∑ p ∈ A, ∑ q ∈ Q₀, w q a * w q p * w q b * g a p b :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  rw [← h6]
  have hn2 : (0 : ℝ) ≤ (Q₀.card : ℝ) ^ 2 := by positivity
  calc ((A.card : ℝ) * τ) ^ 3 ≤ (∑ q ∈ Q₀, ∑ a ∈ A, w q a) ^ 3 := h5
    _ ≤ (Q₀.card : ℝ) ^ 2 * ∑ q ∈ Q₀, (∑ a ∈ A, w q a) ^ 3 := h3
    _ ≤ (Q₀.card : ℝ) ^ 2 * (6 * ∑ q ∈ Q₀, ∑ a ∈ A, ∑ p ∈ A, ∑ b ∈ A,
          w q a * w q p * w q b * g a p b) := mul_le_mul_of_nonneg_left h2 hn2
    _ = _ := by ring

/-- The pair weight `Φ(a, b)` written as a sum of indicator products. -/
theorem triple_sel_phi_eq {α β : Type*} (A : Finset α) (Q₀ : Finset β) (x : α → ℝ)
    (N : α → β → Prop) [∀ p q, Decidable (N p q)] (a b : α) :
    ∑ p ∈ A.filter (fun p => NearFirst x a p b),
        (((Q₀.filter (fun q => N a q ∧ N b q)).filter (fun q => N p q)).card : ℝ) =
      ∑ p ∈ A, ∑ q ∈ Q₀, (if N a q then (1 : ℝ) else 0) * (if N p q then 1 else 0) *
        (if N b q then 1 else 0) * (if NearFirst x a p b then 1 else 0) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.filter_filter, Finset.natCast_card_filter]
  by_cases hNF : NearFirst x a p b
  · simp only [hNF, ite_true, mul_one]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases h1 : N a q <;> by_cases h2 : N b q <;> by_cases h3 : N p q <;> simp [h1, h2, h3]
  · simp [hNF]

/-- Averaging over the pairs `(a, b)`: some `c`-far pair has many common neighbours and a large
weight. -/
theorem triple_sel_key {α β : Type*} (A : Finset α) (Q₀ : Finset β) (x : α → ℝ)
    (N : α → β → Prop) [∀ p q, Decidable (N p q)] {θ c : ℝ} (hθ : 0 < θ)
    (hm : 0 < (A.card : ℝ)) (hn : 0 < (Q₀.card : ℝ))
    (hT : (A.card : ℝ) ^ 3 * θ ^ 3 * Q₀.card ≤ 6 * ∑ a ∈ A, ∑ b ∈ A,
      ∑ p ∈ A.filter (fun p => NearFirst x a p b),
        (((Q₀.filter (fun q => N a q ∧ N b q)).filter (fun q => N p q)).card : ℝ))
    (hclose : (((A ×ˢ A).filter (fun ab => |x ab.1 - x ab.2| < c)).card : ℝ) ≤
        θ ^ 3 / 96 * (A.card : ℝ) ^ 2) :
    ∃ a ∈ A, ∃ b ∈ A, c ≤ |x b - x a| ∧
      θ ^ 3 / 384 * (Q₀.card : ℝ) ≤ ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) ∧
      θ ^ 3 / 192 * (A.card : ℝ) * ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) ≤
        ∑ p ∈ A.filter (fun p => NearFirst x a p b),
          (((Q₀.filter (fun q => N a q ∧ N b q)).filter (fun q => N p q)).card : ℝ) := by
  by_contra hcon
  push Not at hcon
  have hθ3 : 0 < θ ^ 3 := by positivity
  have hpt : ∀ a ∈ A, ∀ b ∈ A,
      ∑ p ∈ A.filter (fun p => NearFirst x a p b),
          (((Q₀.filter (fun q => N a q ∧ N b q)).filter (fun q => N p q)).card : ℝ) ≤
        (A.card : ℝ) * Q₀.card * (if |x a - x b| < c then 1 else 0) +
          (A.card : ℝ) * (θ ^ 3 / 384 * Q₀.card) +
          θ ^ 3 / 192 * (A.card : ℝ) * ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) := by
    intro a ha b hb
    have hQn : ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) ≤ Q₀.card := by
      exact_mod_cast Finset.card_filter_le _ _
    have hQ0 : (0 : ℝ) ≤ ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) := Nat.cast_nonneg _
    have hΦle : ∑ p ∈ A.filter (fun p => NearFirst x a p b),
        (((Q₀.filter (fun q => N a q ∧ N b q)).filter (fun q => N p q)).card : ℝ) ≤
        (A.card : ℝ) * ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) := by
      calc _ ≤ ∑ p ∈ A.filter (fun p => NearFirst x a p b),
            ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) :=
            Finset.sum_le_sum (fun p _ => by exact_mod_cast Finset.card_filter_le _ _)
        _ = ((A.filter (fun p => NearFirst x a p b)).card : ℝ) *
            ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ hQ0
            exact_mod_cast Finset.card_filter_le _ _
    have hA1 : (0 : ℝ) ≤ (A.card : ℝ) * (θ ^ 3 / 384 * Q₀.card) := by positivity
    have hA2 : (0 : ℝ) ≤ θ ^ 3 / 192 * (A.card : ℝ) *
        ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) := by positivity
    by_cases hcl : |x a - x b| < c
    · rw [ite_eq_left hcl]
      have : (A.card : ℝ) * ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) ≤
          (A.card : ℝ) * Q₀.card := mul_le_mul_of_nonneg_left hQn hm.le
      linarith
    · rw [ite_eq_right hcl]
      have hfar : c ≤ |x b - x a| := by rw [abs_sub_comm]; exact not_lt.mp hcl
      by_cases hbig : θ ^ 3 / 384 * (Q₀.card : ℝ) ≤
          ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ)
      · have := hcon a ha b hb hfar hbig
        linarith
      · have : (A.card : ℝ) * ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) ≤
            (A.card : ℝ) * (θ ^ 3 / 384 * Q₀.card) :=
          mul_le_mul_of_nonneg_left (not_le.mp hbig).le hm.le
        linarith
  have hsum := Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hpt a ha b hb))
  have e1 : ∑ a ∈ A, ∑ b ∈ A, ((A.card : ℝ) * Q₀.card * (if |x a - x b| < c then 1 else 0)) =
      (A.card : ℝ) * Q₀.card *
        (((A ×ˢ A).filter (fun ab => |x ab.1 - x ab.2| < c)).card : ℝ) := by
    rw [Finset.natCast_card_filter, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
  have e2 : ∑ a ∈ A, ∑ b ∈ A, ((A.card : ℝ) * (θ ^ 3 / 384 * Q₀.card)) =
      (A.card : ℝ) * ((A.card : ℝ) * ((A.card : ℝ) * (θ ^ 3 / 384 * Q₀.card))) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
  have e3 : ∑ a ∈ A, ∑ b ∈ A,
      (θ ^ 3 / 192 * (A.card : ℝ) * ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ)) =
      θ ^ 3 / 192 * (A.card : ℝ) *
        ∑ a ∈ A, ∑ b ∈ A, ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
  have hsplit : ∑ a ∈ A, ∑ b ∈ A,
      ((A.card : ℝ) * Q₀.card * (if |x a - x b| < c then 1 else 0) +
        (A.card : ℝ) * (θ ^ 3 / 384 * Q₀.card) +
        θ ^ 3 / 192 * (A.card : ℝ) * ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ)) =
      ∑ a ∈ A, ∑ b ∈ A, ((A.card : ℝ) * Q₀.card * (if |x a - x b| < c then 1 else 0)) +
        ∑ a ∈ A, ∑ b ∈ A, ((A.card : ℝ) * (θ ^ 3 / 384 * Q₀.card)) +
        ∑ a ∈ A, ∑ b ∈ A,
          (θ ^ 3 / 192 * (A.card : ℝ) * ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ)) := by
    simp only [Finset.sum_add_distrib]
  have hQsum : ∑ a ∈ A, ∑ b ∈ A, ((Q₀.filter (fun q => N a q ∧ N b q)).card : ℝ) ≤
      (A.card : ℝ) * ((A.card : ℝ) * Q₀.card) := by
    calc _ ≤ ∑ a ∈ A, ∑ b ∈ A, (Q₀.card : ℝ) :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => by
            exact_mod_cast Finset.card_filter_le _ _))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hc1 := mul_le_mul_of_nonneg_left hclose
    (by positivity : (0 : ℝ) ≤ (A.card : ℝ) * Q₀.card)
  have hc3 := mul_le_mul_of_nonneg_left hQsum
    (by positivity : (0 : ℝ) ≤ θ ^ 3 / 192 * (A.card : ℝ))
  have hK : 0 < (A.card : ℝ) ^ 3 * θ ^ 3 * Q₀.card := by positivity
  rw [hsplit, e1, e2, e3] at hsum
  linarith

-- The hypotheses `hx` (distinct positions) and `hbig` are not needed by this proof: the count of
-- patterns includes degenerate triples, which gives `m ^ 3 / 6` patterns per `q` directly.
set_option linter.unusedVariables false in
/-- **Selection of a popular pattern triple.** -/
theorem triple_selection {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (Q₀ : Finset β) (x : α → ℝ) (N : α → β → Prop)
    [∀ p q, Decidable (N p q)] {τ c : ℝ} (hτ : 0 < τ) (hA : A.Nonempty)
    (hx : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → x a ≠ x b)
    (hdeg : ∀ p ∈ A, τ ≤ ((Q₀.filter (fun q => N p q)).card : ℝ))
    (hbig : 4 * (Q₀.card : ℝ) ≤ A.card * τ)
    (hclose : (((A ×ˢ A).filter (fun ab => |x ab.1 - x ab.2| < c)).card : ℝ) ≤
        (τ / Q₀.card) ^ 3 / 96 * (A.card : ℝ) ^ 2) :
    ∃ p₁ ∈ A, ∃ p₂ ∈ A, ∃ Q ⊆ Q₀, ∃ H ⊆ A,
      c ≤ |x p₂ - x p₁| ∧
      (∀ q ∈ Q, N p₁ q ∧ N p₂ q) ∧
      (τ / Q₀.card) ^ 3 / 384 * (Q₀.card : ℝ) ≤ Q.card ∧
      (τ / Q₀.card) ^ 3 / 384 * (A.card : ℝ) ≤ H.card ∧
      ∀ p ∈ H, NearFirst x p₁ p p₂ ∧
        (τ / Q₀.card) ^ 3 / 384 * (Q.card : ℝ) ≤ ((Q.filter (fun q => N p q)).card : ℝ) := by
  obtain ⟨a₀, ha₀⟩ := hA
  have hnpos : (0 : ℝ) < (Q₀.card : ℝ) := by
    have h1 := hdeg a₀ ha₀
    have h2 : ((Q₀.filter (fun q => N a₀ q)).card : ℝ) ≤ Q₀.card := by
      exact_mod_cast Finset.card_filter_le _ _
    linarith
  have hmpos : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨a₀, ha₀⟩
  have hlow := triple_sel_lower A Q₀ (fun q a => if N a q then (1 : ℝ) else 0)
    (fun a p b => if NearFirst x a p b then (1 : ℝ) else 0)
    (fun q a => by split_ifs <;> norm_num)
    (fun a p b => triple_sel_ite_six _ _ _ _ _ _ (triple_sel_six x a p b)) hτ.le
    (fun a ha => by
      have h := hdeg a ha
      rwa [Finset.natCast_card_filter] at h)
  obtain ⟨θ, hθ_def⟩ : ∃ θ : ℝ, θ = τ / (Q₀.card : ℝ) := ⟨_, rfl⟩
  rw [← hθ_def] at hclose ⊢
  have hθpos : 0 < θ := hθ_def ▸ div_pos hτ hnpos
  have hτθ : τ = θ * Q₀.card := by rw [hθ_def]; field_simp
  have hT : (A.card : ℝ) ^ 3 * θ ^ 3 * Q₀.card ≤ 6 * ∑ a ∈ A, ∑ b ∈ A,
      ∑ p ∈ A.filter (fun p => NearFirst x a p b),
        (((Q₀.filter (fun q => N a q ∧ N b q)).filter (fun q => N p q)).card : ℝ) := by
    have hsum_eq : ∑ a ∈ A, ∑ b ∈ A, ∑ p ∈ A.filter (fun p => NearFirst x a p b),
        (((Q₀.filter (fun q => N a q ∧ N b q)).filter (fun q => N p q)).card : ℝ) =
        ∑ a ∈ A, ∑ b ∈ A, ∑ p ∈ A, ∑ q ∈ Q₀, (if N a q then (1 : ℝ) else 0) *
          (if N p q then 1 else 0) * (if N b q then 1 else 0) *
          (if NearFirst x a p b then 1 else 0) :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        triple_sel_phi_eq A Q₀ x N a b))
    rw [hsum_eq]
    have h1 : (Q₀.card : ℝ) ^ 2 * ((A.card : ℝ) ^ 3 * θ ^ 3 * Q₀.card) ≤
        (Q₀.card : ℝ) ^ 2 * (6 * ∑ a ∈ A, ∑ b ∈ A, ∑ p ∈ A, ∑ q ∈ Q₀,
          (if N a q then (1 : ℝ) else 0) * (if N p q then 1 else 0) *
          (if N b q then 1 else 0) * (if NearFirst x a p b then 1 else 0)) := by
      calc _ = ((A.card : ℝ) * τ) ^ 3 := by rw [hτθ]; ring
        _ ≤ _ := hlow
        _ = _ := by ring
    exact le_of_mul_le_mul_left h1 (pow_pos hnpos 2)
  obtain ⟨a, ha, b, hb, hfar, hQbig, hΦbig⟩ :=
    triple_sel_key A Q₀ x N hθpos hmpos hnpos hT hclose
  set Q := Q₀.filter (fun q => N a q ∧ N b q) with hQ_def
  have hκpos : 0 < θ ^ 3 / 384 := div_pos (pow_pos hθpos 3) (by norm_num)
  have hQpos : (0 : ℝ) < (Q.card : ℝ) := lt_of_lt_of_le (mul_pos hκpos hnpos) hQbig
  have hsplit := Finset.sum_filter_add_sum_filter_not (A.filter (fun p => NearFirst x a p b))
    (fun p => θ ^ 3 / 384 * (Q.card : ℝ) ≤ ((Q.filter (fun q => N p q)).card : ℝ))
    (fun p => ((Q.filter (fun q => N p q)).card : ℝ))
  have h2 : ∑ p ∈ (A.filter (fun p => NearFirst x a p b)).filter
      (fun p => ¬ (θ ^ 3 / 384 * (Q.card : ℝ) ≤ ((Q.filter (fun q => N p q)).card : ℝ))),
      ((Q.filter (fun q => N p q)).card : ℝ) ≤ (A.card : ℝ) * (θ ^ 3 / 384 * Q.card) := by
    calc _ ≤ ∑ p ∈ (A.filter (fun p => NearFirst x a p b)).filter
          (fun p => ¬ (θ ^ 3 / 384 * (Q.card : ℝ) ≤ ((Q.filter (fun q => N p q)).card : ℝ))),
          θ ^ 3 / 384 * (Q.card : ℝ) :=
          Finset.sum_le_sum (fun p hp => (not_le.mp (Finset.mem_filter.mp hp).2).le)
      _ = (((A.filter (fun p => NearFirst x a p b)).filter
          (fun p => ¬ (θ ^ 3 / 384 * (Q.card : ℝ) ≤
            ((Q.filter (fun q => N p q)).card : ℝ)))).card : ℝ) *
          (θ ^ 3 / 384 * Q.card) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A.card : ℝ) * (θ ^ 3 / 384 * Q.card) := by
          apply mul_le_mul_of_nonneg_right _ (mul_pos hκpos hQpos).le
          exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)
  set H := (A.filter (fun p => NearFirst x a p b)).filter
    (fun p => θ ^ 3 / 384 * (Q.card : ℝ) ≤ ((Q.filter (fun q => N p q)).card : ℝ)) with hH_def
  have h1 : ∑ p ∈ H, ((Q.filter (fun q => N p q)).card : ℝ) ≤ (H.card : ℝ) * Q.card := by
    calc _ ≤ ∑ p ∈ H, (Q.card : ℝ) :=
          Finset.sum_le_sum (fun p _ => by exact_mod_cast Finset.card_filter_le _ _)
      _ = (H.card : ℝ) * Q.card := by rw [Finset.sum_const, nsmul_eq_mul]
  have h3 : θ ^ 3 / 384 * (A.card : ℝ) * Q.card ≤ (H.card : ℝ) * Q.card := by
    linarith
  refine ⟨a, ha, b, hb, Q, Finset.filter_subset _ _, H,
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _), hfar, ?_, hQbig,
    le_of_mul_le_mul_right h3 hQpos, ?_⟩
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_filter.mp hp1).2, hp2⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
