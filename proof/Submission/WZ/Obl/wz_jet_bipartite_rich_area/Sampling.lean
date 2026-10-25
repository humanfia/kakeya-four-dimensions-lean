-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.Sampling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Incidences

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Finset
open scoped Classical

/-- An elementary upper bound for the probability that all samples miss a set. -/
private theorem miss_pow_bound {x : ℝ} (hx1 : x ≤ 1) (k : ℕ) :
    (1 - x) ^ k * (1 + (k : ℝ) * x) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ = (1 - x) ^ k * ((1 - x) * (1 + ((k : ℝ) + 1) * x)) := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ (1 - x) ^ k * (1 + (k : ℝ) * x) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (sub_nonneg.mpr hx1) _)
        nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity) (sq_nonneg x)]
      _ ≤ 1 := ih

/-- Sampling at least the reciprocal density makes the missed fraction at most one half. -/
private theorem miss_pow_le_half {a m : ℝ} (ha : 0 < a)
    (hma : m ≤ a) (k : ℕ) (hk : a ≤ (k : ℝ) * m) :
    (a - m) ^ k ≤ a ^ k / 2 := by
  have hx1 : m / a ≤ 1 := (div_le_one ha).mpr hma
  have hkx : 1 ≤ (k : ℝ) * (m / a) := by
    rw [← mul_div_assoc]
    exact (one_le_div ha).mpr hk
  have hp := miss_pow_bound hx1 k
  have hp0 : 0 ≤ (1 - m / a) ^ k := pow_nonneg (sub_nonneg.mpr hx1) _
  have hh : (1 - m / a) ^ k ≤ 1 / 2 := by nlinarith
  have heq : 1 - m / a = (a - m) / a := by field_simp
  rw [heq, div_pow] at hh
  exact (div_le_iff₀ (pow_pos ha k)).mp hh |>.trans_eq (by ring)

/-- The exact number of samples with replacement avoiding an incidence set. -/
theorem card_samples_avoiding {α : Type*} [Fintype α] (P : α → Prop) (k : ℕ) :
    Fintype.card {f : Fin k → α // ∀ t, ¬ P (f t)} =
      (Fintype.card α - Fintype.card {a // P a}) ^ k := by
  classical
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun (_ : Fin k) a => ¬ P a))]
  simp

/-- At least half of the samples meet a set when sample length times its cardinality
is at least the ambient cardinality. Empty samples and sets are covered by the hypotheses. -/
theorem half_samples_hit {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) (k : ℕ)
    (hk : Fintype.card α ≤ k * Fintype.card {a // P a}) :
    (Fintype.card (Fin k → α) : ℝ) / 2 ≤
      Fintype.card {f : Fin k → α // ∃ t, P (f t)} := by
  classical
  have hm : Fintype.card {a // P a} ≤ Fintype.card α := Fintype.card_subtype_le _
  have hmiss := miss_pow_le_half (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card α))
    (Nat.cast_le.mpr hm) k
    (by exact_mod_cast hk)
  have havoid : (Fintype.card {f : Fin k → α // ∀ t, ¬ P (f t)} : ℝ) ≤
      (Fintype.card (Fin k → α) : ℝ) / 2 := by
    rw [card_samples_avoiding, Nat.cast_pow, Nat.cast_sub hm]
    simpa using hmiss
  have hc := Fintype.card_subtype_compl (fun f : Fin k → α => ∃ t, P (f t))
  simp only [not_exists] at hc
  rw [hc, Nat.cast_sub (Fintype.card_subtype_le _)] at havoid
  linarith

/-- The two colors are sampled independently, so one quarter of the pairs of samples
meet both incidence sets. -/
theorem quarter_samples_hit_both {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (P : α → Prop) (Q : β → Prop) (k l : ℕ)
    (hk : Fintype.card α ≤ k * Fintype.card {a // P a})
    (hl : Fintype.card β ≤ l * Fintype.card {b // Q b}) :
    (Fintype.card ((Fin k → α) × (Fin l → β)) : ℝ) / 4 ≤
      Fintype.card {w : (Fin k → α) × (Fin l → β) //
        (∃ t, P (w.1 t)) ∧ (∃ t, Q (w.2 t))} := by
  classical
  calc
    _ = ((Fintype.card (Fin k → α) : ℝ) / 2) *
        ((Fintype.card (Fin l → β) : ℝ) / 2) := by
      rw [Fintype.card_prod, Nat.cast_mul]
      ring
    _ ≤ (Fintype.card {f : Fin k → α // ∃ t, P (f t)} : ℝ) *
        Fintype.card {g : Fin l → β // ∃ t, Q (g t)} :=
      mul_le_mul (half_samples_hit P k hk) (half_samples_hit Q l hl)
        (by positivity) (by positivity)
    _ = _ := by
      rw [Fintype.card_congr (Equiv.subtypeProdEquivProd
        (p := fun f : Fin k → α => ∃ t, P (f t))
        (q := fun g : Fin l → β => ∃ t, Q (g t))), Fintype.card_prod, Nat.cast_mul]

private theorem ncard_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : β → Prop) :
    Set.ncard {a | P (e a)} = Fintype.card {b // P b} := by
  rw [← Set.fintypeCard_eq_ncard]
  exact Fintype.card_congr e.subtypeEquivOfSubtype

/-- Reindex the accepted finite incidence bound by arbitrary finite types. -/
private theorem double_count_fintype {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) {N D : ℝ} (hD : 0 ≤ D)
    (hlower : ∀ b, N ≤ (Fintype.card {a // R a b} : ℝ))
    (hupper : ∀ a, (Fintype.card {b // R a b} : ℝ) ≤ D) :
    (Fintype.card β : ℝ) * N ≤ D * Fintype.card α := by
  have h := WangZahlLot.Obl.wz_nonflat_factored_improvement.bounded_incidence_count
    (fun i j => R ((Fintype.equivFin α).symm i) ((Fintype.equivFin β).symm j))
    (fun _ => True) (fun _ => True) (N := N) hD
    (fun j _ => by
      rw [ncard_equiv (Fintype.equivFin α).symm
        (fun a => R a ((Fintype.equivFin β).symm j))]
      exact hlower _)
    (fun i => by
      rw [ncard_equiv (Fintype.equivFin β).symm
        (fun b => R ((Fintype.equivFin α).symm i) b)]
      exact hupper _)
    (fun _ _ _ _ => trivial)
  simpa only [Set.ofPred_true, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin] using h

/-- Rich objects reduce to objects meeting small subfamilies. The hypothesis is the
geometric estimate one must supply separately, for every pair of sampled subfamilies. -/
theorem rich_count_of_sample_bound {α β ρ : Type*}
    [Fintype α] [Fintype β] [Fintype ρ] [Nonempty α] [Nonempty β]
    (P : ρ → α → Prop) (Q : ρ → β → Prop) (k l : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hk : ∀ r, Fintype.card α ≤ k * Fintype.card {a // P r a})
    (hl : ∀ r, Fintype.card β ≤ l * Fintype.card {b // Q r b})
    (hbound : ∀ (S : Finset α) (T : Finset β), S.card ≤ k → T.card ≤ l →
      (Fintype.card {r // (∃ a ∈ S, P r a) ∧ (∃ b ∈ T, Q r b)} : ℝ) ≤ M) :
    (Fintype.card ρ : ℝ) ≤ 4 * M := by
  classical
  let Ω := (Fin k → α) × (Fin l → β)
  let R : Ω → ρ → Prop := fun w r => (∃ t, P r (w.1 t)) ∧ (∃ t, Q r (w.2 t))
  have hupper (w : Ω) : (Fintype.card {r // R w r} : ℝ) ≤ M := by
    have h := hbound (Finset.univ.image w.1) (Finset.univ.image w.2)
      (by simpa using Finset.card_image_le (f := w.1) (s := Finset.univ))
      (by simpa using Finset.card_image_le (f := w.2) (s := Finset.univ))
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, exists_exists_eq_and,
      R] using h
  have hlower (r : ρ) : (Fintype.card Ω : ℝ) / 4 ≤
      Fintype.card {w // R w r} := quarter_samples_hit_both (P r) (Q r) k l (hk r) (hl r)
  have h := double_count_fintype R (N := (Fintype.card Ω : ℝ) / 4) hM
    (fun r => by simpa only [← Nat.card_eq_fintype_card] using hlower r)
    (fun w => by simpa only [← Nat.card_eq_fintype_card] using hupper w)
  have hΩ : 0 < (Fintype.card Ω : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith

/-- A power bound for objects meeting arbitrary subfamilies gives the corresponding
negative power of richness, with an explicit constant and the original local mass. -/
theorem rich_count_of_hereditary_power_bound {α β ρ : Type*}
    [Fintype α] [Fintype β] [Fintype ρ] [Nonempty α] [Nonempty β]
    (P : ρ → α → Prop) (Q : ρ → β → Prop) {μ p C : ℝ}
    (hμ : 0 < μ) (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hP : ∀ r, μ ≤ (Fintype.card {a // P r a} : ℝ))
    (hQ : ∀ r, μ ≤ (Fintype.card {b // Q r b} : ℝ))
    (hbound : ∀ (S : Finset α) (T : Finset β),
      (Fintype.card {r // (∃ a ∈ S, P r a) ∧ (∃ b ∈ T, Q r b)} : ℝ) ≤
        C * ((S.card : ℝ) + T.card) ^ p) :
    (Fintype.card ρ : ℝ) ≤
      4 * C * (2 * ((Fintype.card α : ℝ) + Fintype.card β) / μ) ^ p := by
  classical
  cases isEmpty_or_nonempty ρ with
  | inl h =>
    let _ := h
    simp only [Fintype.card_eq_zero, Nat.cast_zero]
    positivity
  | inr h =>
    let _ := h
    obtain ⟨r⟩ := h
    let k : ℕ := ⌈(Fintype.card α : ℝ) / μ⌉₊
    let l : ℕ := ⌈(Fintype.card β : ℝ) / μ⌉₊
    have hμα : μ ≤ Fintype.card α := (hP r).trans
      (Nat.cast_le.mpr (Fintype.card_subtype_le _))
    have hμβ : μ ≤ Fintype.card β := (hQ r).trans
      (Nat.cast_le.mpr (Fintype.card_subtype_le _))
    have hk (s : ρ) : Fintype.card α ≤ k * Fintype.card {a // P s a} := by
      have hkμ : (Fintype.card α : ℝ) ≤ (k : ℝ) * μ :=
        (div_le_iff₀ hμ).mp (Nat.le_ceil _)
      have hkp := mul_le_mul_of_nonneg_left (hP s) (Nat.cast_nonneg k)
      exact_mod_cast hkμ.trans hkp
    have hl (s : ρ) : Fintype.card β ≤ l * Fintype.card {b // Q s b} := by
      have hlμ : (Fintype.card β : ℝ) ≤ (l : ℝ) * μ :=
        (div_le_iff₀ hμ).mp (Nat.le_ceil _)
      have hlq := mul_le_mul_of_nonneg_left (hQ s) (Nat.cast_nonneg l)
      exact_mod_cast hlμ.trans hlq
    have hsmall : (Fintype.card ρ : ℝ) ≤ 4 * (C * ((k : ℝ) + l) ^ p) := by
      apply rich_count_of_sample_bound P Q k l (by positivity) hk hl
      intro S T hS hT
      exact (hbound S T).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast add_le_add hS hT) hp) hC)
    have hka : (k : ℝ) ≤ 2 * ((Fintype.card α : ℝ) / μ) := by
      have hc := (Nat.ceil_lt_add_one
        (div_nonneg (Nat.cast_nonneg (Fintype.card α)) hμ.le)).le
      have h1 := (one_le_div hμ).mpr hμα
      change (k : ℝ) ≤ _ at hc
      linarith
    have hlb : (l : ℝ) ≤ 2 * ((Fintype.card β : ℝ) / μ) := by
      have hc := (Nat.ceil_lt_add_one
        (div_nonneg (Nat.cast_nonneg (Fintype.card β)) hμ.le)).le
      have h1 := (one_le_div hμ).mpr hμβ
      change (l : ℝ) ≤ _ at hc
      linarith
    have hkl : (k : ℝ) + l ≤
        2 * ((Fintype.card α : ℝ) + Fintype.card β) / μ := by
      calc
        _ ≤ 2 * ((Fintype.card α : ℝ) / μ) +
          2 * ((Fintype.card β : ℝ) / μ) := add_le_add hka hlb
        _ = _ := by ring
    calc
      _ ≤ 4 * (C * ((k : ℝ) + l) ^ p) := hsmall
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hkl hp)
          (by positivity)

/-- Repeating reciprocal-density sampling in blocks makes the missed fraction
exponentially small in the number of blocks. -/
theorem block_samples_avoiding_le {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) (k t : ℕ)
    (hk : Fintype.card α ≤ k * Fintype.card {a // P a}) :
    (Fintype.card {f : Fin (k * t) → α // ∀ j, ¬ P (f j)} : ℝ) ≤
      (Fintype.card (Fin (k * t) → α) : ℝ) / 2 ^ t := by
  classical
  have hm : Fintype.card {a // P a} ≤ Fintype.card α := Fintype.card_subtype_le _
  have hmiss := miss_pow_le_half (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card α))
    (Nat.cast_le.mpr hm) k (by exact_mod_cast hk)
  rw [card_samples_avoiding, Nat.cast_pow, Nat.cast_sub hm, pow_mul,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  calc
    _ ≤ (((Fintype.card α : ℝ) ^ k) / 2) ^ t :=
      pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hm)) k) hmiss t
    _ = _ := by rw [div_pow, pow_mul]

/-- A finite range space has a small hitting sample. Its length is reciprocal density
times any binary logarithmic bound for the number of ranges. -/
theorem exists_hitting_sample {α ι : Type*} [Fintype α] [Fintype ι] [Nonempty α]
    (P : ι → α → Prop) (k t : ℕ)
    (hk : ∀ i, Fintype.card α ≤ k * Fintype.card {a // P i a})
    (ht : Fintype.card ι < 2 ^ t) :
    ∃ f : Fin (k * t) → α, ∀ i, ∃ j, P i (f j) := by
  classical
  by_contra! hbad
  let Ω := Fin (k * t) → α
  let R : ι → Ω → Prop := fun i f => ∀ j, ¬ P i (f j)
  have hlower (f : Ω) : (1 : ℝ) ≤ Fintype.card {i // R i f} := by
    obtain ⟨i, hi⟩ := hbad f
    have hc : 0 < Fintype.card {i // R i f} :=
      Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
    exact_mod_cast hc
  have hupper (i : ι) : (Fintype.card {f // R i f} : ℝ) ≤
      (Fintype.card Ω : ℝ) / 2 ^ t := block_samples_avoiding_le (P i) k t (hk i)
  have hc := double_count_fintype R (N := 1)
    (D := (Fintype.card Ω : ℝ) / 2 ^ t) (by positivity)
    (fun f => by simpa only [← Nat.card_eq_fintype_card] using hlower f)
    (fun i => by simpa only [← Nat.card_eq_fintype_card] using hupper i)
  have hΩ : 0 < (Fintype.card Ω : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have htr : (Fintype.card ι : ℝ) < (2 : ℝ) ^ t := by exact_mod_cast ht
  have hlt := mul_lt_mul_of_pos_left htr (div_pos hΩ (by positivity : 0 < (2 : ℝ) ^ t))
  have heq : (Fintype.card Ω : ℝ) / 2 ^ t * 2 ^ t = Fintype.card Ω := by
    exact div_mul_cancel₀ _ (by positivity)
  rw [heq] at hlt
  norm_num only [mul_one] at hc
  exact (not_lt_of_ge hc) hlt

/-- The image of the hitting sample is a hitting set of the same cardinality bound. -/
theorem exists_hitting_finset {α ι : Type*} [Fintype α] [Fintype ι] [Nonempty α]
    (P : ι → α → Prop) (k t : ℕ)
    (hk : ∀ i, Fintype.card α ≤ k * Fintype.card {a // P i a})
    (ht : Fintype.card ι < 2 ^ t) :
    ∃ S : Finset α, S.card ≤ k * t ∧ ∀ i, ∃ a ∈ S, P i a := by
  classical
  obtain ⟨f, hf⟩ := exists_hitting_sample P k t hk ht
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · simpa using Finset.card_image_le (f := f) (s := Finset.univ)
  · intro i
    obtain ⟨j, hj⟩ := hf i
    exact ⟨f j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hj⟩

/-- Three separated contact classes can be counted once their geometric common-neighbor
bound is supplied. The three right-hand classes need not be the same finite type. -/
theorem three_part_rich_count {α β₀ β₁ β₂ : Type*}
    [Fintype α] [Fintype β₀] [Fintype β₁] [Fintype β₂]
    (P₀ : α → β₀ → Prop) (P₁ : α → β₁ → Prop) (P₂ : α → β₂ → Prop)
    {L₀ L₁ L₂ C : ℝ} (_hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hC : 0 ≤ C)
    (h₀ : ∀ a, L₀ ≤ (Fintype.card {b // P₀ a b} : ℝ))
    (h₁ : ∀ a, L₁ ≤ (Fintype.card {b // P₁ a b} : ℝ))
    (h₂ : ∀ a, L₂ ≤ (Fintype.card {b // P₂ a b} : ℝ))
    (hcommon : ∀ b₀ b₁ b₂,
      (Fintype.card {a // P₀ a b₀ ∧ P₁ a b₁ ∧ P₂ a b₂} : ℝ) ≤ C) :
    (Fintype.card α : ℝ) * L₀ * L₁ * L₂ ≤
      C * Fintype.card β₀ * Fintype.card β₁ * Fintype.card β₂ := by
  classical
  let B := β₀ × β₁ × β₂
  let R : B → α → Prop := fun b a => P₀ a b.1 ∧ P₁ a b.2.1 ∧ P₂ a b.2.2
  have hlower (a : α) : L₀ * L₁ * L₂ ≤ (Fintype.card {b // R b a} : ℝ) := by
    have hc : Fintype.card {b // R b a} = Fintype.card {b // P₀ a b} *
        (Fintype.card {b // P₁ a b} * Fintype.card {b // P₂ a b}) := by
      change Fintype.card {b : β₀ × β₁ × β₂ //
        P₀ a b.1 ∧ (P₁ a b.2.1 ∧ P₂ a b.2.2)} = _
      rw [Fintype.card_congr (Equiv.subtypeProdEquivProd
        (p := P₀ a) (q := fun b : β₁ × β₂ => P₁ a b.1 ∧ P₂ a b.2)),
        Fintype.card_prod,
        Fintype.card_congr (Equiv.subtypeProdEquivProd (p := P₁ a) (q := P₂ a)),
        Fintype.card_prod]
    rw [hc, Nat.cast_mul, Nat.cast_mul, ← mul_assoc]
    exact mul_le_mul (mul_le_mul (h₀ a) (h₁ a) hL₁ (by positivity))
      (h₂ a) hL₂ (by positivity)
  have hu (b : B) : (Fintype.card {a // R b a} : ℝ) ≤ C := by
    simpa only [R, ← Nat.card_eq_fintype_card] using hcommon b.1 b.2.1 b.2.2
  have h := double_count_fintype R (N := L₀ * L₁ * L₂) hC
    (fun a => by simpa only [← Nat.card_eq_fintype_card] using hlower a)
    (fun b => by simpa only [← Nat.card_eq_fintype_card] using hu b)
  simpa only [B, Fintype.card_prod, Nat.cast_mul, mul_assoc] using h

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
