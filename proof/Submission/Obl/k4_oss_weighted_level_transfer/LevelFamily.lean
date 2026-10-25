import Submission.Obl.k4_oss_weighted_level_transfer.Levels

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace Submission.Obl.k4_oss_weighted_level_transfer

attribute [local instance] Classical.propDecidable

noncomputable def levelSet (S : Finset ℝ) (p : ℝ → ℝ) (b : ℝ) (M : ℕ) :
    Option (Fin M) → Finset ℝ
  | none => S
  | some k => level S p b k.val

def levelWeight (b : ℝ) (M : ℕ) : Option (Fin M) → ℝ
  | none => b ^ M
  | some k => b ^ k.val

lemma levelSet_subset (S : Finset ℝ) (p : ℝ → ℝ) (b : ℝ) (M : ℕ)
    (i : Option (Fin M)) : levelSet S p b M i ⊆ S := by
  cases i with
  | none => exact Finset.Subset.refl _
  | some k => exact level_subset _ _ _ _

lemma levelWeight_nonneg {b : ℝ} (hb : 0 ≤ b) (M : ℕ) (i : Option (Fin M)) :
    0 ≤ levelWeight b M i := by cases i <;> simp [levelWeight, pow_nonneg hb]

lemma level_family_cover {S : Finset ℝ} {p : ℝ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hp : ∀ x ∈ S, 0 ≤ p x) (hmass : ∑ x ∈ S, p x ≤ 1)
    (M : ℕ) {x : ℝ} (hx : x ∈ S) :
    p x ≤ ∑ i : Option (Fin M), if x ∈ levelSet S p b M i then levelWeight b M i else 0 := by
  have h := power_cover b (p x) hb (weight_le_one hp hmass hx) M
  simp only [Fintype.sum_option, levelSet, levelWeight, level, Finset.mem_filter,
    hx, true_and, ite_true]
  rw [Fin.sum_univ_eq_sum_range (fun k => if b ^ (k + 1) ≤ p x then b ^ k else 0) M]
  simpa only [add_comm] using h

lemma level_family_mass {S : Finset ℝ} {p : ℝ → ℝ} {b δ : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hp : ∀ x ∈ S, 0 ≤ p x)
    (hmass : ∑ x ∈ S, p x ≤ 1) (hδ1 : δ ≤ 1) (M : ℕ)
    (htail : b ^ M * (S.card : ℝ) ≤ δ) (i : Option (Fin M)) :
    levelWeight b M i * ((levelSet S p b M i).card : ℝ) ≤ 1 / b := by
  cases i with
  | none =>
    exact htail.trans (hδ1.trans ((le_div_iff₀ hb).mpr (by simpa using hb1)))
  | some k => exact level_mass_bound hb hp hmass _

lemma level_family_square {S : Finset ℝ} {p : ℝ → ℝ} {b δ Q : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hδ : 0 ≤ δ) (hQ : δ ≤ Q)
    (hsquare : ∑ x ∈ S, (p x) ^ 2 ≤ Q) (M : ℕ)
    (htail : b ^ M * (S.card : ℝ) ≤ δ) (i : Option (Fin M)) :
    (levelWeight b M i) ^ 2 * ((levelSet S p b M i).card : ℝ) ≤ Q / b ^ 2 := by
  cases i with
  | none =>
    have hw : b ^ M ≤ 1 := pow_le_one₀ hb.le hb1
    have hQ0 := hδ.trans hQ
    change (b ^ M) ^ 2 * (S.card : ℝ) ≤ Q / b ^ 2
    calc
      _ = b ^ M * (b ^ M * (S.card : ℝ)) := by ring
      _ ≤ 1 * δ := by gcongr
      _ ≤ Q := by simpa using hQ
      _ ≤ _ := (le_div_iff₀ (sq_pos_of_pos hb)).mpr (by
        have hbs : b ^ 2 ≤ 1 := pow_le_one₀ hb.le hb1
        nlinarith)
  | some k => exact level_square_bound hb hsquare _

lemma absorb_weight_cost {C δ a : ℝ} (hδ : 0 < δ) (hC : C * δ ^ a ≤ 1) :
    C * δ ^ (-a) ≤ δ ^ (-2 * a) := by
  calc
    _ = (C * δ ^ a) * δ ^ (-2 * a) := by
      rw [mul_assoc, ← Real.rpow_add hδ]
      congr 1
      congr 1
      ring
    _ ≤ 1 * δ ^ (-2 * a) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_pos_of_pos hδ _).le
    _ = _ := one_mul _

lemma level_cost_le {δ a θ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 13 * a ≤ θ) (hsmall : 2 * δ ^ a ≤ 1) :
    2 * δ ^ (-a) ≤ δ ^ (-θ) * δ ^ a * δ ^ (10 * a) := by
  calc
    _ ≤ δ ^ (-2 * a) := absorb_weight_cost hδ hsmall
    _ ≤ δ ^ (-θ + a + 10 * a) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    _ = _ := by rw [Real.rpow_add hδ, Real.rpow_add hδ]

lemma level_frostman {S : Finset ℝ} {p : ℝ → ℝ} {δ b s θ F η : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 < b) (hs : 0 ≤ s) (hθ : 0 ≤ θ)
    (hp : ∀ x ∈ S, 0 ≤ p x) (hF : 0 ≤ F)
    (hcap : ∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      ∑ y ∈ S.filter (fun y => dist y x ≤ u), p y ≤ F * u ^ s)
    (hcost : F ≤ δ ^ (-θ) * b * η) (k : ℕ)
    (hmass : η ≤ b ^ k * ((level S p b k).card : ℝ)) :
    ∀ x u : ℝ, δ ≤ u → ((level S p b k).filter (fun y => dist y x ≤ u)).card ≤
      δ ^ (-θ) * u ^ (s / 2) * ((level S p b k).card : ℝ) := by
  intro x u hδu
  have hu : 0 < u := hδ.trans_le hδu
  have hw : 0 < b ^ (k + 1) := pow_pos hb _
  have hN : 0 ≤ ((level S p b k).card : ℝ) := by positivity
  by_cases hu1 : u ≤ 1
  · have hexp : u ^ s ≤ u ^ (s / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hu hu1 (by linarith)
    have hcost0 : 0 ≤ δ ^ (-θ) * b * η := hF.trans hcost
    have hlocal := (level_local_bound hb.le hp k x u).trans (hcap x u hδu hu1)
    have htotal : b ^ (k + 1) *
        (((level S p b k).filter (fun y => dist y x ≤ u)).card : ℝ) ≤
        b ^ (k + 1) * (δ ^ (-θ) * u ^ (s / 2) * (level S p b k).card) := by
      calc
        _ ≤ F * u ^ s := hlocal
        _ ≤ (δ ^ (-θ) * b * η) * u ^ (s / 2) := by gcongr
        _ ≤ (δ ^ (-θ) * b * (b ^ k * (level S p b k).card)) * u ^ (s / 2) := by gcongr
        _ = _ := by rw [pow_succ]; ring
    exact (mul_le_mul_iff_right₀ hw).mp htotal
  · have hule : 1 ≤ u := (lt_of_not_ge hu1).le
    have hup : 1 ≤ u ^ (s / 2) := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hule (by linarith : 0 ≤ s / 2)
    have hδp : 1 ≤ δ ^ (-θ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    have hcard : (((level S p b k).filter (fun y => dist y x ≤ u)).card : ℝ) ≤
        (level S p b k).card := by exact_mod_cast Finset.card_filter_le _ _
    calc
      _ ≤ ((level S p b k).card : ℝ) := hcard
      _ = 1 * 1 * ((level S p b k).card : ℝ) := by ring
      _ ≤ _ := by gcongr

lemma level_family_frostman {S : Finset ℝ} {p : ℝ → ℝ} {δ a s θ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 < a) (ha1 : 10 * a ≤ 1)
    (hs : 0 ≤ s) (hθ : 13 * a ≤ θ) (hsmall : 2 * δ ^ a ≤ 1)
    (hp : ∀ x ∈ S, 0 ≤ p x)
    (hcap : ∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      ∑ y ∈ S.filter (fun y => dist y x ≤ u), p y ≤ 2 * δ ^ (-a) * u ^ s)
    (M : ℕ) (htail : (δ ^ a) ^ M * (S.card : ℝ) ≤ δ)
    (i : Option (Fin M))
    (hmass : δ ^ (10 * a) < levelWeight (δ ^ a) M i * (levelSet S p (δ ^ a) M i).card) :
    ∀ x u : ℝ, δ ≤ u → ((levelSet S p (δ ^ a) M i).filter (fun y => dist y x ≤ u)).card ≤
      δ ^ (-θ) * u ^ (s / 2) * ((levelSet S p (δ ^ a) M i).card : ℝ) := by
  cases i with
  | none =>
    have hh : δ ≤ δ ^ (10 * a) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 ha1
    exact False.elim (not_lt_of_ge (htail.trans hh) hmass)
  | some k =>
    exact level_frostman hδ hδ1 (Real.rpow_pos_of_pos hδ _) hs (by linarith)
      hp (by positivity) hcap (level_cost_le hδ hδ1 hθ hsmall) _ hmass.le

end Submission.Obl.k4_oss_weighted_level_transfer
