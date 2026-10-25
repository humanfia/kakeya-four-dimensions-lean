-- Adapted from this LOT tree, o040/x0118 Exponents.lean; accepted radius results are imported.
import Submission.Obl.k4_matching_switching_target_certificate.Exponents

/-!
# Jet scales in the form of the frozen children of o040

`jetRadius J β a = sSup ((fun j => (a - β j) / j) '' Icc 1 J)` and
`jetAccuracy r j a = sSup ((fun x => x - j * r x) '' Icc 0 a)` are, after beta
reduction, exactly the functions `r` and `l` of the frozen statements of o055 and o056.
The inequalities `a02:jet-scales`--`a02:active-piece` of the paper are proved here.

Adapted from session x0047's `Submission/Lib/K4MatchingTools/JetScales.lean`
(o015, branch x0047, developed in this workspace), restated for the `sSup` form of the
radius used in the frozen children.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set
open Submission.Obl.k4_matching_trimmed_grid

/-- The largest time exponent required by the Taylor terms of orders `1, ..., J`. -/
noncomputable abbrev jetRadius := radius

/-- The accuracy of a `j`-th derivative bin at value scale `a`: the greatest preceding
value of `x - j r(x)`, so that the jet partitions are nested. -/
noncomputable def jetAccuracy (r : ℝ → ℝ) (j : ℕ) (a : ℝ) : ℝ :=
  sSup ((fun x : ℝ => x - (j : ℝ) * r x) '' Icc 0 a)

lemma jetRadius_eq_sup' {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ) (a : ℝ) :
    jetRadius J β a = (Finset.Icc 1 J).sup' (Finset.nonempty_Icc.mpr hJ)
      (fun j => (a - β j) / (j : ℝ)) := by
  have hfin : ((fun j : ℕ => (a - β j) / (j : ℝ)) '' Set.Icc 1 J).Finite :=
    (Set.finite_Icc 1 J).image _
  apply le_antisymm
  · apply csSup_le ((Set.nonempty_Icc.mpr hJ).image _)
    rintro _ ⟨j, hj, rfl⟩
    exact Finset.le_sup' (fun k : ℕ => (a - β k) / (k : ℝ)) (Finset.mem_Icc.mpr hj)
  · apply Finset.sup'_le
    intro j hj
    exact le_csSup hfin.bddAbove (mem_image_of_mem _ (Finset.mem_Icc.mp hj))

lemma term_le_jetRadius {J : ℕ} (β : ℕ → ℝ) (a : ℝ) {j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J) :
    (a - β j) / (j : ℝ) ≤ jetRadius J β a :=
  line_le_radius hj hjJ a

lemma jetRadius_le {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ) (a c : ℝ)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ J → (a - β j) / (j : ℝ) ≤ c) :
    jetRadius J β a ≤ c :=
  radius_le hJ h

lemma exists_jetRadius_eq {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ) (a : ℝ) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ jetRadius J β a = (a - β j) / (j : ℝ) :=
  radius_max hJ a

lemma continuous_jetRadius {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ) :
    Continuous (jetRadius J β) := by
  have : jetRadius J β = fun a => (Finset.Icc 1 J).sup' (Finset.nonempty_Icc.mpr hJ)
      (fun j => (a - β j) / (j : ℝ)) := funext fun a => jetRadius_eq_sup' hJ β a
  rw [this]
  apply Continuous.finset_sup'_apply
  intro j _
  exact (continuous_id.sub continuous_const).div_const _

lemma monotone_jetRadius {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ) :
    Monotone (jetRadius J β) :=
  radius_mono hJ

lemma jetRadius_zero {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    (hβ : ∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j)
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0) :
    jetRadius J β 0 = 0 :=
  radius_zero hJ hβ ⟨k, hk, hkJ, hβk⟩

lemma div_le_jetRadius_of_zero {J : ℕ} (β : ℕ → ℝ)
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0) (a : ℝ) :
    a / (k : ℝ) ≤ jetRadius J β a := by
  simpa [hβk] using term_le_jetRadius (J := J) β a hk hkJ

lemma jetRadius_nonneg {J : ℕ} (β : ℕ → ℝ)
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0)
    {a : ℝ} (ha : 0 ≤ a) : 0 ≤ jetRadius J β a :=
  (radius_lower hk hkJ hβk ha).1

lemma jetRadius_le_self {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    (hβ : ∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j)
    {a : ℝ} (ha : 0 ≤ a) : jetRadius J β a ≤ a := by
  apply jetRadius_le hJ
  intro j hj hjJ
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < j)).mpr
  nlinarith [hβ j hj hjJ]

lemma continuous_accuracyIntegrand {r : ℝ → ℝ} (hr : Continuous r) (j : ℕ) :
    Continuous (fun x : ℝ => x - (j : ℝ) * r x) :=
  continuous_id.sub (continuous_const.mul hr)

lemma exists_jetAccuracy_eq {r : ℝ → ℝ} (hr : Continuous r) (j : ℕ)
    {a : ℝ} (ha : 0 ≤ a) :
    ∃ x ∈ Icc 0 a, jetAccuracy r j a = x - (j : ℝ) * r x :=
  isCompact_Icc.exists_sSup_image_eq (nonempty_Icc.mpr ha)
    (continuous_accuracyIntegrand hr j).continuousOn

lemma le_jetAccuracy {r : ℝ → ℝ} (hr : Continuous r) (j : ℕ)
    {a x : ℝ} (hx : x ∈ Icc 0 a) : x - (j : ℝ) * r x ≤ jetAccuracy r j a :=
  le_csSup (isCompact_Icc.bddAbove_image (continuous_accuracyIntegrand hr j).continuousOn)
    (mem_image_of_mem _ hx)

lemma jetAccuracy_le {r : ℝ → ℝ} (j : ℕ) {a c : ℝ} (ha : 0 ≤ a)
    (h : ∀ x ∈ Icc 0 a, x - (j : ℝ) * r x ≤ c) : jetAccuracy r j a ≤ c := by
  apply csSup_le ((nonempty_Icc.mpr ha).image _)
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

lemma jetAccuracy_nonneg {r : ℝ → ℝ} (hr : Continuous r) (hr0 : r 0 = 0)
    (j : ℕ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ jetAccuracy r j a := by
  simpa [hr0] using le_jetAccuracy hr j (show (0 : ℝ) ∈ Icc 0 a from ⟨le_rfl, ha⟩)

lemma jetAccuracy_zero_order {r : ℝ → ℝ} (hr : Continuous r)
    {a : ℝ} (ha : 0 ≤ a) : jetAccuracy r 0 a = a := by
  apply le_antisymm
  · apply jetAccuracy_le 0 ha
    intro x hx
    simpa using hx.2
  · simpa using le_jetAccuracy hr 0 (show a ∈ Icc 0 a from ⟨ha, le_rfl⟩)

lemma jetAccuracy_mono {r : ℝ → ℝ} (hr : Continuous r) (j : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    jetAccuracy r j a ≤ jetAccuracy r j b := by
  obtain ⟨x, hx, heq⟩ := exists_jetAccuracy_eq hr j ha
  rw [heq]
  exact le_jetAccuracy hr j ⟨hx.1, hx.2.trans hab⟩

lemma jetAccuracy_le_beta {J : ℕ} (β : ℕ → ℝ)
    {a : ℝ} (ha : 0 ≤ a) {j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J) :
    jetAccuracy (jetRadius J β) j a ≤ β j :=
  accuracy_le_beta hj hjJ ha

/-- Taylor translation between accuracy bins loses at most `i * r(a)` in the exponent. -/
lemma jetAccuracy_translation {r : ℝ → ℝ} (hr : Continuous r) (hm : Monotone r)
    (j i : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    jetAccuracy r j a - jetAccuracy r (j + i) a ≤ (i : ℝ) * r a := by
  obtain ⟨x, hx, heq⟩ := exists_jetAccuracy_eq hr j ha
  have h := le_jetAccuracy hr (j + i) hx
  have hm' := mul_le_mul_of_nonneg_left (hm hx.2) (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
  rw [heq]
  push_cast at h
  nlinarith

/-- The unused Taylor remainder decays at least as fast as every retained accuracy. -/
lemma jetAccuracy_le_remainder {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0)
    {a : ℝ} (ha : 0 ≤ a) {j : ℕ} (hj : j ≤ J) :
    jetAccuracy (jetRadius J β) j a ≤ ((J : ℝ) + 1 - (j : ℝ)) * jetRadius J β a := by
  have hr := continuous_jetRadius hJ β
  have hm := monotone_jetRadius hJ β
  apply jetAccuracy_le j ha
  intro x hx
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hkJ' : (k : ℝ) ≤ J := by exact_mod_cast hkJ
  have hjJ' : (j : ℝ) ≤ J := by exact_mod_cast hj
  have hlow := (div_le_iff₀ hk').mp (div_le_jetRadius_of_zero (J := J) β hk hkJ hβk x)
  have hnonneg := jetRadius_nonneg (J := J) β hk hkJ hβk hx.1
  have hmono := hm hx.2
  nlinarith

/-- Below an active order, the running maximum is attained at the current scale. -/
lemma jetAccuracy_eq_at_active {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {a : ℝ} (ha : 0 ≤ a) {m j : ℕ} (hm : 1 ≤ m) (hmJ : m ≤ J) (hjm : j ≤ m)
    (hactive : jetRadius J β a = (a - β m) / (m : ℝ)) :
    jetAccuracy (jetRadius J β) j a = a - (j : ℝ) * jetRadius J β a :=
  accuracy_eq_active ha hm hmJ hactive hjm

lemma jetAccuracy_active_order {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {a : ℝ} (ha : 0 ≤ a) {m : ℕ} (hm : 1 ≤ m) (hmJ : m ≤ J)
    (hactive : jetRadius J β a = (a - β m) / (m : ℝ)) :
    jetAccuracy (jetRadius J β) m a = β m :=
  accuracy_active_order ha hm hmJ hactive

/-- On an active piece, `l_j(a) = β_m + (m - j) r(a)` for `j ≤ m`. -/
lemma jetAccuracy_eq_beta_add {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {a : ℝ} (ha : 0 ≤ a) {m j : ℕ} (hm : 1 ≤ m) (hmJ : m ≤ J) (hjm : j ≤ m)
    (hactive : jetRadius J β a = (a - β m) / (m : ℝ)) :
    jetAccuracy (jetRadius J β) j a = β m + ((m : ℝ) - (j : ℝ)) * jetRadius J β a := by
  rw [jetAccuracy_eq_at_active hJ β ha hm hmJ hjm hactive]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have heq := (eq_div_iff hm'.ne').mp hactive
  nlinarith

/-- On an active piece, `l_j` increases by `(1 - j/m)` times the increase of the level,
for `j ≤ m`: `l_j(c) - l_j(a) = (c - a) (1 - j/m)`. -/
lemma jetAccuracy_sub_at_active {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {m j : ℕ} (hm : 1 ≤ m) (hmJ : m ≤ J) (hjm : j ≤ m)
    (hacta : jetRadius J β a = (a - β m) / (m : ℝ))
    (hactc : jetRadius J β c = (c - β m) / (m : ℝ)) :
    jetAccuracy (jetRadius J β) j c - jetAccuracy (jetRadius J β) j a =
      (c - a) * (1 - (j : ℝ) / (m : ℝ)) := by
  change accuracy J β j c - accuracy J β j a = _
  rw [accuracy_active_sub ha hc hm hmJ hacta hactc hjm]
  ring

end Submission.Obl.k4_matching_switching_target_certificate
