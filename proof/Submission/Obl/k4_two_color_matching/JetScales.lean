import Mathlib

/-!
# The exponent geometry in the two-color matching argument

The definitions and inequalities here are those in the supplied paper,
Lemma 3.3, equations `a02:jet-scales`--`a02:active-piece`.
-/

namespace Submission.Obl.k4_two_color_matching

open Set

/-- The largest time exponent required by the Taylor terms of orders `1,...,J`. -/
noncomputable def jetRadius (J : ℕ) (hJ : 1 ≤ J) (β : ℕ → ℝ) (a : ℝ) : ℝ :=
  (Finset.Icc 1 J).sup' (Finset.nonempty_Icc.mpr hJ)
    (fun j => (a - β j) / (j : ℝ))

/-- Keep the greatest preceding accuracy, so that the jet partitions are nested. -/
noncomputable def jetAccuracy (r : ℝ → ℝ) (j : ℕ) (a : ℝ) : ℝ :=
  sSup ((fun x : ℝ => x - (j : ℝ) * r x) '' Icc 0 a)

lemma term_le_jetRadius {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ) (a : ℝ)
    {j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J) :
    (a - β j) / (j : ℝ) ≤ jetRadius J hJ β a :=
  Finset.le_sup' (fun k : ℕ => (a - β k) / (k : ℝ)) (Finset.mem_Icc.mpr ⟨hj, hjJ⟩)

lemma jetRadius_le {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ) (a c : ℝ)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ J → (a - β j) / (j : ℝ) ≤ c) :
    jetRadius J hJ β a ≤ c :=
  Finset.sup'_le _ _ fun j hj => h j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2

lemma exists_jetRadius_eq {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ) (a : ℝ) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ jetRadius J hJ β a = (a - β j) / (j : ℝ) := by
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_Icc.mpr hJ)
    (fun j : ℕ => (a - β j) / (j : ℝ))
  exact ⟨j, (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2, heq⟩

lemma continuous_jetRadius {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ) :
    Continuous (jetRadius J hJ β) := by
  apply Continuous.finset_sup'_apply
  intro j hj
  exact (continuous_id.sub continuous_const).div_const _

lemma monotone_jetRadius {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ) :
    Monotone (jetRadius J hJ β) := by
  intro a b hab
  apply jetRadius_le
  intro j hj hjJ
  exact (div_le_div_of_nonneg_right (sub_le_sub_right hab _) (Nat.cast_nonneg j)).trans
    (term_le_jetRadius hJ β b hj hjJ)

lemma jetRadius_zero {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    (hβ : ∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j)
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0) :
    jetRadius J hJ β 0 = 0 := by
  apply le_antisymm
  · apply jetRadius_le
    intro j hj hjJ
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hβ j hj hjJ]) (Nat.cast_nonneg j)
  · simpa [hβk] using term_le_jetRadius hJ β 0 hk hkJ

lemma div_le_jetRadius_of_zero {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0) (a : ℝ) :
    a / (k : ℝ) ≤ jetRadius J hJ β a := by
  simpa [hβk] using term_le_jetRadius hJ β a hk hkJ

lemma jetRadius_nonneg {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0)
    {a : ℝ} (ha : 0 ≤ a) : 0 ≤ jetRadius J hJ β a :=
  (div_nonneg ha (Nat.cast_nonneg k)).trans
    (div_le_jetRadius_of_zero hJ β hk hkJ hβk a)

lemma jetRadius_pos {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0)
    {a : ℝ} (ha : 0 < a) : 0 < jetRadius J hJ β a := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  exact (div_pos ha hk').trans_le (div_le_jetRadius_of_zero hJ β hk hkJ hβk a)

lemma jetRadius_le_self {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    (hβ : ∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j)
    {a : ℝ} (ha : 0 ≤ a) : jetRadius J hJ β a ≤ a := by
  apply jetRadius_le
  intro j hj hjJ
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < j)).mpr
  nlinarith [hβ j hj hjJ]

lemma convexOn_jetRadius {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ) :
    ConvexOn ℝ univ (jetRadius J hJ β) := by
  refine ⟨convex_univ, ?_⟩
  intro a ha b hb u v hu hv huv
  apply jetRadius_le
  intro j hj hjJ
  have h₁ := term_le_jetRadius hJ β a hj hjJ
  have h₂ := term_le_jetRadius hJ β b hj hjJ
  have heq : (u * a + v * b - β j) / (j : ℝ) =
      u * ((a - β j) / (j : ℝ)) + v * ((b - β j) / (j : ℝ)) := by
    rw [sub_div, add_div, mul_div_assoc, mul_div_assoc, sub_div, sub_div]
    have hc := congrArg (fun t : ℝ => t * (β j / (j : ℝ))) huv
    simp only [one_mul] at hc
    nlinarith
  simpa only [smul_eq_mul, heq] using add_le_add
    (mul_le_mul_of_nonneg_left h₁ hu) (mul_le_mul_of_nonneg_left h₂ hv)

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

lemma jetAccuracy_at_zero {r : ℝ → ℝ} (hr0 : r 0 = 0) (j : ℕ) :
    jetAccuracy r j 0 = 0 := by simp [jetAccuracy, hr0]

lemma jetAccuracy_mono {r : ℝ → ℝ} (hr : Continuous r) (j : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    jetAccuracy r j a ≤ jetAccuracy r j b := by
  obtain ⟨x, hx, heq⟩ := exists_jetAccuracy_eq hr j ha
  rw [heq]
  exact le_jetAccuracy hr j ⟨hx.1, hx.2.trans hab⟩

lemma jetAccuracy_le_beta {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {a : ℝ} (ha : 0 ≤ a) {j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J) :
    jetAccuracy (jetRadius J hJ β) j a ≤ β j := by
  apply jetAccuracy_le j ha
  intro x hx
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have h := (div_le_iff₀ hj').mp (term_le_jetRadius hJ β x hj hjJ)
  nlinarith

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

/-- The unused Taylor remainder decays strictly faster than every retained accuracy. -/
lemma jetAccuracy_remainder_gap {r : ℝ → ℝ} (hr : Continuous r) (hm : Monotone r)
    (hr0 : r 0 = 0) {D L : ℝ} (hD : 0 < D) (hDL : D < L)
    (hlower : ∀ x : ℝ, 0 ≤ x → x ≤ D * r x)
    {a : ℝ} (ha : 0 < a) (j : ℕ) (hj : (j : ℝ) < L) :
    jetAccuracy r j a < (L - (j : ℝ)) * r a := by
  have hra : 0 < r a := by nlinarith [hlower a ha.le]
  obtain ⟨x, hx, heq⟩ := exists_jetAccuracy_eq hr j ha.le
  rw [heq]
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · rw [← hx0, hr0]
    simpa using mul_pos (sub_pos.mpr hj) hra
  · have hrx : 0 < r x := by nlinarith [hlower x hx.1]
    have hstrict : x < L * r x := by nlinarith [hlower x hx.1]
    have hmove := mul_le_mul_of_nonneg_left (hm hx.2) (sub_nonneg.mpr hj.le)
    nlinarith

lemma jetRadius_remainder_gap {J D : ℕ} (hJ : 1 ≤ J) (hD : 1 ≤ D) (hDJ : D < J)
    (β : ℕ → ℝ)
    (hβ : ∀ k : ℕ, 1 ≤ k → k ≤ J → 0 ≤ β k)
    {k : ℕ} (hk : 1 ≤ k) (hkD : k ≤ D) (hβk : β k = 0)
    {a : ℝ} (ha : 0 < a) {j : ℕ} (hj : j ≤ J) :
    jetAccuracy (jetRadius J hJ β) j a < ((J : ℝ) + 1 - (j : ℝ)) *
      jetRadius J hJ β a := by
  have hDJ' : D ≤ J := hDJ.le
  have hkJ := hkD.trans hDJ'
  apply jetAccuracy_remainder_gap (continuous_jetRadius hJ β) (monotone_jetRadius hJ β)
    (jetRadius_zero hJ β hβ hk hkJ hβk) (by exact_mod_cast hD : (0 : ℝ) < D)
    (by exact_mod_cast (show D < J + 1 by omega)) _ ha j (by exact_mod_cast (by omega : j < J + 1))
  intro x hx
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hlow := (div_le_iff₀ hk').mp (div_le_jetRadius_of_zero hJ β hk hkJ hβk x)
  have hnonneg := jetRadius_nonneg hJ β hk hkJ hβk hx
  have hkD' : (k : ℝ) ≤ D := by exact_mod_cast hkD
  nlinarith

/-- Below an active order, the running maximum is attained at the current scale. -/
lemma jetAccuracy_eq_at_active {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {a : ℝ} (ha : 0 ≤ a) {m j : ℕ} (hm : 1 ≤ m) (hmJ : m ≤ J) (hjm : j ≤ m)
    (hactive : jetRadius J hJ β a = (a - β m) / (m : ℝ)) :
    jetAccuracy (jetRadius J hJ β) j a = a - (j : ℝ) * jetRadius J hJ β a := by
  apply le_antisymm
  · apply jetAccuracy_le j ha
    intro x hx
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hjm' : (j : ℝ) ≤ m := by exact_mod_cast hjm
    have hlow := (div_le_iff₀ hm').mp (term_le_jetRadius hJ β x hm hmJ)
    have heq := (eq_div_iff hm'.ne').mp hactive
    have hmono := monotone_jetRadius hJ β hx.2
    nlinarith
  · exact le_jetAccuracy (continuous_jetRadius hJ β) j ⟨ha, le_rfl⟩

lemma jetAccuracy_active_order {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {a : ℝ} (ha : 0 ≤ a) {m : ℕ} (hm : 1 ≤ m) (hmJ : m ≤ J)
    (hactive : jetRadius J hJ β a = (a - β m) / (m : ℝ)) :
    jetAccuracy (jetRadius J hJ β) m a = β m := by
  rw [jetAccuracy_eq_at_active hJ β ha hm hmJ le_rfl hactive]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have heq := (eq_div_iff hm'.ne').mp hactive
  nlinarith

/-- At a point preceded by an interval of the same active order, the higher
accuracies have a strict gap. Two active points already witness that gap. -/
lemma jetAccuracy_high_gap {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {x a : ℝ} (hx : 0 ≤ x) (hxa : x < a) {m j : ℕ} (hm : 1 ≤ m) (hmj : m < j)
    (hactive_x : jetRadius J hJ β x = (x - β m) / (m : ℝ))
    (hactive_a : jetRadius J hJ β a = (a - β m) / (m : ℝ)) :
    a - (j : ℝ) * jetRadius J hJ β a < jetAccuracy (jetRadius J hJ β) j a := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmj' : (m : ℝ) < j := by exact_mod_cast hmj
  have h₁ := (eq_div_iff hm'.ne').mp hactive_x
  have h₂ := (eq_div_iff hm'.ne').mp hactive_a
  have hlow := le_jetAccuracy (continuous_jetRadius hJ β) j ⟨hx, hxa.le⟩
  have hrdiff : 0 < jetRadius J hJ β a - jetRadius J hJ β x := by nlinarith
  nlinarith

lemma jetAccuracy_higher_translation_gap {J : ℕ} (hJ : 1 ≤ J) (β : ℕ → ℝ)
    {x a : ℝ} (hx : 0 ≤ x) (hxa : x < a) {m i : ℕ} (hm : 1 ≤ m) (hi : 1 ≤ i)
    (hactive_x : jetRadius J hJ β x = (x - β m) / (m : ℝ))
    (hactive_a : jetRadius J hJ β a = (a - β m) / (m : ℝ)) :
    β m < jetAccuracy (jetRadius J hJ β) (m + i) a +
      (i : ℝ) * jetRadius J hJ β a := by
  have hgap := jetAccuracy_high_gap hJ β hx hxa hm (by omega : m < m + i)
    hactive_x hactive_a
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have heq := (eq_div_iff hm'.ne').mp hactive_a
  push_cast at hgap
  nlinarith

end Submission.Obl.k4_two_color_matching
