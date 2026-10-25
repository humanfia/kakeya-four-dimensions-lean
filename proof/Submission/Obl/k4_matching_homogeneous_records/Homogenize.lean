import Mathlib

/-!
# Homogenizing a finite record tree

A finite set `L` of leaves carries nested labellings `G 0, …, G q` (equal `G b`-labels force
equal `G a`-labels for `a ≤ b`) and nonnegative weights. Processing the levels from the finest
to the coarsest, we keep at each level the dyadic class of children counts of largest weight.
This loses at most a factor `Nat.log 2 |L| + 1` of the weight per level, and in the kept set
every level-`a` label has, up to the factor `2 ^ (b - a)`, the average number of level-`b`
descendants.
-/

namespace Submission.Obl.k4_matching_homogeneous_records

open Finset

variable {α : Type*}

/-- The number of level-`b` labels, inside `T`, below the level-`a` label of `x`. -/
def desc (G : ℕ → α → ℕ) (T : Finset α) (a b : ℕ) (x : α) : ℕ :=
  ((T.filter (fun y => G a y = G a x)).image (G b)).card

/-- Splitting the level-`b'` labels of `U` along the coarser labels `G b`. -/
lemma card_image_eq_sum_fiber (G : ℕ → α → ℕ) (U : Finset α) (b b' : ℕ)
    (hnest : ∀ x ∈ U, ∀ y ∈ U, G b' x = G b' y → G b x = G b y) :
    (U.image (G b')).card =
      ∑ c ∈ U.image (G b), ((U.filter (fun y => G b y = c)).image (G b')).card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext e
    simp only [mem_image, mem_biUnion, mem_filter]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨G b y, ⟨y, hy, rfl⟩, y, ⟨hy, rfl⟩, rfl⟩
    · rintro ⟨c, _, y, ⟨hy, _⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  · intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    simp only [mem_image, mem_filter] at he he'
    obtain ⟨y, ⟨hy, hyc⟩, rfl⟩ := he
    obtain ⟨y', ⟨hy', hyc'⟩, he⟩ := he'
    exact hcc' (by rw [← hyc, ← hyc']; exact (hnest y' hy' y hy he).symm)

lemma desc_pos (G : ℕ → α → ℕ) {T : Finset α} (a b : ℕ) {x : α} (hx : x ∈ T) :
    0 < desc G T a b x := by
  unfold desc
  apply Finset.card_pos.2
  exact ⟨G b x, Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hx, rfl⟩, rfl⟩⟩

lemma desc_le_card (G : ℕ → α → ℕ) (T : Finset α) (a b : ℕ) (x : α) :
    desc G T a b x ≤ T.card :=
  (Finset.card_image_le).trans (Finset.card_filter_le _ _)

lemma desc_self (G : ℕ → α → ℕ) {T : Finset α} (a : ℕ) {x : α} (hx : x ∈ T) :
    desc G T a a x = 1 := by
  unfold desc
  rw [Finset.card_eq_one]
  refine ⟨G a x, ?_⟩
  ext e
  simp only [mem_image, mem_filter, mem_singleton]
  constructor
  · rintro ⟨y, ⟨_, hy⟩, rfl⟩
    exact hy
  · rintro rfl
    exact ⟨x, ⟨hx, rfl⟩, rfl⟩

/-- Nestedness of the labels on a finite set. -/
def Nested (G : ℕ → α → ℕ) (q : ℕ) (L : Finset α) : Prop :=
  ∀ a b, a ≤ b → b ≤ q → ∀ x ∈ L, ∀ y ∈ L, G b x = G b y → G a x = G a y

lemma Nested.mono {G : ℕ → α → ℕ} {q : ℕ} {L T : Finset α} (h : Nested G q L) (hT : T ⊆ L) :
    Nested G q T :=
  fun a b hab hb x hx y hy => h a b hab hb x (hT hx) y (hT hy)

/-- If the level-`k` label of `y` is that of `x`, the level-`k` fibres through `x` and `y` are
the same. -/
lemma filter_eq_of_label (G : ℕ → α → ℕ) (T : Finset α) (k : ℕ) {x y : α}
    (h : G k y = G k x) :
    T.filter (fun z => G k z = G k y) = T.filter (fun z => G k z = G k x) := by
  rw [h]

/-- One step of the homogenization: restrict to the heaviest dyadic class of children counts
at level `m`. -/
lemma homogenize_step (G : ℕ → α → ℕ) (q : ℕ) (L T : Finset α) (hTL : T ⊆ L)
    (w : α → ℝ) (hnest : Nested G q L) (m : ℕ) (hm : m < q) :
    ∃ T' ⊆ T, (∑ x ∈ T, w x) ≤ ((Nat.log 2 L.card + 1 : ℕ) : ℝ) * ∑ x ∈ T', w x ∧
      (∃ g : ℕ, ∀ x ∈ T', 2 ^ g ≤ desc G T' m (m + 1) x ∧ desc G T' m (m + 1) x < 2 ^ (g + 1)) ∧
      (∀ k, m ≤ k → k ≤ q → ∀ x ∈ T',
        T'.filter (fun z => G k z = G k x) = T.filter (fun z => G k z = G k x)) := by
  set K := Nat.log 2 L.card with hK
  let g : α → ℕ := fun x => Nat.log 2 (desc G T m (m + 1) x)
  have hmaps : ∀ x ∈ T, g x ∈ Finset.range (K + 1) := by
    intro x _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.log_mono_right ((desc_le_card G T m (m + 1) x).trans (Finset.card_le_card hTL))
  have hsum : (Finset.range (K + 1)).card • ((∑ x ∈ T, w x) / ((K + 1 : ℕ) : ℝ)) ≤
      ∑ x ∈ T, w x := by
    rw [Finset.card_range, nsmul_eq_mul]
    have : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
    rw [mul_div_cancel₀ _ this.ne']
  obtain ⟨g₀, _, hg₀⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hmaps
    ⟨0, by simp⟩ hsum
  set T' := T.filter (fun x => g x = g₀) with hT'
  -- `T'` is saturated for the level-`m` labels of `T`
  have hsat : ∀ x ∈ T', ∀ y ∈ T, G m y = G m x → y ∈ T' := by
    intro x hx y hy hyx
    rw [hT', Finset.mem_filter] at hx ⊢
    refine ⟨hy, ?_⟩
    have : desc G T m (m + 1) y = desc G T m (m + 1) x := by
      unfold desc
      rw [filter_eq_of_label G T m hyx]
    simp only [g, this]
    exact hx.2
  have hfilt : ∀ k, m ≤ k → k ≤ q → ∀ x ∈ T',
      T'.filter (fun z => G k z = G k x) = T.filter (fun z => G k z = G k x) := by
    intro k hmk hkq x hx
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hzx⟩
      exact ⟨Finset.filter_subset _ _ hz, hzx⟩
    · rintro ⟨hz, hzx⟩
      have hxT : x ∈ T := Finset.filter_subset _ _ hx
      exact ⟨hsat x hx z hz (hnest m k hmk hkq z (hTL hz) x (hTL hxT) hzx), hzx⟩
  refine ⟨T', Finset.filter_subset _ _, ?_, ⟨g₀, ?_⟩, hfilt⟩
  · have hpos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hpos] at hg₀
    linarith
  · intro x hx
    have hxT : x ∈ T := Finset.filter_subset _ _ hx
    have hgx : g x = g₀ := (Finset.mem_filter.1 hx).2
    have hd : desc G T' m (m + 1) x = desc G T m (m + 1) x := by
      unfold desc
      rw [hfilt m le_rfl hm.le x hx]
    rw [hd, ← hgx]
    exact ⟨Nat.pow_log_le_self 2 (desc_pos G m (m + 1) hxT).ne',
      Nat.lt_pow_succ_log_self (by norm_num) _⟩

/-- The homogenization, after processing the `n` finest levels. -/
lemma homogenize_aux (G : ℕ → α → ℕ) (q : ℕ) (L : Finset α) (w : α → ℝ)
    (hnest : Nested G q L) :
    ∀ n, n ≤ q → ∃ T ⊆ L, (∑ x ∈ L, w x) ≤ ((Nat.log 2 L.card + 1 : ℕ) : ℝ) ^ n * ∑ x ∈ T, w x ∧
      ∃ B : ℕ → ℕ, ∀ k, q - n ≤ k → k < q → ∀ x ∈ T,
        B k ≤ desc G T k (k + 1) x ∧ desc G T k (k + 1) x < 2 * B k := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨L, subset_rfl, by simp, fun _ => 0, ?_⟩
    intro k hk hkq
    omega
  | succ n ih =>
    intro hn
    obtain ⟨T, hTL, hmass, B, hB⟩ := ih (by omega)
    obtain ⟨T', hT'T, hmass', ⟨g, hg⟩, hfilt⟩ :=
      homogenize_step G q L T hTL w hnest (q - (n + 1)) (by omega)
    refine ⟨T', hT'T.trans hTL, ?_, fun k => if k = q - (n + 1) then 2 ^ g else B k, ?_⟩
    · have hK : (0 : ℝ) ≤ ((Nat.log 2 L.card + 1 : ℕ) : ℝ) ^ n := by positivity
      calc (∑ x ∈ L, w x) ≤ ((Nat.log 2 L.card + 1 : ℕ) : ℝ) ^ n * ∑ x ∈ T, w x := hmass
        _ ≤ ((Nat.log 2 L.card + 1 : ℕ) : ℝ) ^ n *
            (((Nat.log 2 L.card + 1 : ℕ) : ℝ) * ∑ x ∈ T', w x) :=
          mul_le_mul_of_nonneg_left hmass' hK
        _ = ((Nat.log 2 L.card + 1 : ℕ) : ℝ) ^ (n + 1) * ∑ x ∈ T', w x := by ring
    · intro k hk hkq x hx
      by_cases hkm : k = q - (n + 1)
      · subst hkm
        simp only [ite_true]
        obtain ⟨h1, h2⟩ := hg x hx
        exact ⟨h1, by rw [pow_succ] at h2; omega⟩
      · simp only [hkm, ite_false]
        have hd : desc G T' k (k + 1) x = desc G T k (k + 1) x := by
          unfold desc
          rw [hfilt k (by omega) (by omega) x hx]
        rw [hd]
        exact hB k (by omega) hkq x (hT'T hx)

/-- Two-sided bounds on descendant counts in a homogeneous set. -/
lemma desc_bounds (G : ℕ → α → ℕ) (q : ℕ) (T : Finset α) (hnest : Nested G q T) (B : ℕ → ℕ)
    (hB : ∀ k, k < q → ∀ x ∈ T, B k ≤ desc G T k (k + 1) x ∧ desc G T k (k + 1) x < 2 * B k)
    (a : ℕ) : ∀ b, a ≤ b → b ≤ q → ∀ x ∈ T,
      (∏ k ∈ Finset.Ico a b, B k) ≤ desc G T a b x ∧
        desc G T a b x ≤ 2 ^ (b - a) * ∏ k ∈ Finset.Ico a b, B k := by
  intro b
  induction b with
  | zero =>
    intro hab _ x hx
    have ha : a = 0 := by omega
    subst ha
    simp [desc_self G 0 hx]
  | succ b ih =>
    intro hab hbq x hx
    rcases Nat.eq_or_lt_of_le hab with hab' | hab'
    · subst hab'
      simp [desc_self G (b + 1) hx]
    have hab'' : a ≤ b := by omega
    obtain ⟨ih1, ih2⟩ := ih hab'' (by omega) x hx
    set U := T.filter (fun y => G a y = G a x) with hU
    have hUT : U ⊆ T := Finset.filter_subset _ _
    have hsplit := card_image_eq_sum_fiber G U b (b + 1)
      (fun y hy z hz h => hnest b (b + 1) (by omega) hbq y (hUT hy) z (hUT hz) h)
    -- each fibre of `U` over a level-`b` label is a full level-`b` fibre of `T`
    have hterm : ∀ c ∈ U.image (G b),
        B b ≤ ((U.filter (fun y => G b y = c)).image (G (b + 1))).card ∧
        ((U.filter (fun y => G b y = c)).image (G (b + 1))).card < 2 * B b := by
      intro c hc
      obtain ⟨z, hzU, rfl⟩ := Finset.mem_image.1 hc
      have hzT : z ∈ T := hUT hzU
      have hzx : G a z = G a x := (Finset.mem_filter.1 hzU).2
      have hfib : U.filter (fun y => G b y = G b z) = T.filter (fun y => G b y = G b z) := by
        ext y
        simp only [hU, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hy, _⟩, hyz⟩
          exact ⟨hy, hyz⟩
        · rintro ⟨hy, hyz⟩
          exact ⟨⟨hy, (hnest a b hab'' (by omega) y hy z hzT hyz).trans hzx⟩, hyz⟩
      rw [hfib]
      exact hB b (by omega) z hzT
    have hdesc : desc G T a (b + 1) x = (U.image (G (b + 1))).card := rfl
    have hdescb : desc G T a b x = (U.image (G b)).card := rfl
    rw [Finset.prod_Ico_succ_top hab'', hdesc, hsplit]
    constructor
    · calc (∏ k ∈ Finset.Ico a b, B k) * B b ≤ (U.image (G b)).card * B b := by
            rw [← hdescb]; exact Nat.mul_le_mul_right _ ih1
        _ = ∑ c ∈ U.image (G b), B b := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (fun c hc => (hterm c hc).1)
    · calc ∑ c ∈ U.image (G b), ((U.filter (fun y => G b y = c)).image (G (b + 1))).card
            ≤ ∑ c ∈ U.image (G b), 2 * B b :=
              Finset.sum_le_sum (fun c hc => (hterm c hc).2.le)
        _ = (U.image (G b)).card * (2 * B b) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (2 ^ (b - a) * ∏ k ∈ Finset.Ico a b, B k) * (2 * B b) := by
            rw [← hdescb]; exact Nat.mul_le_mul_right _ ih2
        _ = 2 ^ (b + 1 - a) * ((∏ k ∈ Finset.Ico a b, B k) * B b) := by
            rw [show b + 1 - a = (b - a) + 1 by omega, pow_succ]
            ring

/-- Splitting the level-`b` labels of `T` along the level-`a` labels. -/
lemma card_image_eq_sum_desc (G : ℕ → α → ℕ) (q : ℕ) (T : Finset α) (hnest : Nested G q T)
    {a b : ℕ} (hab : a ≤ b) (hbq : b ≤ q) :
    (T.image (G b)).card = ∑ c ∈ T.image (G a), ((T.filter (fun y => G a y = c)).image (G b)).card :=
  card_image_eq_sum_fiber G T a b (fun x hx y hy h => hnest a b hab hbq x hx y hy h)

lemma card_image_mono (G : ℕ → α → ℕ) (q : ℕ) (T : Finset α) (hnest : Nested G q T)
    {a b : ℕ} (hab : a ≤ b) (hbq : b ≤ q) :
    (T.image (G a)).card ≤ (T.image (G b)).card := by
  rw [card_image_eq_sum_desc G q T hnest hab hbq]
  calc (T.image (G a)).card = ∑ c ∈ T.image (G a), 1 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hc
      exact desc_pos G a b hz

/-- **Finite homogenization.** -/
theorem finite_homogenize (G : ℕ → α → ℕ) (q : ℕ) (L : Finset α) (w : α → ℝ)
    (hnest : Nested G q L) :
    ∃ T ⊆ L, (∑ x ∈ L, w x) ≤ ((Nat.log 2 L.card + 1 : ℕ) : ℝ) ^ q * ∑ x ∈ T, w x ∧
      (∀ a b, a ≤ b → b ≤ q → (T.image (G a)).card ≤ (T.image (G b)).card) ∧
      ∀ a b, a ≤ b → b ≤ q → ∀ x ∈ T,
        desc G T a b x * (T.image (G a)).card ≤ 2 ^ (b - a) * (T.image (G b)).card := by
  obtain ⟨T, hTL, hmass, B, hB⟩ := homogenize_aux G q L w hnest q le_rfl
  have hnT : Nested G q T := hnest.mono hTL
  have hB' : ∀ k, k < q → ∀ x ∈ T,
      B k ≤ desc G T k (k + 1) x ∧ desc G T k (k + 1) x < 2 * B k :=
    fun k hk => hB k (by omega) hk
  refine ⟨T, hTL, hmass, fun a b hab hbq => card_image_mono G q T hnT hab hbq, ?_⟩
  intro a b hab hbq x hx
  have hup := (desc_bounds G q T hnT B hB' a b hab hbq x hx).2
  have hlow : (T.image (G a)).card * ∏ k ∈ Finset.Ico a b, B k ≤ (T.image (G b)).card := by
    rw [card_image_eq_sum_desc G q T hnT hab hbq]
    calc (T.image (G a)).card * ∏ k ∈ Finset.Ico a b, B k
          = ∑ c ∈ T.image (G a), ∏ k ∈ Finset.Ico a b, B k := by
            rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro c hc
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hc
          exact (desc_bounds G q T hnT B hB' a b hab hbq z hz).1
  calc desc G T a b x * (T.image (G a)).card
        ≤ (2 ^ (b - a) * ∏ k ∈ Finset.Ico a b, B k) * (T.image (G a)).card :=
          Nat.mul_le_mul_right _ hup
    _ = 2 ^ (b - a) * ((T.image (G a)).card * ∏ k ∈ Finset.Ico a b, B k) := by ring
    _ ≤ 2 ^ (b - a) * (T.image (G b)).card := Nat.mul_le_mul_left _ hlow

end Submission.Obl.k4_matching_homogeneous_records
