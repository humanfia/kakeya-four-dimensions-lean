-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_whitney_rich_reduction.Whitney.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Whitney cube pairs for coefficient fans (x0284)

Combinatorial helpers for a Whitney reduction of the broad near-tangent rich bound.
The coefficient space `EuclideanSpace ℝ (Fin 3)` is cut into integer cubes of side
`D / 200`.  A Whitney pair at scale `D` is a pair of occupied cubes all of whose cross
coefficient distances lie in `[D, 2D]`.  We prove

* `card_partners_fst_le` / `card_partners_snd_le`: a cube has at most `801 ^ 3` Whitney
  partners;
* `sum_whitney_card_le`: the Whitney pairs carry at most `2 * 801 ^ 3 * #F` fan members;
* `exists_rich_whitney_pair`: a fan with more than `2 μ 801^3 #F` ordered pairs at
  distance in `[1.02 D, 1.98 D]` has a Whitney pair with `≥ μ` members on each side;
* `exists_dense_shell`: the scales `D_m = δ / 1.98 * (3/2)^m` pigeonhole the ordered
  off-diagonal pairs of a `δ`-separated fan.
-/

namespace WangZahlLot.Obl.wz_jet_whitney_rich_reduction

open Finset

noncomputable section

/-- Integer cube index of `x` at side `s`. -/
def cubeIdx (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℤ := fun m => ⌊x m / s⌋

lemma abs_coord_sub_lt_of_cubeIdx_eq {s : ℝ} (hs : 0 < s) {x y : EuclideanSpace ℝ (Fin 3)}
    (h : cubeIdx s x = cubeIdx s y) (m : Fin 3) : |x m - y m| < s := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun h m)
  rw [← sub_div, abs_div, abs_of_pos hs, div_lt_one hs] at h1
  exact h1

lemma dist_lt_of_cubeIdx_eq {s : ℝ} (hs : 0 < s) {x y : EuclideanSpace ℝ (Fin 3)}
    (h : cubeIdx s x = cubeIdx s y) : dist x y < 2 * s := by
  rw [EuclideanSpace.dist_eq]
  have hlt : ∀ i ∈ (univ : Finset (Fin 3)), dist (x i) (y i) ^ 2 < s ^ 2 := by
    intro i _
    rw [Real.dist_eq]
    have h1 := abs_coord_sub_lt_of_cubeIdx_eq hs h i
    have h2 := abs_nonneg (x i - y i)
    nlinarith
  have hsum : ∑ i, dist (x i) (y i) ^ 2 < ∑ _i : Fin 3, s ^ 2 :=
    Finset.sum_lt_sum_of_nonempty univ_nonempty hlt
  rw [Real.sqrt_lt' (by positivity)]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hsum
  have hs2 : 0 < s ^ 2 := by positivity
  nlinarith

lemma abs_coord_sub_le_dist (x y : EuclideanSpace ℝ (Fin 3)) (m : Fin 3) :
    |x m - y m| ≤ dist x y := by
  have := PiLp.dist_apply_le x y m
  rwa [Real.dist_eq] at this

/-- Cube indices of points at distance `≤ T s` differ by at most `T` in each coordinate. -/
lemma abs_cubeIdx_sub_le {s : ℝ} (hs : 0 < s) {x y : EuclideanSpace ℝ (Fin 3)} {T : ℤ}
    (h : dist x y ≤ T * s) (m : Fin 3) : |cubeIdx s x m - cubeIdx s y m| ≤ T := by
  have hxy : |x m / s - y m / s| ≤ T := by
    rw [← sub_div, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact (abs_coord_sub_le_dist x y m).trans h
  have a1 := Int.floor_le (x m / s)
  have a2 := Int.lt_floor_add_one (x m / s)
  have b1 := Int.floor_le (y m / s)
  have b2 := Int.lt_floor_add_one (y m / s)
  have hlt : |((cubeIdx s x m - cubeIdx s y m : ℤ) : ℝ)| < T + 1 := by
    simp only [cubeIdx]
    push_cast
    rw [abs_le] at hxy
    rw [abs_lt]
    constructor <;> linarith [hxy.1, hxy.2]
  have hlt' : |cubeIdx s x m - cubeIdx s y m| < T + 1 := by
    have : ((|cubeIdx s x m - cubeIdx s y m| : ℤ) : ℝ) < ((T + 1 : ℤ) : ℝ) := by
      push_cast
      rw [← Int.cast_abs] at hlt
      exact_mod_cast hlt
    exact_mod_cast this
  omega

variable {n : ℕ}

/-- Indices whose coefficient lies in cube `k` at side `s`. -/
def cubeSet (q : Fin n → EuclideanSpace ℝ (Fin 3)) (s : ℝ) (k : Fin 3 → ℤ) :
    Finset (Fin n) :=
  univ.filter (fun i => cubeIdx s (q i) = k)

/-- Occupied cubes at side `s`. -/
def occCubes (q : Fin n → EuclideanSpace ℝ (Fin 3)) (s : ℝ) : Finset (Fin 3 → ℤ) :=
  univ.image (fun i => cubeIdx s (q i))

open Classical in
/-- Whitney pairs at scale `D`: occupied cube pairs (side `D / 200`) all of whose cross
coefficient distances lie in `[D, 2D]`. -/
def whitneyPairs (q : Fin n → EuclideanSpace ℝ (Fin 3)) (D : ℝ) :
    Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
  (occCubes q (D / 200) ×ˢ occCubes q (D / 200)).filter (fun kk =>
    ∀ i ∈ cubeSet q (D / 200) kk.1, ∀ j ∈ cubeSet q (D / 200) kk.2,
      D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2 * D)

lemma mem_cubeSet {q : Fin n → EuclideanSpace ℝ (Fin 3)} {s : ℝ} {k : Fin 3 → ℤ} {i : Fin n} :
    i ∈ cubeSet q s k ↔ cubeIdx s (q i) = k := by
  simp [cubeSet]

lemma mem_whitneyPairs {q : Fin n → EuclideanSpace ℝ (Fin 3)} {D : ℝ}
    {kk : (Fin 3 → ℤ) × (Fin 3 → ℤ)} :
    kk ∈ whitneyPairs q D ↔ (kk.1 ∈ occCubes q (D / 200) ∧ kk.2 ∈ occCubes q (D / 200)) ∧
      ∀ i ∈ cubeSet q (D / 200) kk.1, ∀ j ∈ cubeSet q (D / 200) kk.2,
        D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2 * D := by
  classical
  unfold whitneyPairs
  rw [Finset.mem_filter, Finset.mem_product]

/-- Partners of a cube lie in an integer box of radius `400`. -/
lemma partner_mem_box {q : Fin n → EuclideanSpace ℝ (Fin 3)} {D : ℝ} (hD : 0 < D)
    {kk : (Fin 3 → ℤ) × (Fin 3 → ℤ)} (h : kk ∈ whitneyPairs q D) (m : Fin 3) :
    |kk.1 m - kk.2 m| ≤ 400 := by
  rw [mem_whitneyPairs] at h
  obtain ⟨⟨h1, h2⟩, hw⟩ := h
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h1
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h2
  have hij := (hw i (mem_cubeSet.mpr hi) j (mem_cubeSet.mpr hj)).2
  have hs : (0 : ℝ) < D / 200 := by positivity
  have hle : dist (q i) (q j) ≤ ((400 : ℤ) : ℝ) * (D / 200) := by
    push_cast; linarith
  have := abs_cubeIdx_sub_le hs hle m
  rwa [hi, hj] at this

lemma card_box (k : Fin 3 → ℤ) :
    (Fintype.piFinset (fun m => Icc (k m - 400) (k m + 400))).card = 801 ^ 3 := by
  rw [Fintype.card_piFinset]
  have h : ∀ m, (Icc (k m - 400) (k m + 400)).card = 801 := by
    intro m
    rw [Int.card_Icc]
    omega
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A cube has at most `801 ^ 3` Whitney partners (as first coordinate). -/
lemma card_partners_fst_le (q : Fin n → EuclideanSpace ℝ (Fin 3)) {D : ℝ} (hD : 0 < D)
    (k : Fin 3 → ℤ) : ((whitneyPairs q D).filter (fun kk => kk.1 = k)).card ≤ 801 ^ 3 := by
  rw [← card_box k]
  apply Finset.card_le_card_of_injOn (fun kk => kk.2)
  · intro kk hkk
    rw [Finset.mem_coe, Finset.mem_filter] at hkk
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro m
    have := partner_mem_box hD hkk.1 m
    rw [hkk.2] at this
    rw [Finset.mem_Icc]
    constructor <;> [linarith [(abs_le.mp this).2]; linarith [(abs_le.mp this).1]]
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    exact Prod.ext (ha.2.trans hb.2.symm) hab

/-- A cube has at most `801 ^ 3` Whitney partners (as second coordinate). -/
lemma card_partners_snd_le (q : Fin n → EuclideanSpace ℝ (Fin 3)) {D : ℝ} (hD : 0 < D)
    (k : Fin 3 → ℤ) : ((whitneyPairs q D).filter (fun kk => kk.2 = k)).card ≤ 801 ^ 3 := by
  rw [← card_box k]
  apply Finset.card_le_card_of_injOn (fun kk => kk.1)
  · intro kk hkk
    rw [Finset.mem_coe, Finset.mem_filter] at hkk
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro m
    have := partner_mem_box hD hkk.1 m
    rw [hkk.2] at this
    rw [Finset.mem_Icc]
    constructor <;> [linarith [(abs_le.mp this).1]; linarith [(abs_le.mp this).2]]
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    exact Prod.ext hab (ha.2.trans hb.2.symm)

/-- The cube counts of a finite set sum to its cardinality. -/
lemma sum_card_inter_cubeSet (q : Fin n → EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (F : Finset (Fin n)) :
    ∑ k ∈ occCubes q s, (F ∩ cubeSet q s k).card = F.card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun i => cubeIdx s (q i)) (t := occCubes q s)]
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    ext i
    simp [cubeSet, Finset.mem_filter]
  · intro i _
    simp [occCubes]

/-- Weighted partner count along the first coordinate. -/
lemma sum_whitney_fst_le (q : Fin n → EuclideanSpace ℝ (Fin 3)) {D : ℝ} (hD : 0 < D)
    (w : (Fin 3 → ℤ) → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ∑ kk ∈ whitneyPairs q D, w kk.1 ≤ 801 ^ 3 * ∑ k ∈ occCubes q (D / 200), w k := by
  classical
  have hmaps : ∀ kk ∈ whitneyPairs q D, kk.1 ∈ occCubes q (D / 200) := by
    intro kk hkk
    exact ((mem_whitneyPairs.mp hkk).1).1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  calc ∑ kk ∈ (whitneyPairs q D).filter (fun kk => kk.1 = k), w kk.1
      = ∑ kk ∈ (whitneyPairs q D).filter (fun kk => kk.1 = k), w k := by
        apply Finset.sum_congr rfl
        intro kk hkk
        rw [(Finset.mem_filter.mp hkk).2]
    _ = ((whitneyPairs q D).filter (fun kk => kk.1 = k)).card * w k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 801 ^ 3 * w k := by
        apply mul_le_mul_of_nonneg_right _ (hw k)
        exact_mod_cast card_partners_fst_le q hD k

/-- Weighted partner count along the second coordinate. -/
lemma sum_whitney_snd_le (q : Fin n → EuclideanSpace ℝ (Fin 3)) {D : ℝ} (hD : 0 < D)
    (w : (Fin 3 → ℤ) → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ∑ kk ∈ whitneyPairs q D, w kk.2 ≤ 801 ^ 3 * ∑ k ∈ occCubes q (D / 200), w k := by
  classical
  have hmaps : ∀ kk ∈ whitneyPairs q D, kk.2 ∈ occCubes q (D / 200) := by
    intro kk hkk
    exact ((mem_whitneyPairs.mp hkk).1).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  calc ∑ kk ∈ (whitneyPairs q D).filter (fun kk => kk.2 = k), w kk.2
      = ∑ kk ∈ (whitneyPairs q D).filter (fun kk => kk.2 = k), w k := by
        apply Finset.sum_congr rfl
        intro kk hkk
        rw [(Finset.mem_filter.mp hkk).2]
    _ = ((whitneyPairs q D).filter (fun kk => kk.2 = k)).card * w k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 801 ^ 3 * w k := by
        apply mul_le_mul_of_nonneg_right _ (hw k)
        exact_mod_cast card_partners_snd_le q hD k

/-- The Whitney pairs at one scale carry at most `2 * 801 ^ 3 * #F` members of `F`. -/
theorem sum_whitney_card_le (q : Fin n → EuclideanSpace ℝ (Fin 3)) {D : ℝ} (hD : 0 < D)
    (F : Finset (Fin n)) :
    ∑ kk ∈ whitneyPairs q D, (((F ∩ cubeSet q (D / 200) kk.1).card : ℝ) +
      (F ∩ cubeSet q (D / 200) kk.2).card) ≤ 2 * 801 ^ 3 * F.card := by
  rw [Finset.sum_add_distrib]
  have h1 := sum_whitney_fst_le q hD (fun k => ((F ∩ cubeSet q (D / 200) k).card : ℝ))
    (fun k => Nat.cast_nonneg _)
  have h2 := sum_whitney_snd_le q hD (fun k => ((F ∩ cubeSet q (D / 200) k).card : ℝ))
    (fun k => Nat.cast_nonneg _)
  have h3 : ∑ k ∈ occCubes q (D / 200), ((F ∩ cubeSet q (D / 200) k).card : ℝ) = F.card := by
    exact_mod_cast sum_card_inter_cubeSet q (D / 200) F
  rw [h3] at h1 h2
  linarith

/-- A pair at distance in `[1.02 D, 1.98 D]` lies in a Whitney pair at scale `D`. -/
lemma cube_pair_mem_whitneyPairs {q : Fin n → EuclideanSpace ℝ (Fin 3)} {D : ℝ} (hD : 0 < D)
    {i j : Fin n} (h1 : 1.02 * D ≤ dist (q i) (q j)) (h2 : dist (q i) (q j) ≤ 1.98 * D) :
    (cubeIdx (D / 200) (q i), cubeIdx (D / 200) (q j)) ∈ whitneyPairs q D := by
  have hs : (0 : ℝ) < D / 200 := by positivity
  rw [mem_whitneyPairs]
  refine ⟨⟨Finset.mem_image.mpr ⟨i, mem_univ _, rfl⟩,
    Finset.mem_image.mpr ⟨j, mem_univ _, rfl⟩⟩, ?_⟩
  intro i' hi' j' hj'
  rw [mem_cubeSet] at hi' hj'
  have a := dist_lt_of_cubeIdx_eq hs hi'
  have b := dist_lt_of_cubeIdx_eq hs hj'
  have e1 := dist_triangle4 (q i) (q i') (q j') (q j)
  have e2 := dist_triangle4 (q i') (q i) (q j) (q j')
  have c1 := dist_comm (q i) (q i')
  have c2 := dist_comm (q j) (q j')
  constructor <;> linarith

/-- Extraction: a fan with many pairs at distance about `D` has a Whitney pair at scale `D`
with at least `μ` members on each side. -/
theorem exists_rich_whitney_pair (q : Fin n → EuclideanSpace ℝ (Fin 3)) {D μ : ℝ} (hD : 0 < D)
    (hμ : 0 ≤ μ) (F : Finset (Fin n))
    (h : 2 * μ * 801 ^ 3 * F.card < (((F ×ˢ F).filter (fun ij =>
      1.02 * D ≤ dist (q ij.1) (q ij.2) ∧ dist (q ij.1) (q ij.2) ≤ 1.98 * D)).card : ℝ)) :
    ∃ kk ∈ whitneyPairs q D, μ ≤ ((F ∩ cubeSet q (D / 200) kk.1).card : ℝ) ∧
      μ ≤ ((F ∩ cubeSet q (D / 200) kk.2).card : ℝ) := by
  classical
  by_contra hcon
  push Not at hcon
  set s := D / 200 with hs_def
  set P := (F ×ˢ F).filter (fun ij =>
      1.02 * D ≤ dist (q ij.1) (q ij.2) ∧ dist (q ij.1) (q ij.2) ≤ 1.98 * D) with hP
  let f : (Fin 3 → ℤ) → ℝ := fun k => ((F ∩ cubeSet q s k).card : ℝ)
  have hmaps : ∀ ij ∈ P, (cubeIdx s (q ij.1), cubeIdx s (q ij.2)) ∈ whitneyPairs q D := by
    intro ij hij
    have := (Finset.mem_filter.mp hij).2
    exact cube_pair_mem_whitneyPairs hD this.1 this.2
  have hcard : (P.card : ℝ) ≤ ∑ kk ∈ whitneyPairs q D, f kk.1 * f kk.2 := by
    rw [card_eq_sum_card_fiberwise hmaps]
    push_cast
    apply Finset.sum_le_sum
    intro kk _
    have hsub : P.filter (fun ij => (cubeIdx s (q ij.1), cubeIdx s (q ij.2)) = kk) ⊆
        (F ∩ cubeSet q s kk.1) ×ˢ (F ∩ cubeSet q s kk.2) := by
      intro ij hij
      rw [Finset.mem_filter] at hij
      obtain ⟨hijP, hkk⟩ := hij
      have hF := (Finset.mem_filter.mp hijP).1
      rw [Finset.mem_product] at hF ⊢
      rw [← hkk]
      exact ⟨Finset.mem_inter.mpr ⟨hF.1, mem_cubeSet.mpr rfl⟩,
        Finset.mem_inter.mpr ⟨hF.2, mem_cubeSet.mpr rfl⟩⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_product] at this
    show _ ≤ ((F ∩ cubeSet q s kk.1).card : ℝ) * ((F ∩ cubeSet q s kk.2).card : ℝ)
    exact_mod_cast this
  have hbound : ∀ kk ∈ whitneyPairs q D, f kk.1 * f kk.2 ≤ μ * (f kk.1 + f kk.2) := by
    intro kk hkk
    have h0a : 0 ≤ f kk.1 := Nat.cast_nonneg _
    have h0b : 0 ≤ f kk.2 := Nat.cast_nonneg _
    by_cases ha : μ ≤ f kk.1
    · have hb := hcon kk hkk ha
      nlinarith
    · push Not at ha
      nlinarith
  have hsum := sum_whitney_card_le q hD F
  have : (P.card : ℝ) ≤ μ * (2 * 801 ^ 3 * F.card) := by
    calc (P.card : ℝ) ≤ ∑ kk ∈ whitneyPairs q D, f kk.1 * f kk.2 := hcard
      _ ≤ ∑ kk ∈ whitneyPairs q D, μ * (f kk.1 + f kk.2) := Finset.sum_le_sum hbound
      _ = μ * ∑ kk ∈ whitneyPairs q D, (f kk.1 + f kk.2) := by rw [Finset.mul_sum]
      _ ≤ μ * (2 * 801 ^ 3 * F.card) := mul_le_mul_of_nonneg_left hsum hμ
  linarith

/-- The Whitney scales. -/
def whitneyScale (δ : ℝ) (m : ℕ) : ℝ := δ / 1.98 * (3 / 2) ^ m

lemma whitneyScale_pos {δ : ℝ} (hδ : 0 < δ) (m : ℕ) : 0 < whitneyScale δ m := by
  unfold whitneyScale; positivity

/-- Every distance in `[δ, δ (3/2)^(L-1))` lies in the window `[1.02 D_m, 1.98 D_m]` of some
scale `m < L`. -/
lemma exists_window {δ d : ℝ} (hδ : 0 < δ) (hd : δ ≤ d) {L : ℕ}
    (hL : d < δ * (3 / 2) ^ (L - 1)) :
    ∃ m < L, 1.02 * whitneyScale δ m ≤ d ∧ d ≤ 1.98 * whitneyScale δ m := by
  have hx : (1 : ℝ) ≤ d / δ := by rw [le_div_iff₀ hδ]; linarith
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 3 / 2)
  have hkL : k + 1 < L := by
    by_contra hcon
    push Not at hcon
    have h1 : (3 / 2 : ℝ) ^ (L - 1) ≤ (3 / 2) ^ k :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : d / δ < (3 / 2) ^ (L - 1) := by rw [div_lt_iff₀ hδ]; linarith
    linarith
  refine ⟨k + 1, hkL, ?_, ?_⟩
  · unfold whitneyScale
    have hkd : (3 / 2 : ℝ) ^ k * δ ≤ d := by rwa [le_div_iff₀ hδ] at hk1
    have ht : 0 ≤ (3 / 2 : ℝ) ^ k * δ := by positivity
    calc 1.02 * (δ / 1.98 * (3 / 2 : ℝ) ^ (k + 1)) = (153 / 198) * ((3 / 2 : ℝ) ^ k * δ) := by
          rw [pow_succ]; ring
      _ ≤ 1 * ((3 / 2 : ℝ) ^ k * δ) := by
          apply mul_le_mul_of_nonneg_right _ ht; norm_num
      _ ≤ d := by linarith
  · unfold whitneyScale
    have hkd : d < (3 / 2 : ℝ) ^ (k + 1) * δ := by rwa [div_lt_iff₀ hδ] at hk2
    have : 1.98 * (δ / 1.98 * (3 / 2 : ℝ) ^ (k + 1)) = (3 / 2 : ℝ) ^ (k + 1) * δ := by ring
    linarith

/-- Pigeonhole over the scales: a `δ`-separated fan with all distances below
`δ (3/2)^(L-1)` has a scale `m < L` holding at least `(#F^2 - #F) / L` ordered pairs in its
window. -/
theorem exists_dense_shell (q : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hδ : 0 < δ)
    (F : Finset (Fin n)) (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → δ ≤ dist (q i) (q j))
    {L : ℕ} (hLpos : 0 < L) (hL : ∀ i ∈ F, ∀ j ∈ F, dist (q i) (q j) < δ * (3 / 2) ^ (L - 1)) :
    ∃ m < L, ((F.card : ℝ) ^ 2 - F.card) / L ≤
      (((F ×ˢ F).filter (fun ij => 1.02 * whitneyScale δ m ≤ dist (q ij.1) (q ij.2) ∧
        dist (q ij.1) (q ij.2) ≤ 1.98 * whitneyScale δ m)).card : ℝ) := by
  classical
  set W : ℕ → Finset (Fin n × Fin n) := fun m => (F ×ˢ F).filter (fun ij =>
    1.02 * whitneyScale δ m ≤ dist (q ij.1) (q ij.2) ∧
      dist (q ij.1) (q ij.2) ≤ 1.98 * whitneyScale δ m) with hW
  have hsub : F.offDiag ⊆ (range L).biUnion W := by
    intro ij hij
    rw [Finset.mem_offDiag] at hij
    obtain ⟨hi, hj, hne⟩ := hij
    obtain ⟨m, hm, h1, h2⟩ := exists_window hδ (hsep _ hi _ hj hne) (hL _ hi _ hj)
    rw [Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.mpr hm,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, h1, h2⟩⟩
  have hoff : ((F.offDiag.card : ℕ) : ℝ) = (F.card : ℝ) ^ 2 - F.card := by
    rw [Finset.offDiag_card]
    rw [Nat.cast_sub (Nat.le_mul_self _)]
    push_cast; ring
  have hle : (F.card : ℝ) ^ 2 - F.card ≤ ∑ m ∈ range L, ((W m).card : ℝ) := by
    rw [← hoff]
    have := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    exact_mod_cast this
  have hne : (range L).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  have hconst : ∑ _m ∈ range L, ((F.card : ℝ) ^ 2 - F.card) / L =
      (F.card : ℝ) ^ 2 - F.card := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  obtain ⟨m, hm, hmle⟩ := Finset.exists_le_of_sum_le
    (f := fun _ => ((F.card : ℝ) ^ 2 - F.card) / L) (g := fun m => ((W m).card : ℝ)) hne
    (by rw [hconst]; exact hle)
  exact ⟨m, Finset.mem_range.mp hm, hmle⟩

end

end WangZahlLot.Obl.wz_jet_whitney_rich_reduction
