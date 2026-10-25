import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.Statement
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.SlicedCells

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# Chart tools for the first jet

* `lipEnv`: the Lipschitz envelope `v ↦ inf_a (f a + L|v - g a|)` (McShane extension), its
  Lipschitz bound and its closeness to slack-Lipschitz data;
* `slab_cap`: the absolute cap summed over the cubes of a slanted slab
  (paper: "covered by `K H^{-j}` cubes of side `Hp`");
* `JetData.swap`, `JetHyp.swap`: the hypotheses are symmetric in the two tangential
  coordinates, so each row component can be fitted by the same construction.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

/-- The Lipschitz envelope `v ↦ inf_{a ∈ s} (f a + L |v - g a|)` of a family of values `f a` at
positions `g a`. -/
def lipEnv {ι : Type*} (s : Set ι) (f g : ι → ℝ) (L v : ℝ) : ℝ :=
  ⨅ a : s, (f a + L * |v - g a|)

theorem lipEnv_bddBelow {ι : Type*} {s : Set ι} {f g : ι → ℝ} {L M : ℝ} (hL : 0 ≤ L)
    (hf : ∀ a ∈ s, -M ≤ f a) (v : ℝ) :
    BddBelow (range fun a : s => f a + L * |v - g a|) := by
  refine ⟨-M, ?_⟩
  rintro _ ⟨a, rfl⟩
  have := hf a a.2
  have : 0 ≤ L * |v - g a| := mul_nonneg hL (abs_nonneg _)
  linarith

theorem lipEnv_le {ι : Type*} {s : Set ι} {f g : ι → ℝ} {L M : ℝ} (hL : 0 ≤ L)
    (hf : ∀ a ∈ s, -M ≤ f a) (v : ℝ) {a : ι} (ha : a ∈ s) :
    lipEnv s f g L v ≤ f a + L * |v - g a| :=
  ciInf_le (lipEnv_bddBelow hL hf v) ⟨a, ha⟩

/-- The envelope is `L`-Lipschitz. -/
theorem lipEnv_lip {ι : Type*} {s : Set ι} (hs : s.Nonempty) {f g : ι → ℝ} {L M : ℝ}
    (hL : 0 ≤ L) (hf : ∀ a ∈ s, -M ≤ f a) (v v' : ℝ) :
    |lipEnv s f g L v - lipEnv s f g L v'| ≤ L * |v - v'| := by
  have : Nonempty s := hs.to_subtype
  have key : ∀ x y : ℝ, lipEnv s f g L x ≤ lipEnv s f g L y + L * |x - y| := by
    intro x y
    have : lipEnv s f g L x - L * |x - y| ≤ lipEnv s f g L y := by
      apply le_ciInf
      intro a
      have h1 := lipEnv_le (g := g) hL hf x a.2
      have h2 : |x - g a| ≤ |x - y| + |y - g a| := abs_sub_le x y (g a)
      have h3 : L * |x - g a| ≤ L * |x - y| + L * |y - g a| := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left h2 hL
      linarith
    linarith
  rw [abs_le]
  constructor
  · have := key v' v; rw [abs_sub_comm] at this; linarith
  · have := key v v'; linarith

/-- On the family itself the envelope is within the slack of the values, when the values are
`L`-Lipschitz with slack `e` in the positions. -/
theorem lipEnv_near {ι : Type*} {s : Set ι} {f g : ι → ℝ} {L M e : ℝ} (hL : 0 ≤ L)
    (hf : ∀ a ∈ s, -M ≤ f a) (hslack : ∀ a ∈ s, ∀ b ∈ s, f a ≤ f b + L * (|g a - g b| + e))
    {a : ι} (ha : a ∈ s) : |lipEnv s f g L (g a) - f a| ≤ L * e := by
  have : Nonempty s := ⟨⟨a, ha⟩⟩
  have hup : lipEnv s f g L (g a) ≤ f a := by
    have := lipEnv_le (g := g) hL hf (g a) ha
    simpa using this
  have hlow : f a - L * e ≤ lipEnv s f g L (g a) := by
    apply le_ciInf
    intro b
    have := hslack a ha b b.2
    have : L * (|g a - g b| + e) = L * |g a - g ↑b| + L * e := by ring
    linarith
  rw [abs_le]; constructor <;> linarith


variable {Ω : Type*} [MeasurableSpace Ω]

/-- Integer windows: if `a ≤ x ≤ a + n q` then `⌊x/q⌋ ∈ [⌊a/q⌋, ⌊a/q⌋ + n]`. -/
theorem floor_window {a x q : ℝ} {n : ℕ} (hq : 0 < q) (h1 : a ≤ x) (h2 : x ≤ a + n * q) :
    ⌊x / q⌋ ∈ Finset.Icc ⌊a / q⌋ (⌊a / q⌋ + n) := by
  rw [Finset.mem_Icc]
  constructor
  · exact Int.floor_le_floor (div_le_div_of_nonneg_right h1 hq.le)
  · have : x / q ≤ a / q + n := by
      rw [div_add' _ _ _ hq.ne', div_le_div_iff_of_pos_right hq]; linarith
    calc ⌊x / q⌋ ≤ ⌊a / q + n⌋ := Int.floor_le_floor this
      _ = ⌊a / q⌋ + n := by exact_mod_cast Int.floor_add_natCast (a / q) n

/-- **Slab cap**: lines labeled at `t` whose tangential coordinates lie in windows of `n₀, n₁`
cubes and whose normal scalar lies in a window of `n₂` cubes of side `q` have mass at most
`(n₀+1)(n₁+1)(n₂+2M+1) K q^(2+d)`, `M = ⌈2K⌉`. -/
theorem slab_cap {D : JetData Ω} {ζ K d : ℝ} (hD : JetHyp D ζ K d) (hK : 0 ≤ K) {t q : ℝ}
    (hq : 0 < q) (hζq : ζ ≤ q) (hq1 : q ≤ 1) (a₀ a₁ s₀ : ℝ) (n₀ n₁ n₂ : ℕ) (X : Set Ω)
    (hX : ∀ l ∈ X, (l, t) ∈ D.E ∧ a₀ ≤ D.y l 0 ∧ D.y l 0 ≤ a₀ + n₀ * q ∧ a₁ ≤ D.y l 1 ∧
      D.y l 1 ≤ a₁ + n₁ * q ∧ s₀ ≤ D.S l t ∧ D.S l t ≤ s₀ + n₂ * q) :
    D.ν X ≤ ((n₀ + 1) * (n₁ + 1) * (n₂ + 2 * ⌈2 * K⌉₊ + 1) : ℕ) *
      ENNReal.ofReal (K * q ^ (2 + d)) := by
  classical
  set M : ℕ := ⌈2 * K⌉₊ with hM
  have hMK : 2 * K ≤ (M : ℝ) := Nat.le_ceil _
  set W₀ : Finset ℤ := Finset.Icc ⌊a₀ / q⌋ (⌊a₀ / q⌋ + n₀)
  set W₁ : Finset ℤ := Finset.Icc ⌊a₁ / q⌋ (⌊a₁ / q⌋ + n₁)
  set base : ℤ × ℤ → ℤ := fun m => ⌊(s₀ + (D.F t 0 * ((m.1 : ℝ) * q) + D.F t 1 * ((m.2 : ℝ) * q))
    - M * q) / q⌋
  set Cubes : Finset (Fin 3 → ℤ) := (W₀ ×ˢ W₁).biUnion (fun m =>
    (Finset.Icc (base m) (base m + (n₂ + 2 * M))).image (fun m₀ => ![m₀, m.1, m.2]))
  have hsub : X ⊆ ⋃ m ∈ Cubes, {l | (l, t) ∈ D.E ∧ D.cube q l t = m} := by
    intro l hl
    obtain ⟨hlE, h0, h0', h1, h1', hs, hs'⟩ := hX l hl
    set m₁ := ⌊D.y l 0 / q⌋
    set m₂ := ⌊D.y l 1 / q⌋
    have hm₁ : m₁ ∈ W₀ := floor_window hq h0 h0'
    have hm₂ : m₂ ∈ W₁ := floor_window hq h1 h1'
    -- the spatial scalar near the corner
    have e0 : |D.y l 0 - (m₁ : ℝ) * q| ≤ q := by
      have a := Int.floor_le (D.y l 0 / q); have b := Int.lt_floor_add_one (D.y l 0 / q)
      rw [le_div_iff₀ hq] at a; rw [div_lt_iff₀ hq] at b
      rw [abs_le]; constructor <;> nlinarith
    have e1 : |D.y l 1 - (m₂ : ℝ) * q| ≤ q := by
      have a := Int.floor_le (D.y l 1 / q); have b := Int.lt_floor_add_one (D.y l 1 / q)
      rw [le_div_iff₀ hq] at a; rw [div_lt_iff₀ hq] at b
      rw [abs_le]; constructor <;> nlinarith
    have hF0 := hD.bound_F t 0
    have hF1 := hD.bound_F t 1
    have hcorner : |(D.F t 0 * D.y l 0 + D.F t 1 * D.y l 1) -
        (D.F t 0 * ((m₁ : ℝ) * q) + D.F t 1 * ((m₂ : ℝ) * q))| ≤ 2 * K * q := by
      have : (D.F t 0 * D.y l 0 + D.F t 1 * D.y l 1) -
          (D.F t 0 * ((m₁ : ℝ) * q) + D.F t 1 * ((m₂ : ℝ) * q)) =
          D.F t 0 * (D.y l 0 - (m₁ : ℝ) * q) + D.F t 1 * (D.y l 1 - (m₂ : ℝ) * q) := by ring
      rw [this]
      calc _ ≤ |D.F t 0 * (D.y l 0 - (m₁ : ℝ) * q)| + |D.F t 1 * (D.y l 1 - (m₂ : ℝ) * q)| :=
            abs_add_le _ _
        _ ≤ K * q + K * q := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul hF0 e0 (abs_nonneg _) hK)
              (mul_le_mul hF1 e1 (abs_nonneg _) hK)
        _ = 2 * K * q := by ring
    have hxb : D.xb l t = D.S l t + (D.F t 0 * D.y l 0 + D.F t 1 * D.y l 1) := by
      simp only [JetData.S, JetData.Fy]; ring
    have hMq : 2 * K * q ≤ (M : ℝ) * q := mul_le_mul_of_nonneg_right hMK hq.le
    have hwin : ⌊D.xb l t / q⌋ ∈ Finset.Icc (base (m₁, m₂)) (base (m₁, m₂) + (n₂ + 2 * M)) := by
      have := floor_window (a := s₀ + (D.F t 0 * ((m₁ : ℝ) * q) + D.F t 1 * ((m₂ : ℝ) * q)) - M * q)
        (x := D.xb l t) (n := n₂ + 2 * M) hq (by rw [hxb]; linarith [(abs_le.1 hcorner).1])
        (by rw [hxb]; push_cast; linarith [(abs_le.1 hcorner).2])
      exact this
    refine mem_iUnion₂.2 ⟨D.cube q l t, Finset.mem_biUnion.2 ⟨(m₁, m₂),
      Finset.mem_product.2 ⟨hm₁, hm₂⟩, Finset.mem_image.2 ⟨_, hwin, ?_⟩⟩, hlE, rfl⟩
    simp [JetData.cube, m₁, m₂]
  have hcard : Cubes.card ≤ (n₀ + 1) * (n₁ + 1) * (n₂ + 2 * M + 1) := by
    calc Cubes.card ≤ ∑ m ∈ W₀ ×ˢ W₁, ((Finset.Icc (base m) (base m + (n₂ + 2 * M))).image
          (fun m₀ => ![m₀, m.1, m.2])).card := Finset.card_biUnion_le
      _ ≤ ∑ _m ∈ W₀ ×ˢ W₁, (n₂ + 2 * M + 1) := by
          apply Finset.sum_le_sum
          intro m _
          refine (Finset.card_image_le).trans ?_
          rw [Int.card_Icc]
          omega
      _ = (W₀ ×ˢ W₁).card * (n₂ + 2 * M + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ = (n₀ + 1) * (n₁ + 1) * (n₂ + 2 * M + 1) := by
          have e0 : (⌊a₀ / q⌋ + n₀ + 1 - ⌊a₀ / q⌋).toNat = n₀ + 1 := by omega
          have e1 : (⌊a₁ / q⌋ + n₁ + 1 - ⌊a₁ / q⌋).toNat = n₁ + 1 := by omega
          rw [Finset.card_product, Int.card_Icc, Int.card_Icc, e0, e1]
  calc D.ν X ≤ ∑ m ∈ Cubes, D.ν {l | (l, t) ∈ D.E ∧ D.cube q l t = m} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _m ∈ Cubes, ENNReal.ofReal (K * q ^ (2 + d)) :=
        Finset.sum_le_sum (fun m _ => hD.abscap t q hζq hq1 m)
    _ = Cubes.card * ENNReal.ofReal (K * q ^ (2 + d)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr



/-- Swap the two tangential coordinates (and the two row components). -/
def swap2 (a : Fin 2 → ℝ) : Fin 2 → ℝ := ![a 1, a 0]

@[simp] theorem swap2_zero (a : Fin 2 → ℝ) : swap2 a 0 = a 1 := by simp [swap2]
@[simp] theorem swap2_one (a : Fin 2 → ℝ) : swap2 a 1 = a 0 := by simp [swap2]

namespace JetData

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The chart with the tangential coordinates swapped. -/
def swap (D : JetData Ω) : JetData Ω where
  ν := D.ν
  E := D.E
  x0 := D.x0
  x1 := D.x1
  y := fun l => swap2 (D.y l)
  F := fun t => swap2 (D.F t)

@[simp] theorem swap_ν (D : JetData Ω) : D.swap.ν = D.ν := rfl
@[simp] theorem swap_E (D : JetData Ω) : D.swap.E = D.E := rfl
@[simp] theorem swap_x0 (D : JetData Ω) : D.swap.x0 = D.x0 := rfl
@[simp] theorem swap_x1 (D : JetData Ω) : D.swap.x1 = D.x1 := rfl
@[simp] theorem swap_y (D : JetData Ω) (l : Ω) : D.swap.y l = swap2 (D.y l) := rfl
@[simp] theorem swap_F (D : JetData Ω) (t : ℝ) : D.swap.F t = swap2 (D.F t) := rfl
@[simp] theorem swap_xb (D : JetData Ω) (l : Ω) (t : ℝ) : D.swap.xb l t = D.xb l t := rfl

@[simp] theorem swap_Fy (D : JetData Ω) (t : ℝ) (l : Ω) : D.swap.Fy t l = D.Fy t l := by
  simp only [Fy, swap_F, swap_y, swap2_zero, swap2_one]; ring

@[simp] theorem swap_S (D : JetData Ω) (l : Ω) (t : ℝ) : D.swap.S l t = D.S l t := by
  simp only [S, swap_xb, swap_Fy]

@[simp] theorem swap_cube (D : JetData Ω) (q : ℝ) (l : Ω) (t : ℝ) :
    D.swap.cube q l t = ![D.cube q l t 0, D.cube q l t 2, D.cube q l t 1] := by
  ext k; fin_cases k <;> simp [cube]

@[simp] theorem swap_coeffBin (D : JetData Ω) (r : ℝ) (l : Ω) :
    D.swap.coeffBin r l = ![D.coeffBin r l 0, D.coeffBin r l 1, D.coeffBin r l 3,
      D.coeffBin r l 2] := by
  ext k; fin_cases k <;> simp [coeffBin]

end JetData

theorem perm3_eq {m m' : Fin 3 → ℤ} :
    (![m' 0, m' 2, m' 1] = m) ↔ (m' = ![m 0, m 2, m 1]) := by
  constructor
  · intro h; subst h; ext k; fin_cases k <;> simp
  · intro h; subst h; ext k; fin_cases k <;> simp

theorem perm4_eq {m m' : Fin 4 → ℤ} :
    (![m' 0, m' 1, m' 3, m' 2] = m) ↔ (m' = ![m 0, m 1, m 3, m 2]) := by
  constructor
  · intro h; subst h; ext k; fin_cases k <;> simp
  · intro h; subst h; ext k; fin_cases k <;> simp

theorem JetHyp.swap {Ω : Type*} [MeasurableSpace Ω] {D : JetData Ω} {ζ K d : ℝ}
    (hD : JetHyp D ζ K d) : JetHyp D.swap ζ K d where
  prob := hD.prob
  measE := hD.measE
  E01 := hD.E01
  meas_x0 := hD.meas_x0
  meas_x1 := hD.meas_x1
  meas_y := fun i => by
    fin_cases i
    · simpa using hD.meas_y 1
    · simpa using hD.meas_y 0
  meas_F := fun i => by
    fin_cases i
    · simpa using hD.meas_F 1
    · simpa using hD.meas_F 0
  bound_x := hD.bound_x
  bound_y := fun l i => by
    fin_cases i
    · simpa using hD.bound_y l 1
    · simpa using hD.bound_y l 0
  bound_F := fun t i => by
    fin_cases i
    · simpa using hD.bound_F t 1
    · simpa using hD.bound_F t 0
  supp := fun t => by
    simpa only [JetData.swap_E, JetData.swap_S] using hD.supp t
  abscap := fun t q hζq hq1 m => by
    have : {l | (l, t) ∈ D.swap.E ∧ D.swap.cube q l t = m} =
        {l | (l, t) ∈ D.E ∧ D.cube q l t = ![m 0, m 2, m 1]} := by
      ext l
      simp only [Set.mem_ofPred_eq, JetData.swap_E, JetData.swap_cube, perm3_eq]
    rw [this]; exact hD.abscap t q hζq hq1 _
  rowcomp := fun l t l' u h h' i => by
    fin_cases i
    · simpa using hD.rowcomp l t l' u h h' 1
    · simpa using hD.rowcomp l t l' u h h' 0
  rescomp := fun l t l' u h h' => by
    have := hD.rescomp l t l' u h h'
    simp only [JetData.swap_x1, JetData.swap_xb, JetData.swap_y, swap2_zero, swap2_one]
    linarith
  mass := hD.mass

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
