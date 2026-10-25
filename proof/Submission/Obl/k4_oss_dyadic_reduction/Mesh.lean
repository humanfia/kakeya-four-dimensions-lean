import Submission.Obl.k4_oss_dyadic_reduction.Basic

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Submission.Obl.k4_oss_dyadic_reduction

noncomputable section
open scoped Classical

def sign (b : Bool) : ℝ := if b then 1 else -1

lemma sign_abs (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]

def meshScale {N : ℕ} (k : Fin N) : ℝ := ((k : ℕ) + 1 : ℝ) / N

def signedScale {N : ℕ} (p : Bool × Fin N) : ℝ := sign p.1 * meshScale p.2

def meshCell {N : ℕ} (p : Bool × Fin N) : Set ℝ :=
  (fun x => sign p.1 * x) ⁻¹'
    Ico (meshScale p.2) (meshScale p.2 + 1 / N)

lemma meshScale_pos {N : ℕ} (hN : 0 < N) (k : Fin N) : 0 < meshScale k := by
  unfold meshScale
  positivity

lemma meshScale_le_one {N : ℕ} (hN : 0 < N) (k : Fin N) : meshScale k ≤ 1 := by
  rw [meshScale, div_le_one (by exact_mod_cast hN)]
  exact_mod_cast k.isLt

lemma meshScale_lower {N : ℕ} (hN : 0 < N) (k : Fin N) : 1 / N ≤ meshScale k := by
  unfold meshScale
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (0 : ℝ) ≤ (k : ℕ) := by positivity
  linarith

lemma abs_signedScale {N : ℕ} (hN : 0 < N) (p : Bool × Fin N) :
    |signedScale p| = meshScale p.2 := by
  simp [signedScale, abs_mul, sign_abs, abs_of_pos (meshScale_pos hN _)]

lemma measurableSet_meshCell {N : ℕ} (p : Bool × Fin N) : MeasurableSet (meshCell p) :=
  measurableSet_Ico.preimage (by fun_prop)

lemma meshCell_rescale {N : ℕ} (hN : 0 < N) (p : Bool × Fin N) :
    ∀ x ∈ meshCell p, x / signedScale p ∈ Icc (1 : ℝ) 2 := by
  intro x hx
  have hc := meshScale_pos hN p.2
  have hb := meshScale_lower hN p.2
  change meshScale p.2 ≤ sign p.1 * x ∧
    sign p.1 * x < meshScale p.2 + 1 / N at hx
  have he : x / signedScale p = (sign p.1 * x) / meshScale p.2 := by
    rcases p with ⟨b, k⟩
    cases b <;> simp [signedScale, sign, neg_div, div_neg]
  rw [he]
  exact ⟨(le_div_iff₀ hc).mpr (by simpa using hx.1),
    (div_le_iff₀ hc).mpr (by linarith [hx.2])⟩

lemma meshCell_disjoint {N : ℕ} (hN : 0 < N) :
    Pairwise (fun p q : Bool × Fin N => Disjoint (meshCell p) (meshCell q)) := by
  rintro ⟨b, k⟩ ⟨c, l⟩ hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  change meshScale k ≤ sign b * x ∧ sign b * x < meshScale k + 1 / N at hx
  change meshScale l ≤ sign c * x ∧ sign c * x < meshScale l + 1 / N at hy
  have hposk := meshScale_pos hN k
  have hposl := meshScale_pos hN l
  have hbc : b = c := by
    cases b <;> cases c <;> simp_all [sign] <;> linarith
  subst c
  have hkl : k ≠ l := by intro he; exact hne (by simp [he])
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hgap {i j : Fin N} (hij : i < j) : meshScale i + 1 / N ≤ meshScale j := by
    rw [meshScale, meshScale, ← add_div]
    apply (div_le_div_iff_of_pos_right hNR).mpr
    have ht : (i : ℕ) + 1 ≤ (j : ℕ) := hij
    exact_mod_cast (show (i : ℕ) + 1 + 1 ≤ (j : ℕ) + 1 by omega)
  rcases lt_or_gt_of_ne hkl with h | h
  · have := hgap h
    linarith [hx.2, hy.1]
  · have := hgap h
    linarith [hy.2, hx.1]

lemma mesh_cover {N : ℕ} (hN : 0 < N) :
    Icc (-1 : ℝ) 1 ⊆ Ioo (-(1 / N : ℝ)) (1 / N) ∪
      ⋃ p : Bool × Fin N, meshCell p := by
  intro x hx
  by_cases hd : x ∈ Ioo (-(1 / N : ℝ)) (1 / N)
  · exact Or.inl hd
  right
  have habs : |x| ≤ 1 := abs_le.mpr hx
  have hdeep : 1 / (N : ℝ) ≤ |x| := by
    by_contra! hh
    exact hd (abs_lt.mp hh)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ht1 : 1 ≤ (N : ℝ) * |x| := (div_le_iff₀ hNR).mp hdeep |>.trans_eq (mul_comm _ _)
  have htN : (N : ℝ) * |x| ≤ N := by nlinarith
  let m : ℕ := ⌊(N : ℝ) * |x|⌋₊
  have hm1 : 1 ≤ m := Nat.le_floor (by simpa using ht1)
  have hmN : m ≤ N := Nat.floor_le_of_le htN
  let k : Fin N := ⟨m - 1, by omega⟩
  have hk : (k : ℕ) + 1 = m := Nat.sub_add_cancel hm1
  let b : Bool := decide (0 ≤ x)
  have hb : sign b * x = |x| := by
    by_cases h : 0 ≤ x
    · simp [b, sign, h, abs_of_nonneg h]
    · simp [b, sign, h, abs_of_neg (lt_of_not_ge h)]
  refine mem_iUnion.mpr ⟨(b, k), ?_⟩
  change meshScale k ≤ sign b * x ∧ sign b * x < meshScale k + 1 / N
  rw [hb]
  have hscale : meshScale k = (m : ℝ) / N := by
    unfold meshScale
    congr 1
    exact_mod_cast hk
  rw [hscale]
  constructor
  · exact (div_le_iff₀ hNR).mpr (by
      simpa [m, mul_comm] using Nat.floor_le (mul_nonneg hNR.le (abs_nonneg x)))
  · rw [← add_div]
    exact (lt_div_iff₀ hNR).mpr (by
      simpa [m, mul_comm] using Nat.lt_floor_add_one ((N : ℝ) * |x|))

abbrev GoodCell (μ : Measure ℝ) (N : ℕ) (η : ℝ) :=
  {p : Bool × Fin N // η ≤ μ.real (meshCell p)}

def goodRegion (μ : Measure ℝ) (N : ℕ) (η : ℝ) : Set ℝ :=
  ⋃ p : GoodCell μ N η, meshCell p.val

lemma measurableSet_goodRegion (μ : Measure ℝ) (N : ℕ) (η : ℝ) :
    MeasurableSet (goodRegion μ N η) := by
  classical
  exact MeasurableSet.iUnion fun _ => measurableSet_meshCell _

lemma goodCell_disjoint (μ : Measure ℝ) {N : ℕ} (hN : 0 < N) (η : ℝ) :
    Pairwise (fun p q : GoodCell μ N η => Disjoint (meshCell p.val) (meshCell q.val)) := by
  intro p q h
  exact meshCell_disjoint hN (by exact fun he => h (Subtype.ext he))

lemma restrict_goodRegion (μ : Measure ℝ) {N : ℕ} (hN : 0 < N) (η : ℝ) :
    μ.restrict (goodRegion μ N η) =
      ∑ p : GoodCell μ N η, μ.restrict (meshCell p.val) := by
  classical
  rw [goodRegion, Measure.restrict_iUnion (goodCell_disjoint μ hN η)
    (fun _ => measurableSet_meshCell _), Measure.sum_fintype]

lemma sum_goodCell_mass_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N) (η : ℝ) :
    ∑ p : GoodCell μ N η, (μ.restrict (meshCell p.val)).real univ ≤ 1 := by
  classical
  simp only [measureReal_restrict_apply MeasurableSet.univ, univ_inter]
  rw [← measureReal_iUnion_fintype (goodCell_disjoint μ hN η)
    (fun _ => measurableSet_meshCell _)]
  exact measureReal_le_one

lemma discarded_mass_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupport : μ (Icc (-1 : ℝ) 1)ᶜ = 0) {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 ≤ η) :
    μ.real (goodRegion μ N η)ᶜ ≤
      μ.real (Icc (-(1 / N : ℝ)) (1 / N)) + 2 * N * η := by
  classical
  let L : Bool × Fin N → Set ℝ := fun p =>
    if μ.real (meshCell p) < η then meshCell p else ∅
  have hsub : (goodRegion μ N η)ᶜ ⊆
      (Icc (-1 : ℝ) 1)ᶜ ∪ (Icc (-(1 / N : ℝ)) (1 / N) ∪ ⋃ p, L p) := by
    intro x hx
    by_cases hu : x ∈ Icc (-1 : ℝ) 1
    · right
      rcases mesh_cover hN hu with hd | hm
      · exact Or.inl ⟨hd.1.le, hd.2.le⟩
      · right
        rcases mem_iUnion.mp hm with ⟨p, hp⟩
        have hl : μ.real (meshCell p) < η := by
          by_contra! hheavy
          exact hx (mem_iUnion.mpr ⟨⟨p, hheavy⟩, hp⟩)
        exact mem_iUnion.mpr ⟨p, by simpa [L, hl] using hp⟩
    · exact Or.inl hu
  have hL (p : Bool × Fin N) : μ.real (L p) ≤ η := by
    dsimp [L]
    split_ifs with h
    · exact h.le
    · simpa using hη
  calc
    μ.real (goodRegion μ N η)ᶜ ≤
        μ.real ((Icc (-1 : ℝ) 1)ᶜ ∪ (Icc (-(1 / N : ℝ)) (1 / N) ∪ ⋃ p, L p)) :=
      measureReal_mono hsub
    _ ≤ μ.real (Icc (-1 : ℝ) 1)ᶜ +
        μ.real (Icc (-(1 / N : ℝ)) (1 / N) ∪ ⋃ p, L p) := measureReal_union_le _ _
    _ ≤ μ.real (Icc (-1 : ℝ) 1)ᶜ +
        (μ.real (Icc (-(1 / N : ℝ)) (1 / N)) + ∑ p, μ.real (L p)) := by
      exact add_le_add le_rfl ((measureReal_union_le _ _).trans
        (add_le_add le_rfl (measureReal_iUnion_fintype_le L)))
    _ ≤ μ.real (Icc (-(1 / N : ℝ)) (1 / N)) + 2 * N * η := by
      have hz : μ.real (Icc (-1 : ℝ) 1)ᶜ = 0 := by simp [measureReal_def, hsupport]
      rw [hz, zero_add]
      have hsum := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hL p)
      apply add_le_add le_rfl
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_ofNat] using hsum

end
end Submission.Obl.k4_oss_dyadic_reduction
