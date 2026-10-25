import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.Chart
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.SlicedFit

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The block sliced model

Paper Proposition 5.4, "Local normalization" and "Fitting one row component": on a time block
`[tI, tI + H]`, with the row frozen at a labeled time `tS`, a group of lines labeled at `tS`
(one `H`-bin of `B_l = x̄_l(tI) - F(tS) · y_l` and one `p`-slice of `y₁`) gives the sliced model
`Block.data` for the first row component: time `u = (t - tI)/H`, prior divided by `H^d p`,
scalar `L_l(u) = (S_l(tI + Hu) - bH)/H + φ₁(u) c p`, slope envelope `G` (McShane extension of
the residual slopes, clamped), row envelope `φ` (Lipschitz extension of
`(F(tI + Hu) - F(tS))/H` from labeled times). `Block.data_hyp` verifies `SlicedHyp` with
constant `200 K³`.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Block

variable (D : JetData Ω) (E : Set (Ω × ℝ)) (tI H p tS : ℝ) (b c : ℤ) (K d : ℝ)

/-- The normal scalar of a line at the block start with the row frozen at `tS`. -/
def Bv (l : Ω) : ℝ := D.xb l tI - D.Fy tS l

/-- A group: lines labeled at `tS`, in one `H`-bin of `Bv` and one `p`-slice of `y₁`. -/
def grp : Set Ω := {l | (l, tS) ∈ E ∧ ⌊Bv D tI tS l / H⌋ = b ∧ ⌊D.y l 1 / p⌋ = c}

/-- The normalized row increment of component `j`. -/
def phiR (j : Fin 2) (u : ℝ) : ℝ := (D.F (tI + H * u) j - D.F tS j) / H

/-- Normalized labeled times of the group. -/
def lamS : Set ℝ := {u | u ∈ Icc (0:ℝ) 1 ∧ ∃ l ∈ grp D E tI H p tS b c, (l, tI + H * u) ∈ E}

/-- The clamp to `[-M, M]`. -/
def clamp (M x : ℝ) : ℝ := max (-M) (min M x)

open Classical in
/-- The sliced model of the block, group and first row component. -/
def data : SlicedData Ω where
  ν := (1 / (H ^ d * p)).toNNReal • D.ν.restrict (grp D E tI H p tS b c)
  E := {q | q.1 ∈ grp D E tI H p tS b c ∧ (q.1, tI + H * q.2) ∈ E ∧ q.2 ∈ Icc (0:ℝ) 1}
  v := fun l => D.y l 0
  z := fun l => if l ∈ grp D E tI H p tS b c then (Bv D tI tS l - b * H) / H else 0
  L := fun l u => (D.S l (tI + H * u) - b * H) / H + phiR D tI H tS 1 u * (c * p)
  G := fun v => clamp (200 * K ^ 3)
    (lipEnv (grp D E tI H p tS b c) D.x1 (fun l => D.y l 0) (7 * K ^ 2) v)
  φ := lipEnv (lamS D E tI H p tS b c) (phiR D tI H tS 0) id K

end Block

namespace Block

variable {D : JetData Ω} {E : Set (Ω × ℝ)} {tI H p tS : ℝ} {b c : ℤ} {K d ζ : ℝ}

theorem S_shift (D : JetData Ω) (tI H tS : ℝ) (hH : H ≠ 0) (l : Ω) (u : ℝ) :
    D.S l (tI + H * u) = Bv D tI tS l + H * u * D.x1 l -
      H * (phiR D tI H tS 0 u * D.y l 0 + phiR D tI H tS 1 u * D.y l 1) := by
  simp only [JetData.S, JetData.xb, JetData.Fy, Bv, phiR]
  field_simp
  ring

theorem S_at_tS (D : JetData Ω) (tI tS : ℝ) (l : Ω) :
    D.S l tS = Bv D tI tS l + (tS - tI) * D.x1 l := by
  simp only [JetData.S, JetData.xb, JetData.Fy, Bv]; ring

theorem measurable_S (hD : JetHyp D ζ K d) : Measurable (fun q : Ω × ℝ => D.S q.1 q.2) := by
  have hy0 : Measurable (fun q : Ω × ℝ => D.y q.1 0) := (hD.meas_y 0).comp measurable_fst
  have hy1 : Measurable (fun q : Ω × ℝ => D.y q.1 1) := (hD.meas_y 1).comp measurable_fst
  have hF0 : Measurable (fun q : Ω × ℝ => D.F q.2 0) := (hD.meas_F 0).comp measurable_snd
  have hF1 : Measurable (fun q : Ω × ℝ => D.F q.2 1) := (hD.meas_F 1).comp measurable_snd
  have hx0 : Measurable (fun q : Ω × ℝ => D.x0 q.1) := hD.meas_x0.comp measurable_fst
  have hx1 : Measurable (fun q : Ω × ℝ => D.x1 q.1) := hD.meas_x1.comp measurable_fst
  show Measurable (fun q : Ω × ℝ => D.x0 q.1 + q.2 * D.x1 q.1 -
    (D.F q.2 0 * D.y q.1 0 + D.F q.2 1 * D.y q.1 1))
  exact (hx0.add (measurable_snd.mul hx1)).sub ((hF0.mul hy0).add (hF1.mul hy1))

theorem measurable_Bv (hD : JetHyp D ζ K d) : Measurable (Bv D tI tS) := by
  show Measurable (fun l => D.x0 l + tI * D.x1 l - (D.F tS 0 * D.y l 0 + D.F tS 1 * D.y l 1))
  exact (hD.meas_x0.add (measurable_const.mul hD.meas_x1)).sub
    ((measurable_const.mul (hD.meas_y 0)).add (measurable_const.mul (hD.meas_y 1)))

theorem measurableSet_grp (hD : JetHyp D ζ K d) (hE : MeasurableSet E) :
    MeasurableSet (grp D E tI H p tS b c) := by
  have h1 : MeasurableSet {l | (l, tS) ∈ E} := measurable_prodMk_right hE
  have h2 : MeasurableSet {l | ⌊Bv D tI tS l / H⌋ = b} :=
    (Int.measurable_floor.comp ((measurable_Bv hD).div_const H)) (measurableSet_singleton b)
  have h3 : MeasurableSet {l | ⌊D.y l 1 / p⌋ = c} :=
    (Int.measurable_floor.comp ((hD.meas_y 1).div_const p)) (measurableSet_singleton c)
  have : grp D E tI H p tS b c = {l | (l, tS) ∈ E} ∩ ({l | ⌊Bv D tI tS l / H⌋ = b} ∩
      {l | ⌊D.y l 1 / p⌋ = c}) := by ext l; simp [grp]
  rw [this]; exact h1.inter (h2.inter h3)

/-- The normalized row increment is bounded by `2K` at labeled times. -/
theorem abs_phiR_le (hD : JetHyp D ζ K d) (hEsub : E ⊆ D.E) (hH : 0 < H) (hζH : ζ ≤ H)
    (htS : tS ∈ Icc tI (tI + H)) (hK : 0 ≤ K) {u : ℝ} (hu : u ∈ lamS D E tI H p tS b c)
    (j : Fin 2) : |phiR D tI H tS j u| ≤ 2 * K := by
  obtain ⟨hu01, l, hl, hlu⟩ := hu
  have h := hD.rowcomp l (tI + H * u) l tS (hEsub hlu) (hEsub hl.1) j
  have h2 : |tI + H * u - tS| ≤ H := by
    rw [abs_le]; constructor <;> nlinarith [htS.1, htS.2, hu01.1, hu01.2]
  simp only [phiR]
  rw [abs_div, abs_of_pos hH, div_le_iff₀ hH]
  calc |D.F (tI + H * u) j - D.F tS j| ≤ K * (|tI + H * u - tS| + ζ) := h
    _ ≤ K * (H + H) := by gcongr
    _ = 2 * K * H := by ring

/-- The normalized row is `K`-Lipschitz with slack `ζ/H` on labeled times. -/
theorem phiR_slack (hD : JetHyp D ζ K d) (hEsub : E ⊆ D.E) (hH : 0 < H) {u u' : ℝ}
    (hu : u ∈ lamS D E tI H p tS b c) (hu' : u' ∈ lamS D E tI H p tS b c) (j : Fin 2) :
    phiR D tI H tS j u ≤ phiR D tI H tS j u' + K * (|u - u'| + ζ / H) := by
  obtain ⟨-, l, -, hlu⟩ := hu
  obtain ⟨-, l', -, hlu'⟩ := hu'
  have h := hD.rowcomp l (tI + H * u) l' (tI + H * u') (hEsub hlu) (hEsub hlu') j
  have e : tI + H * u - (tI + H * u') = H * (u - u') := by ring
  rw [e, abs_mul, abs_of_pos hH] at h
  have : phiR D tI H tS j u - phiR D tI H tS j u' =
      (D.F (tI + H * u) j - D.F (tI + H * u') j) / H := by simp only [phiR]; field_simp; ring
  have h3 : (D.F (tI + H * u) j - D.F (tI + H * u') j) / H ≤ K * (|u - u'| + ζ / H) := by
    rw [div_le_iff₀ hH]
    calc D.F (tI + H * u) j - D.F (tI + H * u') j ≤ |D.F (tI + H * u) j - D.F (tI + H * u') j| :=
          le_abs_self _
      _ ≤ K * (H * |u - u'| + ζ) := h
      _ = K * (|u - u'| + ζ / H) * H := by field_simp
  linarith

/-- The residual slopes of a group are `7K²`-Lipschitz in `y₀` with slack `p`. -/
theorem x1_slack (hD : JetHyp D ζ K d) (hEsub : E ⊆ D.E) (hH : 0 < H) (hHp : H ≤ p)
    (hζp : ζ ≤ p) (hK : 1 ≤ K) (htS : tS ∈ Icc tI (tI + H)) {l l' : Ω}
    (hl : l ∈ grp D E tI H p tS b c) (hl' : l' ∈ grp D E tI H p tS b c) :
    D.x1 l ≤ D.x1 l' + 7 * K ^ 2 * (|D.y l 0 - D.y l' 0| + p) := by
  have hp : 0 < p := hH.trans_le hHp
  obtain ⟨hlE, hlb, hlc⟩ := hl
  obtain ⟨hlE', hlb', hlc'⟩ := hl'
  have h := hD.rescomp l tS l' tS (hEsub hlE) (hEsub hlE')
  simp only [sub_self, abs_zero, zero_add] at h
  -- same `H`-bin of `Bv`
  have hB : |Bv D tI tS l - Bv D tI tS l'| ≤ H := by
    have a1 := Int.floor_le (Bv D tI tS l / H); have a2 := Int.lt_floor_add_one (Bv D tI tS l / H)
    have a3 := Int.floor_le (Bv D tI tS l' / H); have a4 := Int.lt_floor_add_one (Bv D tI tS l' / H)
    rw [hlb] at a1 a2; rw [hlb'] at a3 a4
    rw [le_div_iff₀ hH] at a1 a3; rw [div_lt_iff₀ hH] at a2 a4
    rw [abs_le]; constructor <;> nlinarith
  have hy1 : |D.y l 1 - D.y l' 1| ≤ p := by
    have a1 := Int.floor_le (D.y l 1 / p); have a2 := Int.lt_floor_add_one (D.y l 1 / p)
    have a3 := Int.floor_le (D.y l' 1 / p); have a4 := Int.lt_floor_add_one (D.y l' 1 / p)
    rw [hlc] at a1 a2; rw [hlc'] at a3 a4
    rw [le_div_iff₀ hp] at a1 a3; rw [div_lt_iff₀ hp] at a2 a4
    rw [abs_le]; constructor <;> nlinarith
  have bxl : |D.x1 l| ≤ K := le_trans (le_add_of_nonneg_left (abs_nonneg _)) (hD.bound_x l)
  have bxl' : |D.x1 l'| ≤ K := le_trans (le_add_of_nonneg_left (abs_nonneg _)) (hD.bound_x l')
  have hF0 := hD.bound_F tS 0
  have hF1 := hD.bound_F tS 1
  -- the spatial distance at `tS`
  have hxb : |D.xb l tS - D.xb l' tS| ≤ H + 2 * K * H + K * (|D.y l 0 - D.y l' 0| +
      |D.y l 1 - D.y l' 1|) := by
    have e : D.xb l tS - D.xb l' tS = (Bv D tI tS l - Bv D tI tS l') +
        (tS - tI) * (D.x1 l - D.x1 l') +
        (D.F tS 0 * (D.y l 0 - D.y l' 0) + D.F tS 1 * (D.y l 1 - D.y l' 1)) := by
      simp only [Bv, JetData.xb, JetData.Fy]; ring
    rw [e]
    have t1 : |(tS - tI) * (D.x1 l - D.x1 l')| ≤ H * (2 * K) := by
      rw [abs_mul]
      exact mul_le_mul (by rw [abs_le]; constructor <;> linarith [htS.1, htS.2])
        ((abs_sub _ _).trans (by linarith)) (abs_nonneg _) hH.le
    have t2 : |D.F tS 0 * (D.y l 0 - D.y l' 0) + D.F tS 1 * (D.y l 1 - D.y l' 1)| ≤
        K * (|D.y l 0 - D.y l' 0| + |D.y l 1 - D.y l' 1|) := by
      calc _ ≤ |D.F tS 0 * (D.y l 0 - D.y l' 0)| + |D.F tS 1 * (D.y l 1 - D.y l' 1)| :=
            abs_add_le _ _
        _ ≤ K * |D.y l 0 - D.y l' 0| + K * |D.y l 1 - D.y l' 1| := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul_of_nonneg_right hF0 (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hF1 (abs_nonneg _))
        _ = _ := by ring
    have t3 := abs_add_three (Bv D tI tS l - Bv D tI tS l') ((tS - tI) * (D.x1 l - D.x1 l'))
      (D.F tS 0 * (D.y l 0 - D.y l' 0) + D.F tS 1 * (D.y l 1 - D.y l' 1))
    linarith
  have hfin : |D.x1 l - D.x1 l'| ≤ 7 * K ^ 2 * (|D.y l 0 - D.y l' 0| + p) := by
    have hK0 : 0 ≤ K := by linarith
    calc |D.x1 l - D.x1 l'| ≤ K * (|D.xb l tS - D.xb l' tS| + |D.y l 0 - D.y l' 0| +
          |D.y l 1 - D.y l' 1| + ζ) := h
      _ ≤ K * ((H + 2 * K * H + K * (|D.y l 0 - D.y l' 0| + |D.y l 1 - D.y l' 1|)) +
          |D.y l 0 - D.y l' 0| + |D.y l 1 - D.y l' 1| + ζ) := by gcongr
      _ ≤ K * ((p + 2 * K * p + K * (|D.y l 0 - D.y l' 0| + p)) + |D.y l 0 - D.y l' 0| + p + p) := by
          gcongr
      _ = K * (K + 1) * |D.y l 0 - D.y l' 0| + (3 * K ^ 2 + 3 * K) * p := by ring
      _ ≤ 7 * K ^ 2 * |D.y l 0 - D.y l' 0| + 7 * K ^ 2 * p := by
          have hy0 := abs_nonneg (D.y l 0 - D.y l' 0)
          have a1 : K * (K + 1) ≤ 7 * K ^ 2 := by nlinarith
          have a2 : 3 * K ^ 2 + 3 * K ≤ 7 * K ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right a1 hy0
          have := mul_le_mul_of_nonneg_right a2 hp.le
          linarith
      _ = 7 * K ^ 2 * (|D.y l 0 - D.y l' 0| + p) := by ring
  linarith [(abs_le.1 hfin).2]

end Block

namespace Block

variable {D : JetData Ω} {E : Set (Ω × ℝ)} {tI H p tS : ℝ} {b c : ℤ} {K d ζ : ℝ}

theorem LocalCount.mono {S S' : Set ℝ} {δ K K' d : ℝ} (hδ : 0 < δ) (h : LocalCount S δ K d)
    (hSS : S' ⊆ S) (hKK : K ≤ K') : LocalCount S' δ K' d := by
  intro a L s hs hsL
  obtain ⟨m, cc, hcov, hm⟩ := h a L s hs hsL
  refine ⟨m, cc, (inter_subset_inter_left _ hSS).trans hcov, hm.trans ?_⟩
  have : 0 ≤ (L / s) ^ d := by
    apply Real.rpow_nonneg; apply div_nonneg <;> linarith [hs]
  nlinarith

theorem clamp_lip {M x y : ℝ} : |clamp M x - clamp M y| ≤ |x - y| := by
  simp only [clamp]
  have h1 : |max (min M x) (-M) - max (min M y) (-M)| ≤ |min M x - min M y| :=
    abs_max_sub_max_le_abs _ _ _
  have h2 : |min x M - min y M| ≤ |x - y| := by
    have := abs_min_sub_min_le_max x M y M
    simp only [sub_self, abs_zero] at this
    exact this.trans (max_le le_rfl (abs_nonneg _))
  rw [max_comm (-M), max_comm (-M)]
  rw [min_comm M x, min_comm M y] at h1 ⊢
  exact h1.trans h2

theorem clamp_of_abs_le {M x : ℝ} (h : |x| ≤ M) : clamp M x = x := by
  simp only [clamp]
  rw [min_eq_right (abs_le.1 h).2, max_eq_right (abs_le.1 h).1]

theorem abs_clamp_le {M x : ℝ} (hM : 0 ≤ M) : |clamp M x| ≤ M := by
  simp only [clamp]
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

end Block

namespace Block

variable {D : JetData Ω} {E : Set (Ω × ℝ)} {tI H p tS : ℝ} {b c : ℤ} {K d ζ : ℝ}

/-- The real arithmetic of the group mass bound. -/
theorem grp_mass_arith {K H p d : ℝ} (hK : 1 ≤ K) (hH : 0 < H) (hH1 : H ≤ 1) (hHp : H ≤ p) :
    (1 / (H ^ d * p)) * (((⌈2 * K / H⌉₊ + 1) * (⌈p / H⌉₊ + 1) *
      (⌈2 * K + 1⌉₊ + 2 * ⌈2 * K⌉₊ + 1) : ℕ) * (K * H ^ (2 + d))) ≤ 200 * K ^ 3 := by
  have hp : 0 < p := hH.trans_le hHp
  have hHd : 0 < H ^ d := Real.rpow_pos_of_pos hH d
  have e1 : ((⌈2 * K / H⌉₊ : ℕ) : ℝ) + 1 ≤ 4 * K / H := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * K / H by positivity)
    have h2 : 2 ≤ 2 * K / H := by rw [le_div_iff₀ hH]; nlinarith
    have : 2 * K / H + 2 ≤ 4 * K / H := by
      have : 4 * K / H = 2 * K / H + 2 * K / H := by ring
      linarith
    linarith
  have e2 : ((⌈p / H⌉₊ : ℕ) : ℝ) + 1 ≤ 3 * p / H := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ p / H by positivity)
    have h2 : 1 ≤ p / H := by rw [le_div_iff₀ hH]; linarith
    have : p / H + 2 ≤ 3 * p / H := by
      have : 3 * p / H = p / H + 2 * (p / H) := by ring
      linarith
    linarith
  have e3 : ((⌈2 * K + 1⌉₊ : ℕ) : ℝ) + 2 * ((⌈2 * K⌉₊ : ℕ) : ℝ) + 1 ≤ 11 * K := by
    have a := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * K + 1 by linarith)
    have b := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * K by linarith)
    linarith
  have hprod : (((⌈2 * K / H⌉₊ + 1) * (⌈p / H⌉₊ + 1) * (⌈2 * K + 1⌉₊ + 2 * ⌈2 * K⌉₊ + 1) : ℕ) : ℝ)
      ≤ (4 * K / H) * (3 * p / H) * (11 * K) := by
    push_cast
    apply mul_le_mul (mul_le_mul e1 e2 (by positivity) (by positivity)) e3 (by positivity)
      (by positivity)
  have hHpow : H ^ (2 + d) = H ^ 2 * H ^ d := by
    rw [Real.rpow_add hH, Real.rpow_two]
  calc (1 / (H ^ d * p)) * (((⌈2 * K / H⌉₊ + 1) * (⌈p / H⌉₊ + 1) *
        (⌈2 * K + 1⌉₊ + 2 * ⌈2 * K⌉₊ + 1) : ℕ) * (K * H ^ (2 + d)))
      ≤ (1 / (H ^ d * p)) * ((4 * K / H) * (3 * p / H) * (11 * K) * (K * H ^ (2 + d))) := by
        gcongr
    _ = 132 * K ^ 3 := by rw [hHpow]; field_simp; ring
    _ ≤ 200 * K ^ 3 := by nlinarith [pow_pos (show (0:ℝ) < K by linarith) 3]

/-- The real arithmetic of the sliced cap. -/
theorem cap_arith {K H p d : ℝ} (hK : 1 ≤ K) (hH : 0 < H) (hH1 : H ≤ 1) (hp : 0 < p) :
    (1 / (H ^ d * p)) * (((⌈1 / H⌉₊ + 1) * (⌈1 / H⌉₊ + 1) * (1 + 2 * ⌈2 * K⌉₊ + 1) : ℕ) *
      (K * (H * p) ^ (2 + d))) ≤ 200 * K ^ 3 * p ^ (1 + d) := by
  have hHd : 0 < H ^ d := Real.rpow_pos_of_pos hH d
  have e1 : ((⌈1 / H⌉₊ : ℕ) : ℝ) + 1 ≤ 3 / H := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 1 / H by positivity)
    have h2 : 1 ≤ 1 / H := by rw [le_div_iff₀ hH]; linarith
    have : 1 / H + 2 ≤ 3 / H := by
      have : 3 / H = 1 / H + 2 * (1 / H) := by ring
      linarith
    linarith
  have e3 : 1 + 2 * ((⌈2 * K⌉₊ : ℕ) : ℝ) + 1 ≤ 8 * K := by
    have b := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * K by linarith)
    linarith
  have hprod : (((⌈1 / H⌉₊ + 1) * (⌈1 / H⌉₊ + 1) * (1 + 2 * ⌈2 * K⌉₊ + 1) : ℕ) : ℝ)
      ≤ (3 / H) * (3 / H) * (8 * K) := by
    push_cast
    apply mul_le_mul (mul_le_mul e1 e1 (by positivity) (by positivity)) e3 (by positivity)
      (by positivity)
  have hpow : (H * p) ^ (2 + d) = H ^ 2 * H ^ d * (p * p ^ (1 + d)) := by
    rw [Real.mul_rpow hH.le hp.le, Real.rpow_add hH, Real.rpow_two]
    have : p ^ (2 + d) = p * p ^ (1 + d) := by
      rw [show (2 + d) = 1 + (1 + d) by ring, Real.rpow_add hp, Real.rpow_one]
    rw [this]
  calc (1 / (H ^ d * p)) * (((⌈1 / H⌉₊ + 1) * (⌈1 / H⌉₊ + 1) * (1 + 2 * ⌈2 * K⌉₊ + 1) : ℕ) *
        (K * (H * p) ^ (2 + d)))
      ≤ (1 / (H ^ d * p)) * ((3 / H) * (3 / H) * (8 * K) * (K * (H * p) ^ (2 + d))) := by gcongr
    _ = 72 * K ^ 2 * p ^ (1 + d) := by rw [hpow]; field_simp; ring
    _ ≤ 200 * K ^ 3 * p ^ (1 + d) := by
        have hpd : 0 < p ^ (1 + d) := Real.rpow_pos_of_pos hp _
        have : 72 * K ^ 2 ≤ 200 * K ^ 3 := by nlinarith
        nlinarith

end Block

namespace Block

variable {D : JetData Ω} {E : Set (Ω × ℝ)} {tI H p tS : ℝ} {b c : ℤ} {K d ζ : ℝ}

set_option maxHeartbeats 4000000 in
/-- **The block sliced model satisfies the sliced hypotheses** (paper "Local normalization" and
"Fitting one row component": `a04:local-joint-cap`, `a04:frozen-q-comparison`,
`a04:sliced-model`, `a04:sliced-cap`). -/
theorem data_hyp (hD : JetHyp D ζ K d) (hK : 1 ≤ K) (hd : 0 ≤ d) (hEsub : E ⊆ D.E)
    (hEm : MeasurableSet E) (hH : 0 < H) (hH1 : H ≤ 1) (hHp : H ≤ p) (hp1 : p ≤ 1)
    (hζ0 : 0 < ζ) (hζ : ζ ≤ H * p) (htS : tS ∈ Icc tI (tI + H))
    (hgrp : (grp D E tI H p tS b c).Nonempty) (hlam : (lamS D E tI H p tS b c).Nonempty)
    (Ks : ℝ) (hKs : 200 * K ^ 3 ≤ Ks)
    (hmass : ENNReal.ofReal (1 / Ks) ≤
      ((data D E tI H p tS b c K d).ν.prod volume) (data D E tI H p tS b c K d).E) :
    SlicedHyp (data D E tI H p tS b c K d) p Ks d := by
  classical
  have hp : 0 < p := hH.trans_le hHp
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  have h3K' : 3 * K ≤ 200 * K ^ 3 := by nlinarith [pow_pos (show (0:ℝ) < K by linarith) 2]
  have h3K : 3 * K ≤ Ks := h3K'.trans hKs
  have hK0 : 0 < K := by linarith
  have hKK' : K ≤ 200 * K ^ 3 := by nlinarith [pow_pos hK0 2]
  have hKK : K ≤ Ks := hKK'.trans hKs
  have hζH : ζ ≤ H := hζ.trans (by nlinarith)
  have hζp : ζ ≤ p := hζH.trans hHp
  have hprob := hD.prob
  have hgm := measurableSet_grp (tI := tI) (H := H) (p := p) (tS := tS) (b := b) (c := c) hD hEm
  set g := grp D E tI H p tS b c with hg
  set Λ := lamS D E tI H p tS b c with hΛ
  set r : NNReal := (1 / (H ^ d * p)).toNNReal with hr
  have hr' : (r : ENNReal) = ENNReal.ofReal (1 / (H ^ d * p)) := rfl
  -- boundedness facts
  have hx1 : ∀ l, |D.x1 l| ≤ K := fun l => le_trans (le_add_of_nonneg_left (abs_nonneg _))
    (hD.bound_x l)
  have hfx : ∀ a ∈ g, -K ≤ D.x1 a := fun a _ => (abs_le.1 (hx1 a)).1
  have hfφ : ∀ a ∈ Λ, -(2 * K) ≤ phiR D tI H tS 0 a := fun a ha =>
    (abs_le.1 (abs_phiR_le hD hEsub hH hζH htS hK0.le ha 0)).1
  -- the envelope approximations
  have hGnear : ∀ l ∈ g, |lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) (D.y l 0) - D.x1 l| ≤
      7 * K ^ 2 * p := fun l hl =>
    lipEnv_near (g := fun l => D.y l 0) (by positivity) hfx
      (fun a ha b hb => x1_slack hD hEsub hH hHp hζp hK htS ha hb) hl
  have hφnear : ∀ u ∈ Λ, |lipEnv Λ (phiR D tI H tS 0) id K u - phiR D tI H tS 0 u| ≤ K * (ζ / H) :=
    fun u hu => by
      have := lipEnv_near (g := id) (L := K) (e := ζ / H) hK0.le hfφ
        (fun a ha b hb => phiR_slack hD hEsub hH ha hb 0) hu
      simpa using this
  have hφlip : ∀ u u', |lipEnv Λ (phiR D tI H tS 0) id K u - lipEnv Λ (phiR D tI H tS 0) id K u'|
      ≤ K * |u - u'| := fun u u' => by
    have := lipEnv_lip (g := id) hlam hK0.le hfφ u u'
    simpa using this
  refine
    { finite := ?_, mass_le := ?_, measE := ?_, E01 := ?_, measv := ?_, measL := ?_,
      vbound := ?_, zbound := ?_, Glip := ?_, Gbound := ?_, measφ := ?_, φbound := ?_,
      φlip := ?_, model := ?_, count := ?_, cap := ?_, mass := hmass }
  · show IsFiniteMeasure (r • D.ν.restrict g); infer_instance
  · -- mass bound of the group
    show (r • D.ν.restrict g) univ ≤ ENNReal.ofReal Ks
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      ENNReal.smul_def, smul_eq_mul, hr']
    have hslab := slab_cap hD hK0.le (t := tS) hH hζH hH1 (-K) (c * p) (b * H - K * H)
      ⌈2 * K / H⌉₊ ⌈p / H⌉₊ ⌈2 * K + 1⌉₊ g (by
        intro l hl
        obtain ⟨hlE, hlb, hlc⟩ := hl
        have hy0 := hD.bound_y l 0
        have a1 := Int.floor_le (D.y l 1 / p); have a2 := Int.lt_floor_add_one (D.y l 1 / p)
        rw [hlc, le_div_iff₀ hp] at a1; rw [hlc, div_lt_iff₀ hp] at a2
        have b1 := Int.floor_le (Bv D tI tS l / H); have b2 := Int.lt_floor_add_one (Bv D tI tS l / H)
        rw [hlb, le_div_iff₀ hH] at b1; rw [hlb, div_lt_iff₀ hH] at b2
        have hc1 : 2 * K ≤ (⌈2 * K / H⌉₊ : ℝ) * H := by
          have := Nat.le_ceil (2 * K / H); rwa [div_le_iff₀ hH] at this
        have hc2 : p ≤ (⌈p / H⌉₊ : ℝ) * H := by
          have := Nat.le_ceil (p / H); rwa [div_le_iff₀ hH] at this
        have hc3 : 2 * K + 1 ≤ (⌈2 * K + 1⌉₊ : ℝ) := Nat.le_ceil _
        have hSt := S_at_tS D tI tS l
        have hxt : |(tS - tI) * D.x1 l| ≤ H * K := by
          rw [abs_mul]; exact mul_le_mul (by rw [abs_le]; constructor <;> linarith [htS.1, htS.2])
            (hx1 l) (abs_nonneg _) hH.le
        refine ⟨hEsub hlE, by linarith [(abs_le.1 hy0).1], by linarith [(abs_le.1 hy0).2], by linarith,
          by linarith, ?_, ?_⟩
        · rw [hSt]; linarith [(abs_le.1 hxt).1]
        · rw [hSt]; nlinarith [(abs_le.1 hxt).2])
    calc ENNReal.ofReal (1 / (H ^ d * p)) * D.ν g
        ≤ ENNReal.ofReal (1 / (H ^ d * p)) * ((((⌈2 * K / H⌉₊ + 1) * (⌈p / H⌉₊ + 1) *
            (⌈2 * K + 1⌉₊ + 2 * ⌈2 * K⌉₊ + 1) : ℕ) : ENNReal) * ENNReal.ofReal (K * H ^ (2 + d))) := by
          gcongr
      _ = ENNReal.ofReal ((1 / (H ^ d * p)) * (((⌈2 * K / H⌉₊ + 1) * (⌈p / H⌉₊ + 1) *
            (⌈2 * K + 1⌉₊ + 2 * ⌈2 * K⌉₊ + 1) : ℕ) * (K * H ^ (2 + d)))) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal Ks := ENNReal.ofReal_le_ofReal ((grp_mass_arith hK hH hH1 hHp).trans hKs)
  · -- measurability of the labels
    show MeasurableSet {q : Ω × ℝ | q.1 ∈ g ∧ (q.1, tI + H * q.2) ∈ E ∧ q.2 ∈ Icc (0:ℝ) 1}
    have h1 : MeasurableSet {q : Ω × ℝ | q.1 ∈ g} := measurable_fst hgm
    have h2 : MeasurableSet {q : Ω × ℝ | (q.1, tI + H * q.2) ∈ E} :=
      (measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd))) hEm
    have h3 : MeasurableSet {q : Ω × ℝ | q.2 ∈ Icc (0:ℝ) 1} := measurable_snd measurableSet_Icc
    exact h1.inter (h2.inter h3)
  · intro q hq; exact hq.2.2
  · exact hD.meas_y 0
  · -- measurability of the scalars
    show Measurable (fun q : Ω × ℝ => (D.S q.1 (tI + H * q.2) - b * H) / H +
      phiR D tI H tS 1 q.2 * (c * p))
    have hS := measurable_S hD
    have h1 : Measurable (fun q : Ω × ℝ => D.S q.1 (tI + H * q.2)) :=
      hS.comp (measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd)))
    have h2 : Measurable (fun q : Ω × ℝ => phiR D tI H tS 1 q.2) := by
      show Measurable (fun q : Ω × ℝ => (D.F (tI + H * q.2) 1 - D.F tS 1) / H)
      exact (((hD.meas_F 1).comp (measurable_const.add (measurable_const.mul
        measurable_snd))).sub measurable_const).div_const H
    exact ((h1.sub measurable_const).div_const H).add (h2.mul measurable_const)
  · intro l; exact (hD.bound_y l 0).trans hKK
  · intro l
    show |(if l ∈ g then (Bv D tI tS l - b * H) / H else 0)| ≤ Ks
    split_ifs with hl
    · have b1 := Int.floor_le (Bv D tI tS l / H); have b2 := Int.lt_floor_add_one (Bv D tI tS l / H)
      rw [hl.2.1] at b1 b2
      have : |(Bv D tI tS l - b * H) / H| ≤ 1 := by
        rw [abs_div, abs_of_pos hH, div_le_one hH, abs_le]
        rw [le_div_iff₀ hH] at b1; rw [div_lt_iff₀ hH] at b2
        constructor <;> nlinarith
      linarith
    · simp; linarith
  · intro x y
    show |clamp (200 * K ^ 3) (lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) x) -
      clamp (200 * K ^ 3) (lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) y)| ≤ Ks * |x - y|
    calc _ ≤ |lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) x -
          lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) y| := clamp_lip
      _ ≤ 7 * K ^ 2 * |x - y| := lipEnv_lip hgrp (by positivity) hfx x y
      _ ≤ Ks * |x - y| := by
          have : 7 * K ^ 2 ≤ Ks := by nlinarith [pow_pos hK0 2]
          exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  · intro x _
    exact (abs_clamp_le (by positivity)).trans hKs
  · -- the row is continuous
    show Measurable (lipEnv Λ (phiR D tI H tS 0) id K)
    have hlipw : LipschitzWith K.toNNReal (lipEnv Λ (phiR D tI H tS 0) id K) := by
      apply LipschitzWith.of_dist_le_mul
      intro u u'
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0.le]
      exact hφlip u u'
    exact hlipw.continuous.measurable
  · intro u hu
    show |lipEnv Λ (phiR D tI H tS 0) id K u| ≤ Ks
    obtain ⟨a, ha⟩ := hlam
    have hup := lipEnv_le (g := id) hK0.le hfφ u ha
    have hlo : -(2 * K) ≤ lipEnv Λ (phiR D tI H tS 0) id K u := by
      have : Nonempty Λ := ⟨⟨a, ha⟩⟩
      apply le_ciInf
      intro a'
      have h1 := hfφ a' a'.2
      have h2 : 0 ≤ K * |u - id (a' : ℝ)| := mul_nonneg hK0.le (abs_nonneg _)
      linarith
    have hpa := abs_phiR_le hD hEsub hH hζH htS hK0.le ha 0
    have hua : |u - id a| ≤ 1 := by
      simp only [id]; rw [abs_le]; constructor <;> linarith [ha.1.1, ha.1.2, hu.1, hu.2]
    have hKa : K * |u - id a| ≤ K := by nlinarith
    rw [abs_le]; constructor
    · linarith
    · linarith [(abs_le.1 hpa).2]
  · intro u _ u' _
    calc |lipEnv Λ (phiR D tI H tS 0) id K u - lipEnv Λ (phiR D tI H tS 0) id K u'|
        ≤ K * |u - u'| := hφlip u u'
      _ ≤ Ks * (|u - u'| + p) := by
          have := abs_nonneg (u - u')
          nlinarith
  · -- the model error
    rintro ⟨l, u⟩ ⟨hl, hlu, hu01⟩
    have huΛ : u ∈ Λ := ⟨hu01, l, hl, hlu⟩
    show |((D.S l (tI + H * u) - b * H) / H + phiR D tI H tS 1 u * (c * p)) -
      ((if l ∈ g then (Bv D tI tS l - b * H) / H else 0) +
        u * clamp (200 * K ^ 3) (lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) (D.y l 0)) -
        lipEnv Λ (phiR D tI H tS 0) id K u * D.y l 0)| ≤ Ks * p
    rw [if_pos hl]
    have hGeq : clamp (200 * K ^ 3) (lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) (D.y l 0)) =
        lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) (D.y l 0) := by
      apply clamp_of_abs_le
      have h1 := hGnear l hl
      have h2 := hx1 l
      have : 7 * K ^ 2 * p ≤ 7 * K ^ 2 := by nlinarith [pow_pos hK0 2]
      calc |lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) (D.y l 0)|
          ≤ |lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) (D.y l 0) - D.x1 l| + |D.x1 l| := by
            have := abs_add_le (lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) (D.y l 0) - D.x1 l)
              (D.x1 l)
            simpa using this
        _ ≤ 200 * K ^ 3 := by nlinarith [pow_pos hK0 3, pow_pos hK0 2]
    rw [hGeq, S_shift D tI H tS hH.ne']
    have hc : |D.y l 1 - c * p| ≤ p := by
      have a1 := Int.floor_le (D.y l 1 / p); have a2 := Int.lt_floor_add_one (D.y l 1 / p)
      rw [hl.2.2, le_div_iff₀ hp] at a1; rw [hl.2.2, div_lt_iff₀ hp] at a2
      rw [abs_le]; constructor <;> linarith
    have hφ1 := abs_phiR_le hD hEsub hH hζH htS hK0.le huΛ 1
    have hy0 := hD.bound_y l 0
    set G0 := lipEnv g D.x1 (fun l => D.y l 0) (7 * K ^ 2) (D.y l 0)
    set φ0 := lipEnv Λ (phiR D tI H tS 0) id K u
    have key : ((Bv D tI tS l + H * u * D.x1 l -
        H * (phiR D tI H tS 0 u * D.y l 0 + phiR D tI H tS 1 u * D.y l 1) - b * H) / H +
        phiR D tI H tS 1 u * (c * p)) - ((Bv D tI tS l - b * H) / H + u * G0 - φ0 * D.y l 0) =
        -(phiR D tI H tS 1 u * (D.y l 1 - c * p)) + u * (D.x1 l - G0) +
          (φ0 - phiR D tI H tS 0 u) * D.y l 0 := by
      field_simp; ring
    rw [key]
    have t1 : |-(phiR D tI H tS 1 u * (D.y l 1 - c * p))| ≤ 2 * K * p := by
      rw [abs_neg, abs_mul]; exact mul_le_mul hφ1 hc (abs_nonneg _) (by positivity)
    have t2 : |u * (D.x1 l - G0)| ≤ 7 * K ^ 2 * p := by
      rw [abs_mul, abs_sub_comm]
      have hu1 : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu01.1, hu01.2]
      calc |u| * |G0 - D.x1 l| ≤ 1 * (7 * K ^ 2 * p) :=
            mul_le_mul hu1 (hGnear l hl) (abs_nonneg _) zero_le_one
        _ = 7 * K ^ 2 * p := one_mul _
    have t3 : |(φ0 - phiR D tI H tS 0 u) * D.y l 0| ≤ K ^ 2 * p := by
      rw [abs_mul]
      have h1 := hφnear u huΛ
      have h2 : K * (ζ / H) ≤ K * p := by
        apply mul_le_mul_of_nonneg_left _ hK0.le
        rw [div_le_iff₀ hH]; linarith
      calc |φ0 - phiR D tI H tS 0 u| * |D.y l 0| ≤ (K * p) * K :=
            mul_le_mul (h1.trans h2) hy0 (abs_nonneg _) (by positivity)
        _ = K ^ 2 * p := by ring
    have t4 := abs_add_three (-(phiR D tI H tS 1 u * (D.y l 1 - c * p))) (u * (D.x1 l - G0))
      ((φ0 - phiR D tI H tS 0 u) * D.y l 0)
    have : 2 * K * p + 7 * K ^ 2 * p + K ^ 2 * p ≤ Ks * p := by
      have : 2 * K + 7 * K ^ 2 + K ^ 2 ≤ Ks := by nlinarith [pow_pos hK0 2, pow_pos hK0 3]
      nlinarith
    linarith
  · -- the local count
    intro u
    have hres := localCount_rescale (S := {s | ∃ l, (l, tI + H * u) ∈ D.E ∧ s = D.S l (tI + H * u)})
      (c := b * H - H * phiR D tI H tS 1 u * (c * p)) (by positivity : 0 < 1 / H)
      (show 1 / H * ζ ≤ p by rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hH]; linarith)
      (hD.supp (tI + H * u))
    refine LocalCount.mono hp hres ?_ hKK
    rintro x ⟨l, ⟨hl, hlu, _⟩, rfl⟩
    refine ⟨D.S l (tI + H * u), ⟨l, hEsub hlu, rfl⟩, ?_⟩
    show (D.S l (tI + H * u) - b * H) / H + phiR D tI H tS 1 u * (c * p) =
      1 / H * (D.S l (tI + H * u) - (b * H - H * phiR D tI H tS 1 u * (c * p)))
    field_simp; ring
  · -- the sliced cap
    intro u c₁ c₂
    show (r • D.ν.restrict g) {l | (l, u) ∈ {q : Ω × ℝ | q.1 ∈ g ∧ (q.1, tI + H * q.2) ∈ E ∧
      q.2 ∈ Icc (0:ℝ) 1} ∧ ⌊D.y l 0 / p⌋ = c₁ ∧
      ⌊((D.S l (tI + H * u) - b * H) / H + phiR D tI H tS 1 u * (c * p)) / p⌋ = c₂} ≤
      ENNReal.ofReal (Ks * p ^ (1 + d))
    rw [Measure.smul_apply, Measure.restrict_apply' hgm, ENNReal.smul_def, smul_eq_mul, hr']
    have hHpq : 0 < H * p := mul_pos hH hp
    have hslab := slab_cap hD hK0.le (t := tI + H * u) hHpq hζ (by nlinarith) (c₁ * p) (c * p)
      (b * H - H * phiR D tI H tS 1 u * (c * p) + c₂ * (H * p)) ⌈1 / H⌉₊ ⌈1 / H⌉₊ 1
      ({l | (l, u) ∈ {q : Ω × ℝ | q.1 ∈ g ∧ (q.1, tI + H * q.2) ∈ E ∧ q.2 ∈ Icc (0:ℝ) 1} ∧
        ⌊D.y l 0 / p⌋ = c₁ ∧
        ⌊((D.S l (tI + H * u) - b * H) / H + phiR D tI H tS 1 u * (c * p)) / p⌋ = c₂} ∩ g) (by
        rintro l ⟨⟨⟨hl, hlu, hu01⟩, hc1, hc2⟩, -⟩
        have hcH : p ≤ (⌈1 / H⌉₊ : ℝ) * (H * p) := by
          have := Nat.le_ceil (1 / H)
          have h1 : 1 ≤ (⌈1 / H⌉₊ : ℝ) * H := by rwa [div_le_iff₀ hH] at this
          nlinarith
        have a1 := Int.floor_le (D.y l 0 / p); have a2 := Int.lt_floor_add_one (D.y l 0 / p)
        rw [hc1, le_div_iff₀ hp] at a1; rw [hc1, div_lt_iff₀ hp] at a2
        have b1 := Int.floor_le (D.y l 1 / p); have b2 := Int.lt_floor_add_one (D.y l 1 / p)
        rw [hl.2.2, le_div_iff₀ hp] at b1; rw [hl.2.2, div_lt_iff₀ hp] at b2
        set Lv := (D.S l (tI + H * u) - b * H) / H + phiR D tI H tS 1 u * (c * p) with hLv
        have d1 := Int.floor_le (Lv / p); have d2 := Int.lt_floor_add_one (Lv / p)
        rw [hc2, le_div_iff₀ hp] at d1; rw [hc2, div_lt_iff₀ hp] at d2
        have hSL : D.S l (tI + H * u) = H * Lv + b * H - H * phiR D tI H tS 1 u * (c * p) := by
          rw [hLv]; field_simp; ring
        refine ⟨hEsub hlu, a1, by linarith, b1, by linarith, ?_, ?_⟩
        · rw [hSL]; push_cast; nlinarith
        · rw [hSL]; push_cast; nlinarith)
    calc ENNReal.ofReal (1 / (H ^ d * p)) * D.ν ({l | (l, u) ∈ {q : Ω × ℝ | q.1 ∈ g ∧
          (q.1, tI + H * q.2) ∈ E ∧ q.2 ∈ Icc (0:ℝ) 1} ∧ ⌊D.y l 0 / p⌋ = c₁ ∧
          ⌊((D.S l (tI + H * u) - b * H) / H + phiR D tI H tS 1 u * (c * p)) / p⌋ = c₂} ∩ g)
        ≤ ENNReal.ofReal (1 / (H ^ d * p)) * ((((⌈1 / H⌉₊ + 1) * (⌈1 / H⌉₊ + 1) *
            (1 + 2 * ⌈2 * K⌉₊ + 1) : ℕ) : ENNReal) * ENNReal.ofReal (K * (H * p) ^ (2 + d))) := by
          gcongr
      _ = ENNReal.ofReal ((1 / (H ^ d * p)) * (((⌈1 / H⌉₊ + 1) * (⌈1 / H⌉₊ + 1) *
            (1 + 2 * ⌈2 * K⌉₊ + 1) : ℕ) * (K * (H * p) ^ (2 + d)))) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Ks * p ^ (1 + d)) :=
          ENNReal.ofReal_le_ofReal ((cap_arith hK hH hH1 hp).trans (by
            have := Real.rpow_pos_of_pos hp (1 + d)
            nlinarith))

end Block

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
