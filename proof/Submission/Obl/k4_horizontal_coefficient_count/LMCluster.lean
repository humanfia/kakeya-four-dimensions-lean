import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Obl.k4_horizontal_coefficient_count.LMBand
import Submission.Obl.k4_horizontal_coefficient_count.DepthBasics

/-!
# Light coefficient cells carry little mass (one index, one depth)

Paper, Lemma `a06:horizontal-coefficient-count`, "From support to heavy
coefficient bins".  Fix a group `g`.  Normalize the current marginal on the
light part of the group by `W_g = a² π(d₀)`.  The band cap is the Frostman
bound of scalar clustering, and the support count is its support hypothesis.
If the light part, restricted to labels with incidence time at least `θ`, had
normalized product mass at least `Λ⁻¹`, scalar clustering would produce a
coefficient bin of mass `≥ a^d σ`, larger than the lightness threshold
`a^d / Z`: a contradiction.  Labels with incidence time below `θ` carry at
most `K θ ν(g)` by the prior domination.  Summing over the groups gives
`ρ(light) ≤ 16 K² / (Λ θ) + K θ`.
-/

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The five-coordinate code of a coefficient vector; definitionally the same
as `horizontalCode χ a`. -/
def lmCode (χ a : ℝ) (β : Fin 6 → ℝ) : Fin 5 → ℤ :=
  ![⌊β 3 / χ⌋, ⌊β 0 / a⌋, ⌊β 1 / a⌋, ⌊β 2 / a⌋, ⌊β 5 / a⌋]

variable {α : Type} [MeasurableSpace α]

/-- The labels of `G` with a given code. -/
def lmCell (b : α → Fin 6 → ℝ) (χ a : ℝ) (G : Set α) (c : Fin 5 → ℤ) : Set α :=
  G ∩ {l | lmCode χ a (b l) = c}

/-- The palette-weighted floor of a code. -/
def lmWeight (π : Measure ℝ) (χ a d Z : ℝ) (c : Fin 5 → ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (a ^ 2 * a ^ d / Z) * π (Ico ((c 0 : ℝ) * χ) (((c 0 : ℝ) + 1) * χ))

/-- Labels of `G` whose code cell is light for the current law `ρ`. -/
def lmLight (ρ : Measure (α × ℝ)) (π : Measure ℝ) (b : α → Fin 6 → ℝ) (χ a d Z : ℝ)
    (G : Set α) : Set α :=
  {l | l ∈ G ∧ ρ (lmCell b χ a G (lmCode χ a (b l)) ×ˢ univ) <
    lmWeight π χ a d Z (lmCode χ a (b l))}

/-- Scalar coefficient clustering (accepted `o016`, from `o002`) at one value of
`N`, with `a = N^(-c)`, `Λ = N^η`, `σ = N^(-ε)`. -/
def ClusterOracle (a d Λ σ : ℝ) : Prop :=
  ∀ (β : Type) [MeasurableSpace β] (ν : Measure β) (f : β → EuclideanSpace ℝ (Fin 3))
    (E : Set (β × ℝ)) (F : Finset (ℤ × ℤ)),
    Measurable f → MeasurableSet E → E ⊆ univ ×ˢ Icc (0 : ℝ) 1 → (∀ l, ‖f l‖ ≤ Λ) →
    ν univ ≤ ENNReal.ofReal Λ → ENNReal.ofReal Λ⁻¹ ≤ (ν.prod volume) E →
    (F.card : ℝ) ≤ Λ * a ^ (-1 - d) →
    (∀ l t, (l, t) ∈ E → (⌊t / a⌋, ⌊(f l 0 + t * f l 1 + t ^ 2 * f l 2) / a⌋) ∈ F) →
    (∀ (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ), a ≤ r →
      ν {l | f l ∈ Metric.ball c r} ≤ ENNReal.ofReal (Λ * r ^ d)) →
    ∃ qq : Fin 3 → ℤ, ENNReal.ofReal (a ^ d * σ) ≤
      ν {l | (∀ i : Fin 3, ⌊f l i / a⌋ = qq i) ∧ ENNReal.ofReal σ ≤ volume {t | (l, t) ∈ E}}

theorem measurable_lmCode {b : α → Fin 6 → ℝ} (hb : Measurable b) (χ a : ℝ) :
    Measurable (fun l => lmCode χ a (b l)) := by
  apply Measurable.of_eval
  intro i
  have hc : ∀ e : Fin 6, Measurable fun l => b l e := fun e => (measurable_pi_apply e).comp hb
  fin_cases i
  · exact Int.measurable_floor.comp ((hc 3).div_const χ)
  · exact Int.measurable_floor.comp ((hc 0).div_const a)
  · exact Int.measurable_floor.comp ((hc 1).div_const a)
  · exact Int.measurable_floor.comp ((hc 2).div_const a)
  · exact Int.measurable_floor.comp ((hc 5).div_const a)

theorem measurableSet_codes (S : Set (Fin 5 → ℤ)) : MeasurableSet S :=
  (Set.to_countable S).measurableSet

theorem measurableSet_lmCell {b : α → Fin 6 → ℝ} (hb : Measurable b) (χ a : ℝ) {G : Set α}
    (hG : MeasurableSet G) (c : Fin 5 → ℤ) : MeasurableSet (lmCell b χ a G c) :=
  hG.inter ((measurable_lmCode hb χ a) (measurableSet_singleton c))

theorem measurableSet_lmLight (ρ : Measure (α × ℝ)) (π : Measure ℝ) {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (χ a d Z : ℝ) {G : Set α} (hG : MeasurableSet G) :
    MeasurableSet (lmLight ρ π b χ a d Z G) := by
  have : lmLight ρ π b χ a d Z G = G ∩ (fun l => lmCode χ a (b l)) ⁻¹'
      {c | ρ (lmCell b χ a G c ×ˢ univ) < lmWeight π χ a d Z c} := by
    ext l; simp [lmLight]
  rw [this]
  exact hG.inter ((measurable_lmCode hb χ a) (measurableSet_codes _))

theorem bin_eq_Ico {χ : ℝ} (hχ : 0 < χ) (v : ℤ) :
    {x : ℝ | ⌊x / χ⌋ = v} = Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ) := by
  ext x
  simp only [mem_setOf_eq, mem_Ico, Int.floor_eq_iff, le_div_iff₀ hχ, div_lt_iff₀ hχ]

theorem abs_apply_le_norm3 (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have h : ∀ j, ‖x j‖ ^ 2 = x j ^ 2 := fun j => by rw [Real.norm_eq_abs, sq_abs]
  calc x i ^ 2 = ‖x i‖ ^ 2 := (h i).symm
    _ ≤ ∑ j, ‖x j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)

namespace DepthData.Hyp

variable {H : DepthData α}

theorem K_pos (hH : H.Hyp) : 0 < H.K := lt_of_lt_of_le one_pos hH.hK

end DepthData.Hyp

/-- The numerical band constant. -/
theorem band_const_le {K a x R : ℝ} (hK : 1 ≤ K) (ha : 0 < a) (ha1 : a ≤ 1) (hx0 : 0 ≤ x)
    (hx : x ≤ 13 * K) (hR : 0 ≤ R) :
    (1 / a + 1) * (2 * K + 7) * (2 * K + 9) * x * (K * a ^ 3 * R) ≤
      2574 * K ^ 4 * a ^ 2 * R := by
  have e1 : (1 / a + 1) * a ^ 3 ≤ 2 * a ^ 2 := by
    have : (1 / a + 1) * a ^ 3 = a ^ 2 + a ^ 3 := by field_simp
    rw [this]
    nlinarith
  have e2 : (2 * K + 7) * (2 * K + 9) * x * K ≤ 9 * K * (11 * K) * (13 * K) * K := by
    have h7 : 2 * K + 7 ≤ 9 * K := by linarith
    have h9 : 2 * K + 9 ≤ 11 * K := by linarith
    have hK0 : 0 ≤ K := by linarith
    gcongr
  have hK0 : 0 ≤ K := by linarith
  calc (1 / a + 1) * (2 * K + 7) * (2 * K + 9) * x * (K * a ^ 3 * R)
      = ((1 / a + 1) * a ^ 3) * ((2 * K + 7) * (2 * K + 9) * x * K) * R := by ring
    _ ≤ (2 * a ^ 2) * (9 * K * (11 * K) * (13 * K) * K) * R := by
        have : 0 ≤ (2 * K + 7) * (2 * K + 9) * x * K := by positivity
        gcongr
    _ = 2574 * K ^ 4 * a ^ 2 * R := by ring

/-- Total cap of a group. -/
theorem group_total_cap (H : DepthData α) (hH : H.Hyp) (g : ℤ × ℤ × ℤ) (S : Set α)
    (hS : S ⊆ groupSet H.b H.χ H.a g ∩ goodSet H.b H.K H.χ) :
    H.μ (S ×ˢ univ) ≤ ENNReal.ofReal (2574 * H.K ^ 4 * H.a ^ 2) *
      H.π {x | ⌊x / H.χ⌋ = g.1} := by
  have hK := hH.hK
  have h := band_cap H hH g S hS (fun _ => 0) H.K 1 hH.a_le_one le_rfl (by linarith)
    (by
      intro l hl t ht
      obtain ⟨-, -, -, h2, h25⟩ := hS hl
      simp only [X3, sub_zero]
      have : H.b l 2 + t * H.b l 5 = (1 - t) * H.b l 2 + t * (H.b l 2 + H.b l 5) := by ring
      rw [this]
      calc |(1 - t) * H.b l 2 + t * (H.b l 2 + H.b l 5)|
          ≤ |(1 - t) * H.b l 2| + |t * (H.b l 2 + H.b l 5)| := abs_add_le _ _
        _ = (1 - t) * |H.b l 2| + t * |H.b l 2 + H.b l 5| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t),
              abs_of_nonneg ht.1]
        _ ≤ (1 - t) * H.K + t * H.K := by
            gcongr
            · linarith [ht.2]
            · exact ht.1
        _ = H.K := by ring)
  refine h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  rw [Real.one_rpow, div_one]
  have := band_const_le (K := H.K) (a := H.a) (x := 2 * H.K + 3) (R := 1) hK hH.ha0
    hH.a_le_one (by linarith) (by linarith) zero_le_one
  linarith

/-- Box cap of a group: scalar coefficients in a box of radius `r`. -/
theorem group_box_cap (H : DepthData α) (hH : H.Hyp) (g : ℤ × ℤ × ℤ) (c0 c1 r : ℝ)
    (hr : H.a ≤ r) (hr1 : r ≤ 1) :
    H.μ ({l | l ∈ groupSet H.b H.χ H.a g ∩ goodSet H.b H.K H.χ ∧
        |H.b l 2 - c0| < r ∧ |H.b l 5 - c1| < r} ×ˢ univ) ≤
      ENNReal.ofReal (2574 * H.K ^ 4 * H.a ^ 2 * r ^ H.d) * H.π {x | ⌊x / H.χ⌋ = g.1} := by
  set S := {l | l ∈ groupSet H.b H.χ H.a g ∩ goodSet H.b H.K H.χ ∧
        |H.b l 2 - c0| < r ∧ |H.b l 5 - c1| < r} with hSdef
  have hK := hH.hK
  have ha := hH.ha0
  rcases S.eq_empty_or_nonempty with hS0 | ⟨l0, hl0⟩
  · rw [hS0, empty_prod, measure_empty]; exact bot_le
  -- the center velocity coefficient is bounded
  have hc1 : |c1| ≤ 2 * H.K + 1 := by
    obtain ⟨⟨-, h0, -, h2, h25⟩, -, h5⟩ := hl0
    have hb5 : |H.b l0 5| ≤ 2 * H.K := by
      have : H.b l0 5 = (H.b l0 2 + H.b l0 5) - H.b l0 2 := by ring
      rw [this]
      linarith [abs_sub (H.b l0 2 + H.b l0 5) (H.b l0 2)]
    have : c1 = H.b l0 5 - (H.b l0 5 - c1) := by ring
    rw [this]
    linarith [abs_sub (H.b l0 5) (H.b l0 5 - c1), hr1]
  have hr0 : 0 < r := ha.trans_le hr
  have h := band_cap H hH g S (fun l hl => hl.1) (fun n0 => c0 + ((n0 : ℝ) * H.a) * c1)
    ((2 * H.K + 3) * r) r hr hr1 (mul_nonneg (by linarith) hr0.le)
    (by
      intro l hl t ht
      obtain ⟨-, h2, h5⟩ := hl
      have htt := floor_eq_bounds ha (rfl : ⌊t / H.a⌋ = ⌊t / H.a⌋)
      set n0 := ⌊t / H.a⌋
      have hid : X3 (H.b l) t - (c0 + ((n0 : ℝ) * H.a) * c1) =
          (H.b l 2 - c0) + t * (H.b l 5 - c1) + (t - (n0 : ℝ) * H.a) * c1 := by
        simp only [X3]; ring
      rw [hid]
      have e2 : |t * (H.b l 5 - c1)| ≤ r := by
        rw [abs_mul, abs_of_nonneg ht.1]
        calc t * |H.b l 5 - c1| ≤ 1 * r := mul_le_mul ht.2 h5.le (abs_nonneg _) zero_le_one
          _ = r := one_mul r
      have e3 : |(t - (n0 : ℝ) * H.a) * c1| ≤ H.a * (2 * H.K + 1) := by
        rw [abs_mul]
        have : |t - (n0 : ℝ) * H.a| ≤ H.a := by rw [abs_le]; constructor <;> linarith
        exact mul_le_mul this hc1 (abs_nonneg _) ha.le
      calc _ ≤ |H.b l 2 - c0| + |t * (H.b l 5 - c1)| + |(t - (n0 : ℝ) * H.a) * c1| :=
            abs_add_three _ _ _
        _ ≤ r + r + H.a * (2 * H.K + 1) := by linarith
        _ ≤ (2 * H.K + 3) * r := by nlinarith)
  refine h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  rw [mul_div_assoc, div_self hr0.ne', mul_one]
  have := band_const_le (K := H.K) (a := H.a) (x := 2 * (2 * H.K + 3) + 3) (R := r ^ H.d)
    hK ha hH.a_le_one (by linarith) (by linarith) (by positivity)
  linarith

end

end Submission.Obl.k4_horizontal_coefficient_count
