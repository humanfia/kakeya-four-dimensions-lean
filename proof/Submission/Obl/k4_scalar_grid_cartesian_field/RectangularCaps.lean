import Submission.Lib.K4ListedExceptions.FrameCodes
import Submission.Lib.K4QuadraticSheets.JetBins

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory
open Submission.Lib.K4ListedExceptions

/-- A finite box of original codes costs only its explicit cardinality in a cell cap. -/
theorem mass_le_of_code_box {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (code : Ω → Fin n → ℤ) (S : Set Ω)
    (C : ℕ) (q : Fin n → ℤ) (B : ENNReal)
    (hcodes : ∀ p ∈ S, code p ∈ integerCodeBox C q)
    (hcap : ∀ c, μ {p | code p = c} ≤ B) :
    μ S ≤ ((2 * C + 1) ^ n : ℕ) * B := by
  classical
  have hsub : S ⊆ ⋃ c ∈ integerCodeBox C q, {p | code p = c} := by
    intro p hp
    exact mem_biUnion (hcodes p hp) rfl
  calc
    μ S ≤ μ (⋃ c ∈ integerCodeBox C q, {p | code p = c}) := measure_mono hsub
    _ ≤ ∑ c ∈ integerCodeBox C q, μ {p | code p = c} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ integerCodeBox C q, B := Finset.sum_le_sum fun c _ => hcap c
    _ = ((2 * C + 1) ^ n : ℕ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul, card_integerCodeBox]

/-- A finite cover by original code cells sums their restricted masses. -/
theorem mass_le_of_finite_code_cover {Ω J : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → J) (S : Set Ω) (F : Finset J) (B : ENNReal)
    (hcover : ∀ p ∈ S, code p ∈ F)
    (hcap : ∀ q ∈ F, μ ({p | code p = q} ∩ S) ≤ B) :
    μ S ≤ (F.card : ENNReal) * B := by
  classical
  calc
    _ ≤ μ (⋃ q ∈ F, {p | code p = q} ∩ S) := by
      apply measure_mono
      intro p hp
      exact mem_biUnion (hcover p hp) ⟨rfl, hp⟩
    _ ≤ ∑ q ∈ F, μ ({p | code p = q} ∩ S) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ F, B := Finset.sum_le_sum hcap
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- A bounded normalized base has an explicit finite count of fine cells. -/
theorem mass_le_of_bounded_base_cell_caps {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z : Ω → Fin 2 → ℝ) (S : Set Ω)
    {K ξ : ℝ} (hK : 1 ≤ K) (hξ : 0 < ξ) (hξone : ξ ≤ 1) (B : ENNReal)
    (hbound : ∀ p ∈ S, ∀ e, |z p e| ≤ 2 * K)
    (hcap : ∀ q : Fin 2 → ℤ,
      μ ({p | (fun e => (⌊z p e / ξ⌋ : ℤ)) = q} ∩ S) ≤ B) :
    μ S ≤ ENNReal.ofReal (49 * K ^ 2 * ξ⁻¹ ^ 2) * B := by
  classical
  let C := ⌈2 * K / ξ⌉₊
  have hC : 2 * K ≤ (C : ℝ) * ξ := by
    exact (div_le_iff₀ hξ).mp (Nat.le_ceil _)
  have hcover : ∀ p ∈ S, (fun e => (⌊z p e / ξ⌋ : ℤ)) ∈ integerCodeBox C (fun _ => 0) := by
    intro p hp
    simpa only [Pi.zero_apply, zero_div, Int.floor_zero] using floor_code_mem_integerCodeBox C (z p) 0 (fun _ => ξ)
      (fun _ => hξ) (fun e => by simpa using (hbound p hp e).trans hC)
  have hnum : (((2 * C + 1) ^ 2 : ℕ) : ℝ) ≤ 49 * K ^ 2 * ξ⁻¹ ^ 2 := by
    have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * K / ξ)).le
    have hratio : 1 ≤ K / ξ := (le_div_iff₀ hξ).mpr (by simpa using hξone.trans hK)
    dsimp [C]
    push_cast
    rw [mul_div_assoc] at hceil ⊢
    calc
      _ ≤ (7 * (K / ξ)) ^ 2 := by gcongr; linarith
      _ = _ := by field_simp <;> norm_num
  calc
    _ ≤ ((integerCodeBox C (fun _ : Fin 2 => 0)).card : ENNReal) * B :=
      mass_le_of_finite_code_cover μ (fun p e => ⌊z p e / ξ⌋) S
        (integerCodeBox C (fun _ => 0)) B hcover (fun q _ => hcap q)
    _ ≤ _ := by
      rw [card_integerCodeBox]
      apply mul_le_mul' _ le_rfl
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hnum

/-- Closeness in physical coordinates transfers the original rectangular caps to
arbitrary shifted or normalized cells. No alignment of the two grids is needed. -/
theorem mass_le_of_rectangular_closeness {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (z : Ω → Fin n → ℝ) (width : Fin n → ℝ)
    (hwidth : ∀ e, 0 < width e) (S : Set Ω) (center : Fin n → ℝ)
    (C : ℕ) (B : ENNReal)
    (hclose : ∀ p ∈ S, ∀ e, |z p e - center e| ≤ (C : ℝ) * width e)
    (hcap : ∀ q, μ {p | (fun e => (⌊z p e / width e⌋ : ℤ)) = q} ≤ B) :
    μ S ≤ ((2 * C + 1) ^ n : ℕ) * B := by
  apply mass_le_of_code_box μ (fun p e => ⌊z p e / width e⌋) S C
    (fun e => ⌊center e / width e⌋) B ?_ hcap
  intro p hp
  exact floor_code_mem_integerCodeBox C (z p) center width hwidth (hclose p hp)

/-- A cell in normalized unsheared base coordinates has the exact physical diameter. -/
theorem normalized_cell_diameter {h ξ : ℝ} (hh : 0 < h) (hξ : 0 < ξ)
    {z z' z₀ : Fin 2 → ℝ}
    (hcell : (fun e => (⌊(z e - z₀ e) / h / ξ⌋ : ℤ)) =
      (fun e => (⌊(z' e - z₀ e) / h / ξ⌋ : ℤ))) :
    ∀ e, |z e - z' e| ≤ h * ξ := by
  intro e
  have hcode := congrFun hcell e
  have hdiff := (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hξ hcode).le
  have hid : (z e - z₀ e) / h - (z' e - z₀ e) / h = (z e - z' e) / h := by ring
  rw [hid, abs_div, abs_of_pos hh] at hdiff
  have := (div_le_iff₀ hh).mp hdiff
  nlinarith

/-- A three-coordinate code is exactly the scalar base code and the hidden code. -/
theorem rectangular_cap_fin_three {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z : Ω → Fin 2 → ℝ) (x : Ω → ℝ)
    (a b : ℝ) (B : ENNReal)
    (hcap : ∀ (q : Fin 2 → ℤ) (c : ℤ),
      μ {p | (fun e => (⌊z p e / a⌋ : ℤ)) = q ∧ (⌊x p / b⌋ : ℤ) = c} ≤ B) :
    ∀ q : Fin 3 → ℤ,
      μ {p | (fun e : Fin 3 => (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e /
        (![a, a, b] : Fin 3 → ℝ) e⌋ : ℤ)) = q} ≤ B := by
  intro q
  apply (measure_mono (t := {p | (fun e => (⌊z p e / a⌋ : ℤ)) = ![q 0, q 1] ∧
    (⌊x p / b⌋ : ℤ) = q 2}) ?_).trans (hcap _ _)
  intro p hp
  constructor
  · funext e
    fin_cases e
    · simpa using congrFun hp 0
    · simpa using congrFun hp 1
  · simpa using congrFun hp 2

/-- A normalized base cell meeting a fitted graph inherits an original rectangular cap.
The graph error and its within-cell oscillation are charged in the original hidden bins. -/
theorem normalized_graph_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (ρ μ : Measure Ω) (hμ : μ ≤ ρ) (z : Ω → Fin 2 → ℝ) (x : Ω → ℝ)
    (S : Set Ω) (hsupport : μ Sᶜ = 0) (f : (Fin 2 → ℝ) → ℝ)
    {h ξ δ α K : ℝ} (hh : 0 < h) (hξ : 0 < ξ) (hδ : 0 < δ)
    (hα : 0 < α)
    (z₀ : Fin 2 → ℝ) (C : ℕ) (hwidth : h * ξ ≤ (C : ℝ) * α)
    (hKC : 2 * K + 1 ≤ C)
    (B : ENNReal)
    (hcap : ∀ (q : Fin 2 → ℤ) (c : ℤ),
      ρ {p | (fun e => (⌊z p e / α⌋ : ℤ)) = q ∧ (⌊x p / δ⌋ : ℤ) = c} ≤ B)
    (hfit : ∀ p ∈ S, |x p - f (z p)| ≤ K * δ)
    (hvar : ∀ p ∈ S, ∀ p' ∈ S,
      (fun e => (⌊(z p e - z₀ e) / h / ξ⌋ : ℤ)) =
        (fun e => (⌊(z p' e - z₀ e) / h / ξ⌋ : ℤ)) →
      |f (z p) - f (z p')| ≤ δ) :
    ∀ q : Fin 2 → ℤ,
      μ {p | (fun e => (⌊(z p e - z₀ e) / h / ξ⌋ : ℤ)) = q} ≤
        ((2 * C + 1) ^ 3 : ℕ) * B := by
  intro q
  let U := {p | (fun e => (⌊(z p e - z₀ e) / h / ξ⌋ : ℤ)) = q}
  have hred : μ U ≤ ρ (U ∩ S) := by
    rw [← measure_inter_conull hsupport (s := U)]
    exact hμ _
  apply hred.trans
  rcases (U ∩ S).eq_empty_or_nonempty with hempty | ⟨p₀, hp₀U, hp₀S⟩
  · rw [hempty, measure_empty]
    exact bot_le
  apply mass_le_of_rectangular_closeness ρ
    (fun p => ![z p 0, z p 1, x p]) ![α, α, δ]
    (by intro e; fin_cases e <;> simp [hα, hδ])
    (U ∩ S) ![z p₀ 0, z p₀ 1, x p₀] C B ?_
    (rectangular_cap_fin_three ρ z x α δ B hcap)
  intro p hp e
  have hcell : (fun e => (⌊(z p e - z₀ e) / h / ξ⌋ : ℤ)) =
      (fun e => (⌊(z p₀ e - z₀ e) / h / ξ⌋ : ℤ)) := hp.1.trans hp₀U.symm
  have hbase := normalized_cell_diameter hh hξ hcell
  fin_cases e
  · change |z p 0 - z p₀ 0| ≤ (C : ℝ) * α
    exact (hbase 0).trans hwidth
  · change |z p 1 - z p₀ 1| ≤ (C : ℝ) * α
    exact (hbase 1).trans hwidth
  · change |x p - x p₀| ≤ (C : ℝ) * δ
    calc
      |x p - x p₀| = |(x p - f (z p)) + (f (z p) - f (z p₀)) +
          (f (z p₀) - x p₀)| := by ring_nf
      _ ≤ |x p - f (z p)| + |f (z p) - f (z p₀)| + |f (z p₀) - x p₀| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ K * δ + δ + K * δ := by
        rw [abs_sub_comm (f (z p₀)) (x p₀)]
        exact add_le_add (add_le_add (hfit p hp.2) (hvar p hp.2 p₀ hp₀S hcell))
          (hfit p₀ hp₀S)
      _ ≤ (C : ℝ) * δ := by nlinarith

/-- Calibrate a base ceiling to the full, unchanged trajectory mass of the packet. -/
theorem normalized_cap_calibration {K h ξ a : ℝ} (hK : 0 < K)
    (hh : 0 ≤ h) (m : ENNReal)
    (hfloor : ENNReal.ofReal (a * h / K) ≤ m) :
    ENNReal.ofReal (K * (h * ξ) ^ 2 * a) ≤
      ENNReal.ofReal (K ^ 2 * h * ξ ^ 2) * m := by
  calc
    _ = ENNReal.ofReal (K ^ 2 * h * ξ ^ 2) * ENNReal.ofReal (a * h / K) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ K ^ 2 * h * ξ ^ 2)]
      congr 1
      field_simp
    _ ≤ _ := mul_le_mul' le_rfl hfloor

end Submission.Obl.k4_scalar_grid_cartesian_field
