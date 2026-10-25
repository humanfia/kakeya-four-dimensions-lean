import Submission.Obl.k4_row_cell_regularization.Assembly
import Submission.Obl.k4_row_cell_regularization.Levels
import Submission.Obl.k4_row_cell_regularization.LossBounds

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace Submission.Obl.k4_row_cell_regularization

variable {α : Type} [MeasurableSpace α]
variable {ν : Measure α} {μ : Measure (α × ℝ)} {b v H : α → ℝ}
    {T : α × ℝ → Fin 2 → ℝ} {π : Measure ℝ} {E : ℝ}
    {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)} {h L S : ℝ}

/-- The original law, one comparable palette level, and the numerical budget together give
all the original measurable cell data. -/
theorem IncHyp.regularize (hyp : IncHyp ν μ b v H T π E F h L S)
    (J : ℕ) (R : ℝ) (hJ : 0 < J) (hL128 : 128 ≤ L) (hS : 0 < S)
    (hR : 2 ≤ R) (hRh : h ≤ 2 / R)
    (hlow : 128 * L ^ 5 ≤ h * L ^ J)
    (hsep : 512 * (J : ℝ) * L ^ 6 * lossK J L ^ 3 * 2 ^ S ≤ R ^ S) :
    let K := lossK J L
    ∃ (P : Finset Point) (D : Finset ℤ) (u : ℤ → ℝ) (c : Point → ℤ → ℝ) (C : Point → Set (α × ℝ)),
      (μ ≤ ENNReal.ofReal K • (ν.prod volume)) ∧
      (∀ p d, 0 ≤ c p d) ∧ ((P.card : ℝ) ≤ K / h ^ 2) ∧
      (∀ p ∈ P, ∀ d ∈ D, c p d ≤ K * h ^ 2 / (D.card : ℝ)) ∧
      (1 / K ≤ ∑ p ∈ P, ∑ d ∈ D, c p d) ∧
      (∀ d ∈ D, |u d| ≤ K) ∧
      (∀ p ∈ P, ∀ j : Fin 4, |h * (p j : ℝ)| ≤ K) ∧
      (∀ q : ℤ × ℤ, ((P.filter (fun p => (p 0, p 1) = q)).card : ℝ) ≤ K) ∧
      (∀ d ∈ D, (((P.filter (fun p => 0 < c p d)).image
        (fun p => (⌊(p 1 : ℝ) - u d * (p 0 : ℝ)⌋,
          ⌊(p 2 : ℝ) + u d * (p 3 : ℝ)⌋))).card : ℝ) ≤ K / h) ∧
      (∀ x r : ℝ, h ≤ r → r ≤ 1 →
        ((D.filter (fun d => u d ∈ Icc x (x + r))).card : ℝ) ≤
          K * r ^ (S / 4) * (D.card : ℝ)) ∧
      (∀ d₀ ∈ D, ((D.filter (fun d => |u d - u d₀| < 1 / R)).card : ℝ) ≤
        (D.card : ℝ) / (16 * K ^ 3)) ∧
      (∀ p, MeasurableSet (C p)) ∧
      Pairwise (fun p q => Disjoint (C p) (C q)) ∧
      (∀ p ∈ P, ENNReal.ofReal (∑ d ∈ D, c p d) ≤ μ (C p)) ∧
      (∀ p ∈ P, ∀ x ∈ C p,
        |trajPos b v x 0| ≤ 1 ∧ |trajPos b v x 1| ≤ K ∧ ∀ j, |T x j| ≤ K) ∧
      (∀ p ∈ P, ∀ x ∈ C p, ∀ j : Fin 2,
        |trajPos b v x j - h * ((![p 0, p 1] : Fin 2 → ℤ) j : ℝ)| ≤ h) ∧
      (∀ p ∈ P, ∀ x ∈ C p, ∀ j : Fin 2,
        |(h / E) * T x j - h * ((![p 2, p 3] : Fin 2 → ℤ) j : ℝ)| ≤ h) := by
  dsimp only
  let K := lossK J L
  let P := incPoints h E L F
  let B := incBins h L
  let m := originalMass μ h E L b v H T F
  let w := binWeight π h
  have hL : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hh := hyp.h_pos
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hK1 : 1 ≤ K := one_le_lossK hJ hL
  have hKpos : 0 < K := by linarith
  have hπ := hyp.prob_π
  have hP : (P.card : ℝ) ≤ 8 * L ^ 2 / h ^ 2 :=
    incPoints_card hh hyp.h_lt_one.le hL hyp.bins_card
  have hB : (B.card : ℝ) ≤ 4 * L / h := incBins_card hh hyp.h_lt_one.le hL
  have htail : (B.card : ℝ) * (P.card : ℝ) * (L * h ^ 2) * (L ^ J)⁻¹ ≤
      (1 / (2 * L)) / 2 := by
    calc
      _ ≤ (4 * L / h) * (8 * L ^ 2 / h ^ 2) * (L * h ^ 2) * (L ^ J)⁻¹ := by
        gcongr
      _ = 32 * L ^ 4 / (h * L ^ J) := by field_simp <;> ring
      _ ≤ 1 / (4 * L) := by
        apply (div_le_div_iff₀ (by positivity : 0 < h * L ^ J)
          (by positivity : 0 < 4 * L)).mpr
        convert hlow using 1 <;> ring
      _ = (1 / (2 * L)) / 2 := by ring
  have hw1 : ∀ d ∈ B, w d ≤ 1 := by
    intro d hd
    exact (Finset.single_le_sum (fun d _ => binWeight_nonneg π h d) hd).trans
      (sum_binWeight_le_one hh π B)
  obtain ⟨D, hDB, θ, hθ, hlev, hmass⟩ := exists_weight_level B P m w J hJ
    (by positivity : 0 ≤ L * h ^ 2) (by linarith) hw1
    (fun p _ d _ => hyp.originalMass_upper p d) hyp.originalMass_total htail
  have heM : (1 / (2 * L)) / (2 * (J : ℝ)) = 1 / (4 * L * (J : ℝ)) := by
    field_simp <;> ring
  rw [heM] at hmass
  have hMpos : 0 < 1 / (4 * L * (J : ℝ)) := by positivity
  obtain ⟨hmu, hcount⟩ := level_caps D P m w (binVel h) hθ hlev
    (sum_binWeight_le_one hh π D) (hyp.binWeight_cap D)
    (fun p _ d _ => hyp.originalMass_upper p d) (by positivity : 0 ≤ L * h ^ 2)
    hP hMpos hmass
  have heC : L * (8 * L ^ 2 / h ^ 2) * (L * h ^ 2) * L /
      (1 / (4 * L * (J : ℝ))) = 32 * (J : ℝ) * L ^ 6 := by
    field_simp <;> ring
  rw [heC] at hcount
  obtain ⟨hLK, hpoints, hproj, hmassK, hL2K, hcapK⟩ := lossK_bounds hJ hL
  have hmuK : ∀ p ∈ P, ∀ d ∈ D, m p d ≤ K * h ^ 2 / (D.card : ℝ) := by
    intro p hp d hd
    calc
      _ ≤ (L * h ^ 2) * L / (D.card : ℝ) := hmu p hp d hd
      _ = L ^ 2 * h ^ 2 / (D.card : ℝ) := by ring
      _ ≤ K * h ^ 2 / (D.card : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_right hL2K (sq_nonneg h)
  have hmTK : 1 / K ≤ ∑ p ∈ P, ∑ d ∈ D, m p d :=
    (one_div_le_one_div_of_le (by positivity : 0 < 4 * L * (J : ℝ))
      hmassK).trans hmass
  have hcap : ∀ x r : ℝ, h ≤ r → r ≤ 1 →
      ((D.filter (fun d => binVel h d ∈ Icc x (x + r))).card : ℝ) ≤
        K * r ^ (S / 4) * (D.card : ℝ) := by
    intro x r hr hr1
    have hr0 : 0 < r := hh.trans_le hr
    have hp : r ^ S ≤ r ^ (S / 4) :=
      Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
    exact (hcount x r hr hr1).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul hcapK hp (Real.rpow_nonneg hr0.le _) hKpos.le) (Nat.cast_nonneg _))
  have hRpos : 0 < R := by linarith
  have hRS : 0 < R ^ S := Real.rpow_pos_of_pos hRpos S
  have hnearCoeff : (32 * (J : ℝ) * L ^ 6) * (2 / R) ^ S ≤ 1 / (16 * K ^ 3) := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hRpos.le, ← mul_div_assoc]
    apply (div_le_div_iff₀ hRS (by positivity : 0 < 16 * K ^ 3)).mpr
    convert hsep using 1 <;> ring
  have hnear : ∀ d₀ ∈ D,
      ((D.filter (fun d => |binVel h d - binVel h d₀| < 1 / R)).card : ℝ) ≤
        (D.card : ℝ) / (16 * K ^ 3) := by
    intro d₀ hd₀
    calc
      _ ≤ (32 * (J : ℝ) * L ^ 6) * (2 / R) ^ S * (D.card : ℝ) :=
        near_cap_of_interval_cap D (binVel h) hcount hR hRh d₀ hd₀
      _ ≤ (1 / (16 * K ^ 3)) * (D.card : ℝ) :=
        mul_le_mul_of_nonneg_right hnearCoeff (Nat.cast_nonneg _)
      _ = (D.card : ℝ) / (16 * K ^ 3) := by ring
  obtain ⟨P₁, u, c, C, hfields⟩ := hyp.assemble K R D hDB hLK hpoints hproj hmuK hmTK hcap hnear
  exact ⟨P₁, D, u, c, C, hfields⟩

end Submission.Obl.k4_row_cell_regularization
