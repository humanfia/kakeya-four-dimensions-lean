import Submission.Obl.k4_scalar_grid_cartesian_field.ActiveCodes
import Submission.Obl.k4_scalar_grid_density_extension.GridRelation
import Submission.Lib.K4QuadraticSublevel

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory

/-- A physical interval has a finite list of shifted fine bins, uniformly in its location. -/
theorem interval_refinement_bins {b a : ℝ} (hb : 0 < b) (ha : 0 < a)
    (origin : ℝ) (q : ℤ) :
    ∃ D : Finset ℤ, (D.card : ℝ) ≤ 2 * b / a + 2 ∧
      ∀ x : ℝ, (⌊x / b⌋ : ℤ) = q → (⌊(x - origin) / a⌋ : ℤ) ∈ D := by
  let I := Icc (b * (q : ℝ)) (b * ((q : ℝ) + 1))
  have hdiam : ∀ x ∈ I, ∀ y ∈ I, dist x y ≤ b := by
    intro x hx y hy
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  obtain ⟨hfin, hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    I hb.le ha origin hdiam
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · simpa only [Set.ncard_eq_toFinset_card _ hfin] using hcard
  · intro x hx
    apply hfin.mem_toFinset.mpr
    refine ⟨x, ?_, rfl⟩
    have hlo := Int.floor_le (x / b)
    have hhi := Int.lt_floor_add_one (x / b)
    rw [hx] at hlo hhi
    constructor
    · nlinarith [(le_div_iff₀ hb).mp hlo]
    · nlinarith [(div_lt_iff₀ hb).mp hhi]

/-- Coarsening each physical coordinate costs at most two labels, even on unaligned grids. -/
theorem physical_code_coarsening_count {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (z : Ω → Fin n → ℝ) {b w : ℝ} (hb : 0 < b) (hbw : b ≤ w)
    (hfinite : (activeCodes μ (fun p e => (⌊z p e / b⌋ : ℤ))).Finite) :
    (activeCodes μ (fun p e => (⌊z p e / w⌋ : ℤ))).Finite ∧
      ((activeCodes μ (fun p e => (⌊z p e / w⌋ : ℤ))).ncard : ℝ) ≤
        (2 : ℝ) ^ n * ((activeCodes μ (fun p e => (⌊z p e / b⌋ : ℤ))).ncard : ℝ) := by
  classical
  let D : (Fin n → ℤ) → Finset (Fin n → ℤ) := fun q => Fintype.piFinset
    (fun e => {⌊(q e : ℝ) * b / w⌋, ⌊(q e : ℝ) * b / w⌋ + 1})
  have hcard (q : Fin n → ℤ) : ((D q).card : ℝ) ≤ (2 : ℝ) ^ n := by
    have hn : (D q).card ≤ 2 ^ n := by
      dsimp only [D]
      rw [Fintype.card_piFinset]
      calc
        _ ≤ ∏ _e : Fin n, 2 := Finset.prod_le_prod' fun _ _ => Finset.card_le_two
        _ = _ := by simp
    exact_mod_cast hn
  have hdecode (p : Ω) : (fun e => (⌊z p e / w⌋ : ℤ)) ∈ D (fun e => ⌊z p e / b⌋) := by
    simp only [D, Fintype.mem_piFinset]
    intro e
    exact Submission.Obl.k4_scalar_grid_density_extension.floorCompatible_coarse_mem hb hbw
      ⌊z p e / b⌋ ⌊z p e / w⌋ ⟨z p e, rfl, rfl⟩
  exact active_code_count_of_ae_decoder μ (fun p e => ⌊z p e / b⌋)
    (fun p e => ⌊z p e / w⌋) hfinite D (Filter.Eventually.of_forall hdecode)
    (fun q _ => hcard q)

/-- Refine two base coordinates inside each physical cell while coarsening its hidden bin.
The physical mesh may be unaligned with either requested grid. -/
theorem physical_to_normalized_joint_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z : Ω → Fin 2 → ℝ) (x : Ω → ℝ) (origin : Fin 2 → ℝ)
    {b h ξ w : ℝ} (hb : 0 < b) (hh : 0 < h) (hξ : 0 < ξ)
    (hbase : h * ξ ≤ b) (hhidden : b ≤ w)
    (hfinite : (activeCodes μ (fun p (e : Fin 3) =>
      (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / b⌋ : ℤ))).Finite) :
    (activeCodes μ (fun p => ((fun e : Fin 2 => (⌊(z p e - origin e) / h / ξ⌋ : ℤ)),
      (⌊x p / w⌋ : ℤ)))).Finite ∧
    ((activeCodes μ (fun p => ((fun e : Fin 2 => (⌊(z p e - origin e) / h / ξ⌋ : ℤ)),
      (⌊x p / w⌋ : ℤ)))).ncard : ℝ) ≤
      32 * (b / (h * ξ)) ^ 2 * ((activeCodes μ (fun p (e : Fin 3) =>
        (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / b⌋ : ℤ))).ncard : ℝ) := by
  classical
  have ha : 0 < h * ξ := mul_pos hh hξ
  let fine : Ω → Fin 3 → ℤ := fun p e => ⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / b⌋
  let target : Ω → (Fin 2 → ℤ) × ℤ := fun p =>
    ((fun e => ⌊(z p e - origin e) / h / ξ⌋), ⌊x p / w⌋)
  choose D₀ hD₀ hmem₀ using fun q : ℤ => interval_refinement_bins hb ha (origin 0) q
  choose D₁ hD₁ hmem₁ using fun q : ℤ => interval_refinement_bins hb ha (origin 1) q
  let Dh : ℤ → Finset ℤ := fun q => {⌊(q : ℝ) * b / w⌋, ⌊(q : ℝ) * b / w⌋ + 1}
  let decode : (Fin 3 → ℤ) → Finset ((Fin 2 → ℤ) × ℤ) := fun q =>
    ((D₀ (q 0) ×ˢ D₁ (q 1)) ×ˢ Dh (q 2)).image (fun c => (![c.1.1, c.1.2], c.2))
  have hratio : 1 ≤ b / (h * ξ) := (le_div_iff₀ ha).mpr (by simpa using hbase)
  have hbase₀ (q : ℤ) : ((D₀ q).card : ℝ) ≤ 4 * (b / (h * ξ)) := by
    calc
      _ ≤ 2 * b / (h * ξ) + 2 := hD₀ q
      _ = 2 * (b / (h * ξ)) + 2 := by ring
      _ ≤ _ := by linarith
  have hbase₁ (q : ℤ) : ((D₁ q).card : ℝ) ≤ 4 * (b / (h * ξ)) := by
    calc
      _ ≤ 2 * b / (h * ξ) + 2 := hD₁ q
      _ = 2 * (b / (h * ξ)) + 2 := by ring
      _ ≤ _ := by linarith
  have hDh (q : ℤ) : ((Dh q).card : ℝ) ≤ 2 := by
    exact_mod_cast (show (Dh q).card ≤ 2 from Finset.card_le_two)
  have hcard (q : Fin 3 → ℤ) : ((decode q).card : ℝ) ≤ 32 * (b / (h * ξ)) ^ 2 := by
    have hn : (decode q).card ≤ (D₀ (q 0)).card * (D₁ (q 1)).card * (Dh (q 2)).card := by
      apply Finset.card_image_le.trans_eq
      rw [Finset.card_product, Finset.card_product]
    calc
      _ ≤ ((D₀ (q 0)).card : ℝ) * ((D₁ (q 1)).card : ℝ) * ((Dh (q 2)).card : ℝ) := by exact_mod_cast hn
      _ ≤ (4 * (b / (h * ξ))) * (4 * (b / (h * ξ))) * 2 := by
        gcongr
        · exact hbase₀ _
        · exact hbase₁ _
        · exact hDh _
      _ = _ := by ring
  have hdecode : ∀ p, target p ∈ decode (fine p) := by
    intro p
    have h₀ := hmem₀ (fine p 0) (z p 0) (by rfl)
    have h₁ := hmem₁ (fine p 1) (z p 1) (by rfl)
    have hhbin : (⌊x p / w⌋ : ℤ) ∈ Dh (fine p 2) := by
      exact Submission.Obl.k4_scalar_grid_density_extension.floorCompatible_coarse_mem hb hhidden
        (fine p 2) ⌊x p / w⌋ ⟨x p, rfl, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨((⌊(z p 0 - origin 0) / (h * ξ)⌋, ⌊(z p 1 - origin 1) / (h * ξ)⌋),
      ⌊x p / w⌋), Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h₀, h₁⟩, hhbin⟩, ?_⟩
    apply Prod.ext
    · funext e
      fin_cases e <;> simp [target, div_div]
    · rfl
  exact active_code_count_of_ae_decoder μ fine target hfinite decode
    (Filter.Eventually.of_forall hdecode) (fun q _ => hcard q)

end Submission.Obl.k4_scalar_grid_cartesian_field
