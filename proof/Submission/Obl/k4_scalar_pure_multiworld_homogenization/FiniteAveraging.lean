import Submission.Obl.k4_scalar_pure_multiworld_homogenization.PolynomialAveraging
import Submission.Obl.k4_native_base_flattening.FiniteAveraging
import Submission.Obl.k4_native_base_flattening.Powers

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction

theorem finite_scalar_flattening {m : ℕ} (T : ℝ) (hT : 1 ≤ T) (D : ℕ)
    (hm : (m : ℝ) ≤ T) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ T)
    (A : Fin m → Set (Fin 5 → ℝ)) (B : Fin m → Set (Fin 6 → ℝ))
    (hA : ∀ j, Format 5 T D (A j)) (hB : ∀ j, Format 6 T D (B j))
    (hsA : ∀ j a, a ∈ A j → ∀ i, |a i| ≤ T)
    (hsB : ∀ j a, a ∈ B j → a 5 ∈ Icc (0 : ℝ) 1)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ g : (Fin 6 → ℝ) → ℝ, Measurable g ∧
      (∀ z, 0 ≤ g z ∧ g z ≤ T ^ 2) ∧
      (∀ z z', (∀ i ∉ ([0, 1] : List (Fin 6)), z i = z' i) →
        (∀ i ∈ ([0, 1] : List (Fin 6)), ⌊z i / ρ⌋ = ⌊z' i / ρ⌋) → g z = g z') ∧
      supportedInCube g (3 * T + 2 * ρ) ∧
      densityL1Distance volume g (fun z => ∑ j, scalarComponentDensity (c j) (A j) (B j) z) ≤
        ENNReal.ofReal (746496 * (D : ℝ) * T ^ 8 * ρ) := by
  classical
  let e : ℝ := 96 * T ^ 2 * (D : ℝ) * ρ * (6 * T) ^ 5
  have he₀ : 0 ≤ e := by dsimp [e]; positivity
  have hcomp (j : Fin m) : ∃ g : (Fin 6 → ℝ) → ℝ,
      Measurable (scalarComponentDensity (c j) (A j) (B j)) ∧
      Measurable g ∧ (∀ z, 0 ≤ g z ∧ g z ≤ c j) ∧
      (∀ z z', (∀ i ∉ ([0, 1] : List (Fin 6)), z i = z' i) →
        (∀ i ∈ ([0, 1] : List (Fin 6)), ⌊z i / ρ⌋ = ⌊z' i / ρ⌋) → g z = g z') ∧
      supportedInCube g (3 * T + 2 * ρ) ∧
      densityL1Distance volume g (scalarComponentDensity (c j) (A j) (B j)) ≤
        ENNReal.ofReal e := by
    obtain ⟨g, hg, hgb, _, hcell, hs, he⟩ :=
      scalar_component_flattening (c j) T (hc j).1 hT D (A j) (B j)
        (hA j) (hB j) (hsA j) (hsB j) hρ
    refine ⟨g, measurable_scalarComponentDensity _
      (Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format.measurable (hA j))
      (Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format.measurable (hB j)),
      hg, hgb, hcell, hs, he.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    calc
      _ ≤ 96 * T * T * (D : ℝ) * ρ * (6 * T) ^ 5 := by gcongr; exact (hc j).2
      _ = e := by dsimp [e]; ring
  choose g hf hg hgb hcell hs he using hcomp
  refine ⟨fun z => ∑ j, g j z, Finset.measurable_sum _ (fun j _ => hg j), ?_, ?_, ?_, ?_⟩
  · intro z
    refine ⟨Finset.sum_nonneg (fun j _ => (hgb j z).1), ?_⟩
    calc
      _ ≤ ∑ _j : Fin m, T := Finset.sum_le_sum (fun j _ => (hgb j z).2.trans (hc j).2)
      _ = (m : ℝ) * T := by simp
      _ ≤ T ^ 2 := by nlinarith
  · intro z z' ho hb
    exact Finset.sum_congr rfl (fun j _ => hcell j z z' ho hb)
  · intro z i hi
    exact Finset.sum_eq_zero (fun j _ => hs j z i hi)
  · calc
      _ ≤ ∑ j, densityL1Distance volume (g j) (scalarComponentDensity (c j) (A j) (B j)) :=
        Submission.Obl.k4_native_base_flattening.densityL1Distance_sum_le volume _ _ hf hg
      _ ≤ ∑ _j : Fin m, ENNReal.ofReal e := Finset.sum_le_sum (fun j _ => he j)
      _ = ENNReal.ofReal ((m : ℝ) * e) := by
        simp [ENNReal.ofReal_mul, ENNReal.ofReal_natCast, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (T * e) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hm he₀)
      _ = _ := by congr 1; dsimp [e]; ring

def ScalarMixtureFormat (N : ℝ) (M D : ℕ) (f : (Fin 6 → ℝ) → ℝ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℝ) (A : Fin m → Set (Fin 5 → ℝ))
    (B : Fin m → Set (Fin 6 → ℝ)),
    (m : ℝ) ≤ N ^ M ∧ (∀ j, 0 ≤ c j ∧ c j ≤ N ^ M) ∧
    (∀ j, Format 5 (N ^ M) D (A j)) ∧ (∀ j, Format 6 (N ^ M) D (B j)) ∧
    (∀ j a, a ∈ A j → ∀ i, |a i| ≤ N ^ M) ∧
    (∀ j a, a ∈ B j → a 5 ∈ Icc (0 : ℝ) 1) ∧
    f = fun z => ∑ j, scalarComponentDensity (c j) (A j) (B j) z

theorem scalar_flattening_at_mesh (M D q H : ℕ) (N : ℝ) (hN : 2 ≤ N)
    (hmesh : 746496 * (D : ℝ) * (N ^ M) ^ 9 * (N ^ H)⁻¹ ≤ (N ^ q)⁻¹)
    (hmesh₁ : (N ^ H)⁻¹ ≤ 1) (f : (Fin 6 → ℝ) → ℝ)
    (hf : ScalarMixtureFormat N M D f) :
      ∃ g : (Fin 6 → ℝ) → ℝ, Measurable g ∧
        (∀ z, 0 ≤ g z ∧ g z ≤ N ^ (2 * M)) ∧
        (∀ z z', (∀ i ∉ ([0, 1] : List (Fin 6)), z i = z' i) →
          (∀ i ∈ ([0, 1] : List (Fin 6)), ⌊N ^ H * z i⌋ = ⌊N ^ H * z' i⌋) → g z = g z') ∧
        supportedInCube g (N ^ (M + 3)) ∧
        densityL1Distance volume g f ≤ ENNReal.ofReal ((N ^ q)⁻¹) := by
  have hN₀ : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have hT : 1 ≤ N ^ M := one_le_pow₀ hN₁
  let ρ : ℝ := (N ^ H)⁻¹
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ₁ : ρ ≤ 1 := hmesh₁
  obtain ⟨m, c, A, B, hm, hc, hA, hB, hsA, hsB, rfl⟩ := hf
  obtain ⟨g, hg, hgb, hcell, hs, he⟩ :=
    finite_scalar_flattening (N ^ M) hT D hm c hc A B hA hB hsA hsB hρ
  refine ⟨g, hg, ?_, ?_, ?_, he.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · intro z
    refine ⟨(hgb z).1, (hgb z).2.trans_eq ?_⟩
    rw [← pow_mul]
    congr 1
    omega
  · intro z z' ho hb
    apply hcell z z' ho
    intro i hi
    simpa only [ρ, div_inv_eq_mul, mul_comm] using hb i hi
  · have hfive : (5 : ℝ) ≤ N ^ 3 := by
      calc
        (5 : ℝ) ≤ 2 ^ 3 := by norm_num
        _ ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN _
    have hR : 3 * N ^ M + 2 * ρ ≤ N ^ (M + 3) := by
      rw [pow_add]
      nlinarith [mul_le_mul_of_nonneg_left hfive (by positivity : 0 ≤ N ^ M)]
    intro z i hi
    exact hs z i (lt_of_le_of_lt hR hi)
  · calc
      _ ≤ 746496 * (D : ℝ) * (N ^ M) ^ 9 * ρ := by
        gcongr
        norm_num
      _ ≤ _ := hmesh

/-- One fixed exponent of the mesh suffices at every sample and in every world. -/
theorem uniform_scalar_flattening (M D q : ℕ) :
    ∃ H : ℕ, ∀ N : ℝ, 2 ≤ N → ∀ f : (Fin 6 → ℝ) → ℝ,
      ScalarMixtureFormat N M D f →
      ∃ g : (Fin 6 → ℝ) → ℝ, Measurable g ∧
        (∀ z, 0 ≤ g z ∧ g z ≤ N ^ (2 * M)) ∧
        (∀ z z', (∀ i ∉ ([0, 1] : List (Fin 6)), z i = z' i) →
          (∀ i ∈ ([0, 1] : List (Fin 6)), ⌊N ^ H * z i⌋ = ⌊N ^ H * z' i⌋) → g z = g z') ∧
        supportedInCube g (N ^ (M + 3)) ∧
        densityL1Distance volume g f ≤ ENNReal.ofReal ((N ^ q)⁻¹) := by
  obtain ⟨H, hH⟩ := Submission.Obl.k4_native_base_flattening.exists_uniform_mesh_exponent
    M (746496 * (D : ℝ)) q
  exact ⟨H, fun N hN f hf => scalar_flattening_at_mesh M D q H N hN
    (hH N hN).1 (hH N hN).2 f hf⟩

/-- The common mesh exponent may also dominate any fixed bound needed to
control cells crossing another observation grid. -/
theorem uniform_scalar_flattening_above (M D q Hmin : ℕ) :
    ∃ H : ℕ, Hmin ≤ H ∧ ∀ N : ℝ, 2 ≤ N → ∀ f : (Fin 6 → ℝ) → ℝ,
      ScalarMixtureFormat N M D f →
      ∃ g : (Fin 6 → ℝ) → ℝ, Measurable g ∧
        (∀ z, 0 ≤ g z ∧ g z ≤ N ^ (2 * M)) ∧
        (∀ z z', (∀ i ∉ ([0, 1] : List (Fin 6)), z i = z' i) →
          (∀ i ∈ ([0, 1] : List (Fin 6)), ⌊N ^ H * z i⌋ = ⌊N ^ H * z' i⌋) → g z = g z') ∧
        supportedInCube g (N ^ (M + 3)) ∧
        densityL1Distance volume g f ≤ ENNReal.ofReal ((N ^ q)⁻¹) := by
  obtain ⟨H₀, hH₀⟩ := Submission.Obl.k4_native_base_flattening.exists_uniform_mesh_exponent
    M (746496 * (D : ℝ)) q
  let H := max H₀ Hmin
  refine ⟨H, le_max_right _ _, ?_⟩
  intro N hN f hf
  have hN₁ : 1 ≤ N := by linarith
  have hρ : (N ^ H)⁻¹ ≤ (N ^ H₀)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    exact pow_le_pow_right₀ hN₁ (le_max_left _ _)
  apply scalar_flattening_at_mesh M D q H N hN _ (hρ.trans (hH₀ N hN).2) f hf
  exact (mul_le_mul_of_nonneg_left hρ (by positivity)).trans (hH₀ N hN).1

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
