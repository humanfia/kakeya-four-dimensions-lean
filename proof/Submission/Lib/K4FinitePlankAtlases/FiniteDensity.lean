import Submission.Lib.K4FinitePlankAtlases.FiniteAtlas

/-!
Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank input is a parameter; no obligation module is imported.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open Set
open scoped BigOperators

private theorem disjoint_sum_eq_covered {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (f : Fin n → ℝ) :
    (∑ j, ∑ i ∈ S j, f i) = ∑ i ∈ Finset.univ.filter (fun i => ∃ j, i ∈ S j), f i := by
  classical
  have hU : Finset.univ.filter (fun i => ∃ j, i ∈ S j) =
      (Finset.univ : Finset (Fin m)).biUnion S := by ext i; simp
  rw [hU]
  exact (Finset.sum_biUnion (fun i _ j _ hij => hS hij)).symm

/-- A finite lower density estimate gives a true matrix atlas retaining half of
that mass. No conditional trajectory probabilities appear in its floors. -/
theorem finite_density_atlas (hweighted : WeightedPlankEstimate) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ) (b u : Fin n → Plane)
      (ω : Fin n → ℝ) (J : Fin n → Finset (Fin D)),
    (∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i, 0 < ω i) →
    (∀ i, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) →
    ∀ mass ρ : ℝ, 0 < mass → 0 < ρ →
    mass ≤ (∑ i, ω i * ((J i).card : ℝ)) / (D : ℝ) →
    ((visitedCells b u J).card : ℝ) ≤ mass * (D : ℝ) ^ 3 / ρ →
    ∃ m : ℕ, ∃ c w : Fin m → Plane,
      ∃ Q : Fin m → Matrix (Fin 2) (Fin 2) ℝ, ∃ S : Fin m → Finset (Fin n),
      m ≤ n ∧ (m : ℝ) ≤ (C * (D : ℝ) ^ (2 + ε) / ρ) * (∑ i, ω i) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      (∀ j,
        Matrix.det (Q j) ≠ 0 ∧ ‖c j‖ + ‖w j‖ ≤ 2 ∧
        (∑ e : Fin 2, ∑ e' : Fin 2, (|Q j e e'| + |(Q j)⁻¹ e e'|)) ≤ 16 * (D : ℝ) ∧
        (∑ e : Fin 2, ∑ e' : Fin 2, |Q j e e'|) ≤ 8 ∧
        (∀ i ∈ S j, ∀ t ∈ Icc (0 : ℝ) 1,
          ‖Matrix.toEuclideanLin ((Q j)⁻¹) (b i + t • u i - c j - t • w j)‖ ≤ 2) ∧
        (ρ / (C * (D : ℝ) ^ ε)) * |Matrix.det (Q j)| ≤
          (∑ i ∈ S j, ω i * ((J i).card : ℝ)) / (D : ℝ)) ∧
      mass / 2 ≤ ∑ j, (∑ i ∈ S j, ω i * ((J i).card : ℝ)) / (D : ℝ) := by
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  obtain ⟨η₀, hη₀, C₀, hC₀, hatlas⟩ := finite_matrix_atlas hweighted (ε / 2) he
  refine ⟨min η₀ (ε / 2), lt_min hη₀ he, 8 * C₀, by positivity, ?_⟩
  intro D hD n b u ω J hbu hω hmarks mass ρ hmass hρ htotal hcells
  have hD₁ : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD₀ : (0 : ℝ) < D := zero_lt_one.trans_le hD₁
  have hmarks₀ (i : Fin n) : (D : ℝ) ^ (1 - η₀) ≤ ((J i).card : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hD₁ (by linarith [min_le_left η₀ (ε / 2)])).trans (hmarks i)
  have hmarks₁ (i : Fin n) : (D : ℝ) ^ (1 - ε / 2) ≤ ((J i).card : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hD₁ (by linarith [min_le_right η₀ (ε / 2)])).trans (hmarks i)
  let d : ℝ := (D : ℝ) ^ (ε / 2)
  have hd : 0 < d := Real.rpow_pos_of_pos hD₀ _
  let A : ℝ := ρ / (2 * C₀ * d * (D : ℝ) ^ 2)
  have hA : 0 < A := div_pos hρ (by positivity)
  obtain ⟨m, c, w, Q, S, hm, hcount, hdisj, hpack, hres⟩ :=
    hatlas D hD n b u ω J hbu hω hmarks₀ A hA
  have hprod : (D : ℝ) ^ (1 - ε / 2) * d = D := by
    dsimp [d]
    rw [← Real.rpow_add hD₀, sub_add_cancel, Real.rpow_one]
  have hsquare : d ^ 2 = (D : ℝ) ^ ε := by
    rw [pow_two]
    dsimp [d]
    rw [← Real.rpow_add hD₀]
    congr 1
    ring
  have hscale : C₀ * A * d * (mass * (D : ℝ) ^ 3 / ρ) = mass * (D : ℝ) / 2 := by
    dsimp [A]
    field_simp
  have hres' : (∑ i ∈ Finset.univ.filter (fun i => ∀ j, i ∉ S j),
      ω i * ((J i).card : ℝ)) ≤ mass * (D : ℝ) / 2 := by
    apply hres.trans
    change C₀ * A * d * ((visitedCells b u J).card : ℝ) ≤ _
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hcells (by positivity)
  have hmass_nonneg : 0 ≤ ∑ i, ω i := Finset.sum_nonneg (fun i _ => (hω i).le)
  have hd₁ : 1 ≤ d := Real.one_le_rpow hD₁ he.le
  have hpoly : d * (D : ℝ) ^ 2 ≤ (D : ℝ) ^ (2 + ε) := by
    rw [Real.rpow_add hD₀, Real.rpow_two, ← hsquare]
    apply (mul_le_mul_of_nonneg_right (show d ≤ d ^ 2 by nlinarith) (sq_nonneg (D : ℝ))).trans_eq
    ring
  have hcoefficient : 2 * C₀ * d * (D : ℝ) ^ 2 ≤ (8 * C₀) * (D : ℝ) ^ (2 + ε) := by
    calc
      _ = (2 * C₀) * (d * (D : ℝ) ^ 2) := by ring
      _ ≤ (2 * C₀) * (D : ℝ) ^ (2 + ε) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ ≤ _ := by gcongr; linarith
  have hcount' : (m : ℝ) ≤ ((8 * C₀) * (D : ℝ) ^ (2 + ε) / ρ) * (∑ i, ω i) := by
    calc
      _ ≤ (∑ i, ω i) / A := (le_div_iff₀ hA).mpr hcount
      _ = (2 * C₀ * d * (D : ℝ) ^ 2 / ρ) * (∑ i, ω i) := by
        dsimp [A]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hcoefficient hρ.le) hmass_nonneg
  refine ⟨m, c, w, Q, S, hm, hcount', hdisj, ?_, ?_⟩
  · intro j
    obtain ⟨hdet, hcenter, hbudget, hsmall, hfit, hprior⟩ := hpack j
    refine ⟨hdet, hcenter, hbudget, hsmall, hfit, ?_⟩
    have h := marked_packet_floor ω J (S j) (η := ε / 2) hD
      (fun i _ => (hω i).le) hprior (fun i _ => hmarks₁ i)
    have heq : (D : ℝ) ^ (1 - ε / 2) *
        ((A * (D : ℝ) ^ 2 / 4) * |Matrix.det (Q j)|) / (D : ℝ) =
        (ρ / ((8 * C₀) * (D : ℝ) ^ ε)) * |Matrix.det (Q j)| := by
      rw [← hsquare]
      calc
        _ = ((D : ℝ) ^ (1 - ε / 2) * d / (D : ℝ)) *
            (ρ / (8 * C₀ * d ^ 2)) * |Matrix.det (Q j)| := by
          dsimp [A]
          field_simp
          ring
        _ = _ := by rw [hprod, div_self hD₀.ne', one_mul]
    rw [heq] at h
    exact h
  · have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => ∃ j, i ∈ S j) (fun i => ω i * ((J i).card : ℝ))
    rw [← disjoint_sum_eq_covered S hdisj] at hpart
    simp only [not_exists] at hpart
    have htotal' : mass * (D : ℝ) ≤ ∑ i, ω i * ((J i).card : ℝ) :=
      (le_div_iff₀ hD₀).mp htotal
    have hcover : mass * (D : ℝ) / 2 ≤ ∑ j, ∑ i ∈ S j, ω i * ((J i).card : ℝ) := by
      linarith
    rw [← Finset.sum_div]
    apply (le_div_iff₀ hD₀).mpr
    nlinarith

end Submission.Lib.K4FinitePlankAtlases
